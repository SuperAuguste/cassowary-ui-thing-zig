const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const ConstraintTokenizer = struct {
    const Tag = enum {
        invalid,
        float,
        variable,
        plus,
        asterisk,
        equal,
        left_angle_bracket_equal,
        right_angle_bracket_equal,
        end,
    };

    const Token = struct {
        tag: Tag,
        start: u16,
        end: u16,
    };

    const State = enum {
        start,
        float_whole,
        float_decimal,
        variable,
        left_angle_bracket,
        right_angle_bracket,
    };

    buffer: [:0]const u8,
    index: usize = 0,

    fn next(tokenizer: *ConstraintTokenizer) Token {
        var start: u16 = @intCast(tokenizer.index);

        const tag: Tag = loop: switch (State.start) {
            .start => switch (tokenizer.buffer[tokenizer.index]) {
                0 => break :loop .end,
                ' ' => {
                    tokenizer.index += 1;
                    start += 1;
                    continue :loop .start;
                },
                '+' => {
                    tokenizer.index += 1;
                    break :loop .plus;
                },
                '*' => {
                    tokenizer.index += 1;
                    break :loop .asterisk;
                },
                '=' => {
                    tokenizer.index += 1;
                    break :loop .equal;
                },
                '<' => {
                    tokenizer.index += 1;
                    continue :loop .left_angle_bracket;
                },
                '>' => {
                    tokenizer.index += 1;
                    continue :loop .right_angle_bracket;
                },
                '-', '0'...'9' => {
                    tokenizer.index += 1;
                    continue :loop .float_whole;
                },
                'a'...'z', 'A'...'Z', '_' => {
                    tokenizer.index += 1;
                    continue :loop .variable;
                },
                else => break :loop .invalid,
            },
            .float_whole => switch (tokenizer.buffer[tokenizer.index]) {
                '0'...'9', '-' => {
                    tokenizer.index += 1;
                    continue :loop .float_whole;
                },
                '.' => {
                    tokenizer.index += 1;
                    continue :loop .float_decimal;
                },
                else => break :loop .invalid,
            },
            .float_decimal => switch (tokenizer.buffer[tokenizer.index]) {
                '0'...'9' => {
                    tokenizer.index += 1;
                    continue :loop .float_decimal;
                },
                else => break :loop .float,
            },
            .variable => switch (tokenizer.buffer[tokenizer.index]) {
                'a'...'z', 'A'...'Z', '_', '0'...'9' => {
                    tokenizer.index += 1;
                    continue :loop .variable;
                },
                else => break :loop .variable,
            },
            .left_angle_bracket => switch (tokenizer.buffer[tokenizer.index]) {
                '=' => {
                    tokenizer.index += 1;
                    break :loop .left_angle_bracket_equal;
                },
                else => break :loop .invalid,
            },
            .right_angle_bracket => switch (tokenizer.buffer[tokenizer.index]) {
                '=' => {
                    tokenizer.index += 1;
                    break :loop .right_angle_bracket_equal;
                },
                else => break :loop .invalid,
            },
        };

        return .{
            .tag = tag,
            .start = start,
            .end = @intCast(tokenizer.index),
        };
    }
};

pub const Variable = packed struct {
    const Kind = enum(u2) {
        external,
        slack,
        @"error",
    };
    const Id = enum(u30) { _ };

    id: Id,
    kind: Kind,
};

/// Although the Cassowary paper uses lexicographically ordered sets in the objective
/// function to prevent the erosion of greater strength when many lesser strength constraints
/// add up, these order of magnitude strength constraints should do the trick for a vast
/// majority of usecases while also simplifying the implementation.
pub const strengths = struct {
    pub const required = 100_000_000_000;
    pub const strong = 1_000_000;
    pub const medium = 1_000;
    pub const weak = 1;
};

pub fn Constraint(comptime Float: type) type {
    return struct {
        pub const Operator = enum { eq, lte, gte };

        expression: Solver(Float).Row,
        operator: Operator,
        strength: Float,

        fn parse(
            allocator: Allocator,
            strength: Float,
            comptime text: [:0]const u8,
            variables: anytype,
        ) !@This() {
            var constraint: @This() = .{
                .expression = .{},
                .operator = undefined,
                .strength = strength,
            };

            comptime var tokenizer = ConstraintTokenizer{ .buffer = text };
            comptime var state: enum { at_term, post_term, post_float, post_asterisk } = .at_term;
            comptime var side: enum {
                left,
                right,

                fn coefficient(side: @This()) Float {
                    return switch (side) {
                        .left => 1,
                        .right => -1,
                    };
                }
            } = .left;
            comptime var withheld_float: Float = undefined;

            comptime var token = tokenizer.next();
            inline while (true) : ({
                comptime token = tokenizer.next();
            }) {
                switch (state) {
                    .at_term => switch (token.tag) {
                        .float => {
                            withheld_float = comptime try std.fmt.parseFloat(Float, text[token.start..token.end]);
                            state = .post_float;
                        },
                        .variable => {
                            try constraint.expression.addTerm(
                                allocator,
                                @field(variables, text[token.start..token.end]),
                                side.coefficient(),
                            );
                            state = .post_term;
                        },
                        else => @compileError("Invalid " ++ @tagName(token.tag) ++ ": " ++ text[token.start..token.end]),
                    },
                    .post_term => switch (token.tag) {
                        .plus => {
                            state = .at_term;
                        },
                        .equal => {
                            if (side != .left) @compileError("Constraint cannot have two operators");
                            side = .right;
                            constraint.operator = .eq;
                            state = .at_term;
                        },
                        .left_angle_bracket_equal => {
                            if (side != .left) @compileError("Constraint cannot have two operators");
                            side = .right;
                            constraint.operator = .lte;
                            state = .at_term;
                        },
                        .right_angle_bracket_equal => {
                            if (side != .left) @compileError("Constraint cannot have two operators");
                            side = .right;
                            constraint.operator = .gte;
                            state = .at_term;
                        },
                        .end => return constraint,
                        else => @compileError("Invalid " ++ @tagName(token.tag) ++ ": " ++ text[token.start..token.end]),
                    },
                    .post_float => switch (token.tag) {
                        .plus => {
                            constraint.expression.constant += side.coefficient() * withheld_float;
                            withheld_float = undefined;
                            state = .at_term;
                        },
                        .end => {
                            constraint.expression.constant += side.coefficient() * withheld_float;
                            withheld_float = undefined;
                            return constraint;
                        },
                        .asterisk => {
                            state = .post_asterisk;
                        },
                        .equal => {
                            constraint.expression.constant += side.coefficient() * withheld_float;
                            withheld_float = undefined;

                            if (side != .left) @compileError("Constraint cannot have two operators");
                            side = .right;
                            constraint.operator = .eq;
                            state = .at_term;
                        },
                        .left_angle_bracket_equal => {
                            constraint.expression.constant += side.coefficient() * withheld_float;
                            withheld_float = undefined;

                            if (side != .left) @compileError("Constraint cannot have two operators");
                            side = .right;
                            constraint.operator = .lte;
                            state = .at_term;
                        },
                        .right_angle_bracket_equal => {
                            constraint.expression.constant += side.coefficient() * withheld_float;
                            withheld_float = undefined;

                            if (side != .left) @compileError("Constraint cannot have two operators");
                            side = .right;
                            constraint.operator = .gte;
                            state = .at_term;
                        },
                        else => @compileError("Invalid " ++ @tagName(token.tag) ++ ": " ++ text[token.start..token.end]),
                    },
                    .post_asterisk => switch (token.tag) {
                        .variable => {
                            try constraint.expression.addTerm(
                                allocator,
                                @field(variables, text[token.start..token.end]),
                                side.coefficient() * withheld_float,
                            );
                            withheld_float = undefined;
                            state = .post_term;
                        },
                        else => @compileError("Invalid " ++ @tagName(token.tag) ++ ": " ++ text[token.start..token.end]),
                    },
                }
            }

            unreachable;
        }
    };
}

pub fn Solver(comptime Float: type) type {
    return struct {
        const Row = struct {
            terms: std.AutoArrayHashMapUnmanaged(Variable, Float) = .{},
            constant: Float = 0,

            pub fn addTerm(
                row: *Row,
                allocator: Allocator,
                variable: Variable,
                coefficient: Float,
            ) error{OutOfMemory}!void {
                const gop = try row.terms.getOrPutValue(allocator, variable, 0);
                gop.value_ptr.* += coefficient;
                if (gop.value_ptr.* == 0) {
                    assert(row.terms.swapRemove(variable));
                }
            }

            pub fn addRow(
                dest_row: *Row,
                allocator: Allocator,
                src_row: Row,
            ) error{OutOfMemory}!void {
                for (src_row.terms.keys(), src_row.terms.values()) |variable, coefficient| {
                    try dest_row.addTerm(allocator, variable, coefficient);
                }
                dest_row.constant += src_row.constant;
            }

            /// `solveFor` will make the coefficient of the selected
            /// variable `-1`, allowing you to make it basic, for example.
            fn solveFor(
                row: *Row,
                variable: Variable,
            ) void {
                const transformation_coefficient = -1 / row.terms.get(variable).?;
                for (row.terms.values()) |*coefficient| {
                    coefficient.* *= transformation_coefficient;
                }
                row.constant *= transformation_coefficient;
                assert(row.terms.swapRemove(variable));
            }

            fn replaceVariable(
                dest_row: *Row,
                allocator: Allocator,
                src_row: Row,
                replaced_variable: Variable,
            ) !void {
                // Assert replaced variable is basis variable
                assert(!src_row.terms.contains(replaced_variable));

                const transformation_coefficient =
                    (dest_row.terms.fetchSwapRemove(replaced_variable) orelse return).value;

                const src_constraint_variable_indices = src_row.terms.keys();
                const src_constraint_coefficients = src_row.terms.values();

                for (
                    src_constraint_variable_indices,
                    src_constraint_coefficients,
                ) |src_variable, src_coefficient| {
                    if (src_variable.id == replaced_variable.id) continue;

                    try dest_row.addTerm(
                        allocator,
                        src_variable,
                        src_coefficient * transformation_coefficient,
                    );
                }

                dest_row.constant += src_row.constant * transformation_coefficient;
            }
        };

        next_variable_id: Variable.Id = @enumFromInt(0),

        objective_function: Row = .{},
        rows: std.AutoArrayHashMapUnmanaged(Variable, Row) = .{},

        fn debugPrint(
            solver: @This(),
            writer: anytype,
        ) !void {
            try writer.writeAll("objective function: ");

            for (
                solver.objective_function.terms.keys(),
                solver.objective_function.terms.values(),
            ) |variable, coefficient| {
                try writer.print("{d}*var_{d} + ", .{ coefficient, @intFromEnum(variable.id) });
            }

            try writer.print("{d}\n\n", .{solver.objective_function.constant});

            for (solver.rows.keys(), solver.rows.values(), 0..) |
                constraint_variable,
                constraint,
                index,
            | {
                try writer.print("constraint {d} (of var_{d}, {s}): ", .{
                    index,
                    @intFromEnum(constraint_variable.id),
                    @tagName(constraint_variable.kind),
                });

                for (
                    constraint.terms.keys(),
                    constraint.terms.values(),
                ) |variable, coefficient| {
                    try writer.print("{d}*var_{d} + ", .{ coefficient, @intFromEnum(variable.id) });
                }

                try writer.print("{d} = 0\n", .{constraint.constant});
            }
        }

        pub fn newExternalVariable(solver: *@This()) Variable {
            return solver.newVariable(.external);
        }

        fn newVariable(solver: *@This(), kind: Variable.Kind) Variable {
            const next_variable_id = solver.next_variable_id;
            solver.next_variable_id = @enumFromInt(@intFromEnum(solver.next_variable_id) + 1);
            return .{
                .kind = kind,
                .id = next_variable_id,
            };
        }

        fn optimize(solver: *@This(), allocator: Allocator) !void {
            while (true) {
                const entry_variable = entry: for (
                    solver.objective_function.terms.keys(),
                    solver.objective_function.terms.values(),
                ) |variable, coefficient| {
                    if (coefficient < 0) break :entry variable;
                } else break;

                var min = std.math.inf(Float);
                var maybe_exit_variable: ?Variable = null;

                const variables = solver.rows.keys();
                const rows = solver.rows.values();

                for (variables, rows) |simplex_variable, row| {
                    // Simplex tableau only (slack, error)
                    if (simplex_variable.kind == .external) continue;

                    const new_min =
                        -row.constant /
                        (row.terms.get(entry_variable) orelse continue);

                    if (new_min < min) {
                        min = new_min;
                        maybe_exit_variable = simplex_variable;
                    }
                }

                const exit_variable = maybe_exit_variable.?;

                std.log.info("{any} {any}", .{ entry_variable, exit_variable });

                var exit_row = solver.rows.get(exit_variable).?;

                exit_row.solveFor(exit_variable);
                try solver.objective_function.replaceVariable(allocator, exit_row, exit_variable);

                for (variables) |simplex_variable| {
                    if (simplex_variable.kind == .external) continue;
                    if (simplex_variable.id == exit_variable.id) continue;

                    const row = solver.rows.getPtr(simplex_variable).?;
                    try row.replaceVariable(
                        allocator,
                        exit_row,
                        exit_variable,
                    );
                }

                _ = solver.rows.swapRemove(exit_variable);
                try solver.rows.put(allocator, entry_variable, exit_row);
            }
        }

        pub fn addConstraint(
            solver: *@This(),
            allocator: Allocator,
            constraint: Constraint(Float),
        ) !void {
            var row = Row{ .constant = constraint.expression.constant };

            var new_row_basic_variable: ?Variable = null;

            const constraint_variables = constraint.expression.terms.keys();
            const constraint_coefficients = constraint.expression.terms.values();

            for (constraint_variables, constraint_coefficients) |variable, coefficient| {
                if (solver.rows.get(variable)) |existing_row| {
                    try row.addRow(allocator, existing_row);
                } else {
                    if (new_row_basic_variable == null) {
                        new_row_basic_variable = variable;
                    }
                    try row.addTerm(allocator, variable, coefficient);
                }
            }

            switch (constraint.operator) {
                .lte, .gte => {
                    const coefficient: Float = switch (constraint.operator) {
                        .lte => 1,
                        .gte => -1,
                        .eq => unreachable,
                    };

                    const slack_variable = solver.newVariable(.slack);
                    try row.addTerm(allocator, slack_variable, coefficient);

                    if (new_row_basic_variable == null) {
                        new_row_basic_variable = slack_variable;
                    }

                    if (constraint.strength < strengths.required) {
                        const error_variable = solver.newVariable(.@"error");
                        try row.addTerm(allocator, error_variable, -coefficient);

                        try solver.objective_function.addTerm(
                            allocator,
                            error_variable,
                            constraint.strength,
                        );
                    }
                },
                .eq => {
                    if (constraint.strength < strengths.required) {
                        const error_variable_positive = solver.newVariable(.@"error");
                        try row.addTerm(allocator, error_variable_positive, -1);

                        try solver.objective_function.addTerm(
                            allocator,
                            error_variable_positive,
                            constraint.strength,
                        );

                        if (new_row_basic_variable == null) {
                            new_row_basic_variable = error_variable_positive;
                        }

                        const error_variable_negative = solver.newVariable(.@"error");
                        try row.addTerm(allocator, error_variable_negative, 1);

                        try solver.objective_function.addTerm(
                            allocator,
                            error_variable_negative,
                            constraint.strength,
                        );
                    }
                },
            }

            if (row.constant < 0) {
                for (row.terms.values()) |*coefficient| {
                    coefficient.* *= -1;
                }
                row.constant *= -1;
            }

            if (new_row_basic_variable) |basic_variable| {
                row.solveFor(basic_variable);
                for (solver.rows.values()) |*dest_row| {
                    try dest_row.replaceVariable(allocator, row, basic_variable);
                }
                try solver.rows.put(allocator, basic_variable, row);
            } else {
                assert(constraint.strength >= strengths.required);
                // TODO
            }

            try solver.optimize(allocator);
        }

        pub fn getExternalVariableValue(solver: @This(), variable: Variable) Float {
            assert(variable.kind == .external);
            const row = solver.rows.get(variable).?;
            for (row.terms.keys()) |term| {
                assert(term.kind != .external);
            }
            return row.constant;
        }
    };
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    const MySolver = Solver(f32);
    var solver: MySolver = .{};

    const x_m = solver.newExternalVariable();
    const x_l = solver.newExternalVariable();
    const x_r = solver.newExternalVariable();

    const variables = .{ .x_m = x_m, .x_l = x_l, .x_r = x_r };

    try solver.addConstraint(allocator, try .parse(
        allocator,
        strengths.strong,
        "2.0 * x_m = x_l + x_r",
        variables,
    ));

    try solver.addConstraint(allocator, try .parse(
        allocator,
        strengths.strong,
        "x_l + 10.0 <= x_r",
        variables,
    ));

    try solver.addConstraint(allocator, try .parse(
        allocator,
        strengths.strong,
        "x_l >= -10.0",
        variables,
    ));

    try solver.addConstraint(allocator, try .parse(
        allocator,
        strengths.strong,
        "x_r <= 100.0",
        variables,
    ));

    try solver.debugPrint(std.io.getStdOut().writer());

    std.log.info("x_m = {d}", .{solver.getExternalVariableValue(x_m)});
    std.log.info("x_l = {d}", .{solver.getExternalVariableValue(x_l)});
    std.log.info("x_r = {d}", .{solver.getExternalVariableValue(x_r)});
}
