const std = @import("std");
const raylib = @import("raylib");
const cassowary = @import("cassowary.zig");
const Solver = cassowary.Solver(f32);

pub fn main() !void {
    raylib.setConfigFlags(.{ .window_resizable = true });
    raylib.initWindow(600, 400, "layout demo");
    raylib.setTargetFPS(60);

    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();

    var solver: Solver = .{};
    defer solver.deinit(allocator);

    const box_width = solver.newExternalVariable();
    var window_width = try solver.addEditVariable(allocator, cassowary.strengths.strong, 0);

    const variables = .{ .box_width = box_width, .window_width = window_width.variable };

    var buffer_row: Solver.Row = .{};
    defer buffer_row.deinit(allocator);

    try solver.addConstraint(allocator, try .parse(
        allocator,
        &buffer_row,
        cassowary.strengths.strong,
        "box_width = 0.5 * window_width",
        variables,
    ));

    try solver.addConstraint(allocator, try .parse(
        allocator,
        &buffer_row,
        cassowary.strengths.strong,
        "box_width >= 200.0",
        variables,
    ));

    try solver.debugPrint(std.io.getStdOut().writer());

    while (!raylib.windowShouldClose()) {
        raylib.beginDrawing();
        raylib.clearBackground(raylib.Color.white);

        try solver.suggestValue(allocator, &window_width, @floatFromInt(raylib.getScreenWidth()));

        raylib.drawRectangleV(.{ .x = 0, .y = 0 }, .{
            .x = solver.getValue(box_width),
            .y = 100,
        }, raylib.Color.black);

        raylib.endDrawing();
    }
}
