const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const meta = std.meta;
const testing = std.testing;

// Ported from https://github.com/MnO2/cedarwood
// not the reduced version. could add it in future

pub fn DoubleArrayTrie(
    comptime opts: struct {
        T: type = u31,
        B: type = u23,
        max_trial: comptime_int = 1,
        ordered: bool = true,
    },
) type {
    return struct {
        pub const T = opts.T;
        pub const B = opts.B;
        pub const MaxTrial = opts.max_trial;
        pub const TrialT = std.math.IntFittingRange(0, MaxTrial);

        pub const NodeIndex = packed struct {
            i: u8 = 0,
            b: B = 0,

            pub fn with(self: NodeIndex, l: u8) NodeIndex {
                return .{ .b = self.b, .i = self.i ^ l };
            }
        };
        pub const Node = packed struct {
            pub const Base = packed union {
                /// active if empty
                prev: u8,
                /// active if in chain
                base: NodeIndex,
                value: T,
            };

            base: Base,
            base_is_prev: bool,
            check: packed union {
                /// active if empty
                next: u8,
                /// active if in chain
                check: NodeIndex,
            },
            check_is_next: bool,

            pub fn getBase(self: Node) Base {
                return self.base;
            }
        };

        pub const NodeInfo = struct {
            sibling: u8 = 0,
            child: u8 = 0,
        };
        pub const BlockInfo = packed struct {
            e_head: u8 = 0,
            prev: B,
            next: B,
            /// range [0, 256]
            num: u9 = 256,
            /// range [0, 257]
            reject: u9 = no_reject,
            trial: TrialT = 0,

            pub const no_reject = 257;
        };

        pub const Block = struct {
            pub fn initNodes() [256]Node {
                var nodes: [256]Node = undefined;
                inline for (&nodes, 0..) |*node, i| {
                    node.* = .{
                        .base_is_prev = true,
                        .base = .{ .prev = @as(u8, @truncate(i)) -% 1 },
                        .check_is_next = true,
                        .check = .{ .next = @as(u8, @truncate(i)) +% 1 },
                    };
                }
                return nodes;
            }

            info: BlockInfo,
            nodes: [256]Node = initNodes(),
            node_infos: [256]NodeInfo = .{.{}} ** 256,

            pub fn dumpNode(block: *const Block, node: Node, j: u8) void {
                const nodeinfo = block.node_infos[j];
                std.debug.print(
                    "    {} ({c}) {{ ",
                    .{ j, if (std.ascii.isASCII(@as(u8, @intCast(j))))
                        @as(u8, @intCast(j))
                    else
                        ' ' },
                );
                if (node.base_is_prev) {
                    std.debug.print("prev:{}, ", .{node.base.prev});
                } else {
                    std.debug.print("base:{}-{}({}), ", .{
                        node.base.base.b,
                        node.base.base.i,
                        node.base.value,
                    });
                }
                if (node.check_is_next) {
                    std.debug.print("next:{}, ", .{node.check.next});
                } else {
                    std.debug.print(
                        "chck:{}-{}, ",
                        .{ node.check.check.b, node.check.check.i },
                    );
                }
                std.debug.print(
                    "sib:{}, chi:{} }}\n",
                    .{ nodeinfo.sibling, nodeinfo.child },
                );
            }
        };
        pub const BlockType = enum { open, closed, full };

        pub fn dump(self: *const Self) void {
            const dump_all_nodes = false;
            var iter = self.blocks.constIterator(0);
            var i: usize = 0;
            while (iter.next()) |block| {
                std.debug.print(
                    "block {}: head:{}, prev:{}, next:{}, " ++
                        "num:{}, reject:{}, trial:{}\n",
                    .{
                        i,
                        block.info.e_head,
                        block.info.prev,
                        block.info.next,
                        block.info.num,
                        block.info.reject,
                        block.info.trial,
                    },
                );
                var last_skipped = false;
                for (&block.nodes, &block.node_infos, 0..) |node, nodeinfo, j| {
                    if (!dump_all_nodes and j > 1 and
                        node.base_is_prev and
                        node.base.prev == @as(u8, @truncate(j)) -% 1 and
                        node.check_is_next and
                        node.check.next == @as(u8, @truncate(j)) +% 1 and
                        nodeinfo.sibling == 0 and nodeinfo.child == 0)
                    {
                        if (!last_skipped) {
                            last_skipped = true;
                            std.debug.print("    ...\n", .{});
                        }
                        continue;
                    }
                    block.dumpNode(node, @truncate(j));
                    last_skipped = false;
                }
                i += 1;
            }
            std.debug.print(
                \\first_full_block: {}
                \\first_closed_block: {}
                \\first_open_block: {}
                \\reject: --
                \\
                \\
            , .{
                self.first_full_block,
                self.first_closed_block,
                self.first_open_block,
                //self.reject,
            });
        }

        blocks: std.SegmentedList(Block, 1) = .{
            .prealloc_segment = .{.{
                .info = .{ .prev = 0, .next = 0, .e_head = 1 },
                .nodes = blk: {
                    var nodes = Block.initNodes();
                    nodes[0] = .{
                        .base_is_prev = false,
                        .base = .{ .value = 0 },
                        .check_is_next = true,
                        .check = .{ .next = 1 },
                    };
                    nodes[1] = .{
                        .base_is_prev = true,
                        .base = .{ .prev = 255 },
                        .check_is_next = true,
                        .check = .{ .next = 2 },
                    };
                    nodes[255] = .{
                        .base_is_prev = true,
                        .base = .{ .prev = 254 },
                        .check_is_next = true,
                        .check = .{ .next = 1 },
                    };
                    break :blk nodes;
                },
            }},
            .len = 1,
        },
        reject: [257]u9 = blk: {
            var reject: [257]u9 = undefined;
            inline for (&reject, 0..) |*r, i| {
                r.* = i + 1;
            }
            break :blk reject;
        },
        first_full_block: B = 0,
        first_closed_block: B = 0,
        first_open_block: B = 0,

        const Self = @This();

        pub fn deinit(self: *Self, alloc: Allocator) void {
            self.blocks.deinit(alloc);
            self.* = undefined;
        }

        pub fn update(
            self: *Self,
            alloc: Allocator,
            key: []const u8,
            value: T,
        ) !void {
            assert(key.len != 0);
            var current = NodeIndex{};
            for (key) |c| {
                current = try self.follow(alloc, current, c);
            }
            var to = self.nodeAt(try self.follow(alloc, current, 0));
            to.base_is_prev = false;
            to.base = .{ .value = value };
        }

        pub fn pushBlock(
            self: *Self,
            idx: B,
            comptime to: BlockType,
            empty: bool,
        ) void {
            var head = switch (to) {
                .open => &self.first_open_block,
                .closed => &self.first_closed_block,
                .full => &self.first_full_block,
            };

            var binfo = &self.blocks.at(idx).info;
            if (empty) {
                binfo.next = idx;
                binfo.prev = idx;

                head.* = idx;
            } else {
                var t = &self.blocks.at(head.*).info.prev;
                binfo.prev = t.*;
                binfo.next = head.*;

                self.blocks.at(t.*).info.next = idx;
                self.blocks.at(head.*).info.prev = idx;

                head.* = idx;
            }
        }

        pub fn popBlock(
            self: *Self,
            idx: B,
            comptime from: BlockType,
            last: bool,
        ) void {
            var head = switch (from) {
                .open => &self.first_open_block,
                .closed => &self.first_closed_block,
                .full => &self.first_full_block,
            };

            if (last) {
                head.* = 0;
            } else {
                const binfo = self.blocks.at(idx).info;
                self.blocks.at(binfo.prev).info.next = binfo.next;
                self.blocks.at(binfo.next).info.prev = binfo.prev;
                if (idx == head.*) {
                    head.* = binfo.next;
                }
            }
        }

        pub fn addBlock(self: *Self, alloc: Allocator) !B {
            const idx: B = @intCast(self.blocks.count());
            var b = try self.blocks.addOne(alloc);
            b.* = .{ .info = .{ .prev = undefined, .next = undefined } };
            self.pushBlock(idx, .open, self.first_open_block == 0);
            return idx;
        }

        pub inline fn constNodeAt(self: *const Self, n: NodeIndex) *const Node {
            return &self.blocks.at(n.b).nodes[n.i];
        }
        pub inline fn constNodeInfoAt(self: *const Self, n: NodeIndex) *const NodeInfo {
            return &self.blocks.at(n.b).node_infos[n.i];
        }
        pub inline fn nodeAt(self: *Self, n: NodeIndex) *Node {
            return &self.blocks.at(n.b).nodes[n.i];
        }
        pub inline fn nodeInfoAt(self: *Self, n: NodeIndex) *NodeInfo {
            return &self.blocks.at(n.b).node_infos[n.i];
        }

        pub fn findPlace(self: *Self, alloc: Allocator) !NodeIndex {
            if (self.first_closed_block != 0) return .{
                .i = self.blocks.at(self.first_closed_block).info.e_head,
                .b = self.first_closed_block,
            };
            if (self.first_open_block != 0) return .{
                .i = self.blocks.at(self.first_open_block).info.e_head,
                .b = self.first_open_block,
            };

            return .{ .b = try self.addBlock(alloc) };
        }

        pub fn findPlaces(
            self: *Self,
            alloc: Allocator,
            children: []const u8,
        ) !NodeIndex {
            var idx = self.first_open_block;
            if (idx > 0) {
                const bz = self.blocks.at(self.first_open_block).info.prev;
                while (true) {
                    var block = self.blocks.at(idx);
                    if (block.info.num >= children.len and
                        children.len < block.info.reject)
                    {
                        var ei = block.info.e_head;
                        while (true) {
                            const base_i = ei ^ children[0];
                            var i: u8 = 1;
                            while (block.nodes[base_i ^ children[i]].check_is_next) {
                                if (i == children.len - 1) {
                                    block.info.e_head = ei;
                                    return .{ .b = idx, .i = ei };
                                }
                                i += 1;
                            }
                            ei = block.nodes[ei].check.next;
                            if (ei == block.info.e_head) break;
                        }
                    }

                    block.info.reject = @intCast(children.len);
                    if (block.info.reject < self.reject[block.info.num])
                        self.reject[block.info.num] = block.info.reject;

                    const next_idx = block.info.next;
                    block.info.trial += 1;
                    if (block.info.trial == MaxTrial)
                        self.transferBlock(
                            idx,
                            .open,
                            .closed,
                            self.first_closed_block == 0,
                        );
                    if (idx == bz) break;
                    idx = next_idx;
                }
            }
            return .{ .b = try self.addBlock(alloc) };
        }

        pub fn transferBlock(
            self: *Self,
            idx: B,
            comptime from: BlockType,
            comptime to: BlockType,
            to_empty: bool,
        ) void {
            self.popBlock(idx, from, idx == self.blocks.at(idx).info.next);
            self.pushBlock(idx, to, to_empty and (self.blocks.at(idx).info.num != 0));
        }

        pub fn popENode(
            self: *Self,
            base_is_prev: bool,
            e: NodeIndex,
            label: u8,
            from: NodeIndex,
        ) void {
            var block = self.blocks.at(e.b);
            const n = block.nodes[e.i];
            block.info.num -= 1;
            if (block.info.num == 0) {
                if (e.b > 0) {
                    self.transferBlock(
                        e.b,
                        .closed,
                        .full,
                        self.first_full_block == 0,
                    );
                }
            } else {
                //std.debug.print("n:", .{});
                //block.dumpNode(n, e.i);
                //assert(n.base_is_prev); // ok i guess :\
                //assert(n.check_is_next);
                //if (n.check_is_next) {
                //block.nodes[n.base.prev].check_is_next = true;
                //block.nodes[n.base.prev].check = .{ .next = n.check.next };
                block.nodes[n.base.prev].check_is_next = n.check_is_next;
                block.nodes[n.base.prev].check = n.check;
                //}
                //if (n.base_is_prev) {
                //block.nodes[n.check.next].base_is_prev = true;
                //block.nodes[n.check.next].base = .{ .prev = n.base.prev };
                block.nodes[n.check.next].base_is_prev = n.base_is_prev;
                block.nodes[n.check.next].base = n.base;
                //}

                if (e.i == block.info.e_head) block.info.e_head = n.check.next;

                if (e.b > 0 and block.info.num == 1 and block.info.trial != MaxTrial) {
                    self.transferBlock(
                        e.b,
                        .open,
                        .closed,
                        self.first_closed_block == 0,
                    );
                }
            }

            if (label != 0) {
                block.nodes[e.i].base_is_prev = true;
                block.nodes[e.i].base = .{ .prev = 1 };
            } else {
                block.nodes[e.i].base_is_prev = false;
                block.nodes[e.i].base = .{ .value = 0 };
            }
            block.nodes[e.i].check_is_next = false;
            block.nodes[e.i].check = .{ .check = from };
            if (base_is_prev) {
                var from_n = self.nodeAt(from);
                from_n.base_is_prev = false;
                from_n.base.base = e.with(label);
            }
        }

        pub fn pushENode(self: *Self, e: NodeIndex) void {
            var block = self.blocks.at(e.b);
            block.info.num += 1;

            if (block.info.num == 1) {
                block.info.e_head = e.i;
                block.nodes[e.i] = .{
                    .base = .{ .prev = e.i },
                    .base_is_prev = true,
                    .check = .{ .next = e.i },
                    .check_is_next = true,
                };

                if (e.b > 0) self.transferBlock(
                    e.b,
                    .full,
                    .closed,
                    self.first_closed_block == 0,
                );
            } else {
                const prev = block.info.e_head;
                const next = block.nodes[prev].check.next;

                block.nodes[e.i] = .{
                    .base = .{ .prev = prev },
                    .base_is_prev = true,
                    .check = .{ .next = next },
                    .check_is_next = true,
                };

                block.nodes[prev].check = .{ .next = e.i };
                block.nodes[prev].check_is_next = true;
                block.nodes[next].base = .{ .prev = e.i };
                block.nodes[next].base_is_prev = true;

                if (block.info.num == 2 or block.info.trial == MaxTrial) {
                    assert(block.info.num > 1);
                    if (e.b > 0) self.transferBlock(
                        e.b,
                        .closed,
                        .open,
                        self.first_open_block == 0,
                    );
                }

                block.info.trial = 0;
            }

            if (block.info.reject < self.reject[block.info.num])
                block.info.reject = self.reject[block.info.num];
            block.node_infos[e.i] = .{};
        }

        pub fn pushSibling(
            self: *Self,
            from: NodeIndex,
            e: NodeIndex,
            label: u8,
            has_child: bool,
        ) void {
            var finfo = self.nodeInfoAt(from);
            const keep_order = if (opts.ordered)
                label > finfo.child
            else
                finfo.child > 0;

            var c = &finfo.child;
            if (has_child and keep_order) while (true) {
                c = &self.nodeInfoAt(e.with(c.*)).sibling;
                if (!opts.ordered) break;
                if (c.* == 0 or c.* >= label) break;
            };
            const sibling = c.*;
            c.* = label;
            self.nodeInfoAt(e.with(label)).sibling = sibling;
        }

        pub fn consult(
            self: *const Self,
            base_n: NodeIndex,
            base_p: NodeIndex,
            n_: u8,
            p_: u8,
        ) bool {
            var block_n = self.blocks.at(base_n.b);
            var block_p = self.blocks.at(base_p.b);
            var n = n_;
            var p = p_;
            //std.debug.print(
            //    "base_n.b: {}, i: {}, base_p.b: {}, i: {}, n: {}, p: {}\n",
            //    .{ base_n.b, base_n.i, base_p.b, base_p.i, n, p },
            //);
            while (true) {
                n = block_n.node_infos[base_n.i ^ n].sibling;
                p = block_p.node_infos[base_p.i ^ p].sibling;
                //std.debug.print("n: {}, p: {}\n", .{ n, p });
                if (n == 0 or p == 0) return p != 0;
            }
        }

        pub fn getChildren(
            self: *const Self,
            base: NodeIndex,
            c_: u8,
            label: u8,
            not_terminal: bool,
        ) std.BoundedArray(u8, 256) {
            var block = self.blocks.at(base.b);
            var children = std.BoundedArray(u8, 256){};
            var c = c_;

            if (c == 0) {
                children.appendAssumeCapacity(c);
                c = block.node_infos[base.i ^ c].sibling;
            }

            if (opts.ordered) {
                while (c != 0 and c <= label) {
                    children.appendAssumeCapacity(c);
                    c = block.node_infos[base.i ^ c].sibling;
                }
            }

            if (not_terminal) {
                children.appendAssumeCapacity(label);
            }

            while (c != 0) {
                children.appendAssumeCapacity(c);
                c = block.node_infos[base.i ^ c].sibling;
            }
            return children;
        }

        pub fn resolve(
            self: *Self,
            alloc: Allocator,
            from_n_: NodeIndex,
            base_n: NodeIndex,
            label_n: u8,
        ) !NodeIndex {
            var from_n = from_n_;
            const to_pn = base_n.with(label_n);
            //std.debug.print("to_pn b:{}, i:{}\n", .{ to_pn.b, to_pn.i });
            // we know these variants are active because the caller made sure
            const from_p = self.nodeAt(to_pn).check.check;
            const base_p = self.nodeAt(from_p).getBase().base;

            const replace_sib = self.consult(
                base_n,
                base_p,
                self.nodeInfoAt(from_n).child,
                self.nodeInfoAt(from_p).child,
            );
            //std.debug.print("replace_sib:{}\n", .{replace_sib});

            const children = if (replace_sib)
                self.getChildren(
                    base_n,
                    self.nodeInfoAt(from_n).child,
                    label_n,
                    true,
                )
            else
                self.getChildren(
                    base_p,
                    self.nodeInfoAt(from_p).child,
                    255,
                    false,
                );

            const base = (if (children.len > 1)
                try self.findPlaces(alloc, children.constSlice())
            else
                try self.findPlace(alloc)).with(children.constSlice()[0]);
            const from = if (replace_sib) from_n else from_p;
            const base_ = if (replace_sib) base_n else base_p;
            if (replace_sib and children.constSlice()[0] == label_n)
                self.nodeInfoAt(from).child = label_n;

            self.nodeAt(from).base_is_prev = false;
            self.nodeAt(from).base = .{ .base = base };

            for (children.constSlice(), 0..) |ci, i| {
                //std.debug.print("child {}: {}\n", .{ i, ci });
                const to = base.with(ci);
                self.popENode(false, to, ci, from);
                const to_ = base_.with(ci);
                var to_info = self.nodeInfoAt(to);
                to_info.sibling =
                    if (i == children.len - 1) 0 else children.constSlice()[i + 1];
                if (replace_sib and meta.eql(to_, to_pn)) continue;

                var to_n = self.nodeAt(to);
                var to__n = self.nodeAt(to_);
                to_n.base_is_prev = to__n.base_is_prev;
                to_n.base = to__n.base;

                if (!to_n.base_is_prev and ci != 0) {
                    var c = self.nodeInfoAt(to_).child;
                    to_info.child = c;

                    while (true) {
                        const n_idx = to_n.getBase().base.with(c);
                        self.nodeAt(n_idx).check_is_next = false;
                        self.nodeAt(n_idx).check = .{ .check = to };
                        c = self.nodeInfoAt(n_idx).sibling;
                        if (c == 0) break;
                    }
                }

                if (!replace_sib and meta.eql(to_, from_n)) {
                    from_n = to;
                }

                if (!replace_sib and meta.eql(to_, to_pn)) {
                    self.pushSibling(from_n, to_pn.with(label_n), label_n, true);
                    self.nodeInfoAt(to_).child = 0;

                    if (label_n != 0) {
                        to__n.base_is_prev = true;
                        to__n.base = .{ .prev = 1 };
                    } else {
                        to__n.base_is_prev = false;
                        to__n.base = .{ .value = 0 };
                    }

                    to__n.check_is_next = false;
                    to__n.check = .{ .check = from_n };
                } else {
                    self.pushENode(to_);
                }
            }

            return if (replace_sib) base.with(label_n) else to_pn;
        }

        pub fn follow(
            self: *Self,
            alloc: Allocator,
            from: NodeIndex,
            label: u8,
        ) !NodeIndex {
            var n = self.nodeAt(from);
            const base = n.getBase();
            if (n.base_is_prev or
                self.nodeAt(base.base.with(label)).check_is_next)
            {
                //std.debug.print("push\n", .{});
                const is_prev = n.base_is_prev;
                const to = if (is_prev)
                    try self.findPlace(alloc)
                else
                    base.base.with(label);
                //std.debug.print("to b:{}, i:{}\n", .{ to.b, to.i });

                self.popENode(is_prev, to, label, from);

                self.pushSibling(from, to.with(label), label, !is_prev); // !n.base_is_prev);
                return to;
            } else {
                //std.debug.print("resolve. from b:{}, from i:{}\n", .{ from.b, from.i });
                const to = base.base.with(label);
                var to_n = self.nodeAt(to);
                //std.debug.print("to_n:", .{});
                //self.blocks.at(to.b).dumpNode(to_n.*, to.i);
                //assert(!to_n.check_is_next);
                if (to_n.check_is_next or !meta.eql(to_n.check.check, from)) {
                    return try self.resolve(alloc, from, base.base, label);
                } else {
                    return to;
                }
            }
        }

        pub fn find(self: *const Self, key: []const u8, from: *NodeIndex) ?T {
            var to = NodeIndex{};
            for (key) |c| {
                to = self.constNodeAt(from.*).getBase().base.with(c);
                const to_n = self.constNodeAt(to);
                if (to_n.check_is_next or !meta.eql(to_n.check.check, from.*))
                    return null;
                from.* = to;
            }
            const from_n = self.constNodeAt(self.constNodeAt(from.*).getBase().base);
            if (from_n.check_is_next or !meta.eql(from_n.check.check, from.*)) {
                return null;
            } else {
                return from_n.getBase().value;
            }
        }

        pub fn exactMatchSearch(
            self: *const Self,
            key: []const u8,
            from_out: ?*NodeIndex,
        ) ?T {
            var from = NodeIndex{};
            if (self.find(key, &from)) |v| {
                if (from_out) |o| o.* = from;
                return v;
            } else {
                return null;
            }
        }

        pub fn contains(
            self: *const Self,
            key: []const u8,
        ) bool {
            var from = NodeIndex{};
            return self.find(key, &from) != null;
        }

        pub const PrefixIterator = struct {
            self: *const Self,
            key: []const u8,
            from: NodeIndex = .{},
            i: usize = 0,

            pub const Pair = struct { value: T, i: usize };
            pub fn next(self: *PrefixIterator) ?Pair {
                while (self.i < self.key.len) {
                    defer self.i += 1;
                    if (self.self.find(self.key[self.i .. self.i + 1], &self.from)) |v| {
                        return .{
                            .value = v,
                            .i = self.i,
                        };
                    }
                }
                return null;
            }
        };

        pub fn commonPrefixIterator(self: *const Self, key: []const u8) PrefixIterator {
            return .{
                .self = self,
                .key = key,
            };
        }
    };
}

test "insert and exact" {
    var alloc = testing.allocator;

    @setEvalBranchQuota(10000);
    const words = .{
        "a",
        "ab",
        "abc",
        "アルゴリズム",
        "データ",
        "構造",
        "网",
        "网球",
        "网球拍",
        "中",
        "中华",
        "中华人民",
        "中华人民共和国",
    };

    const Trie = DoubleArrayTrie(.{
        .T = u10,
        .B = u5,
    });
    var trie = Trie{};
    defer trie.deinit(alloc);

    inline for (words, 1..) |s, i| {
        if (trie.contains(s)) @panic(s);
        try trie.update(alloc, s, @intCast(i));
    }

    //trie.dump();

    inline for (words, 1..) |s, i| {
        try testing.expectEqual(
            @as(?Trie.T, @intCast(i)),
            trie.exactMatchSearch(s, null),
        );
    }

    try testing.expectEqual(@as(?Trie.T, null), trie.exactMatchSearch("abcd", null));

    std.debug.print(
        "block size: {}\nblocks: {}\nwords: {}\n",
        .{ @sizeOf(Trie.Block), trie.blocks.count(), words.len },
    );
    std.debug.print("{d} bytes per word\n", .{
        @as(f64, @floatFromInt(@sizeOf(Trie.Block) * trie.blocks.count())) /
            @as(f64, @floatFromInt(words.len)),
    });
}
