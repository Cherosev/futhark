-- ==
-- entry: main
-- random input { [1000000]i64 [1000000]u32 [100]u32 }
-- random input { [1000000]i64 [1000000]u32 [1000]u32 }
-- random input { [1000000]i64 [1000000]u32 [10000]u32 }
-- random input { [1000000]i64 [1000000]u32 [100000]u32 }
-- random input { [1000000]i64 [1000000]u32 [1000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [3000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [5000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [7000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [10000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [30000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [50000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [70000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [100000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [110000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [120000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [130000000]u32 }
-- random input { [1000000]i64 [1000000]u32 [140000000]u32 }


entry main [n][w] (is: [n]i64) (vs: [n]u32) (hist: [w]u32) =
  reduce_by_index (copy hist) (u32.max) (0u32) is vs