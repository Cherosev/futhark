-- ==
-- entry: main
-- random input { [100]i64 [100]u32 [10]u32 [10]u32 }
-- random input { [1000]i64 [1000]u32 [10]u32 [10]u32 }
-- random input { [10000]i64 [10000]u32 [10]u32 [10]u32 }
-- random input { [100000]i64 [100000]u32 [10]u32 [10]u32 }
-- random input { [1000000]i64 [1000000]u32 [10]u32 [10]u32 }
-- random input { [3000000]i64 [3000000]u32 [10]u32 [10]u32 }
-- random input { [5000000]i64 [5000000]u32 [10]u32 [10]u32 }
-- random input { [7000000]i64 [7000000]u32 [10]u32 [10]u32 }
-- random input { [10000000]i64 [10000000]u32 [10]u32 [10]u32 }
-- random input { [30000000]i64 [30000000]u32 [10]u32 [10]u32 }
-- random input { [50000000]i64 [50000000]u32 [10]u32 [10]u32 }
-- random input { [70000000]i64 [70000000]u32 [10]u32 [10]u32 }
-- random input { [100000000]i64 [100000000]u32 [10]u32 [10]u32 }
-- random input { [110000000]i64 [110000000]u32 [10]u32 [10]u32 }
-- random input { [120000000]i64 [120000000]u32 [10]u32 [10]u32 }
-- random input { [130000000]i64 [130000000]u32 [10]u32 [10]u32 }
-- random input { [140000000]i64 [140000000]u32 [10]u32 [10]u32 }

let histo_max [w][n] (is: [n]i64) (vs: [n]u32, hist0: [w]u32) : *[w]u32 =
  let hist0' = map2 (*) hist0 hist0
  in reduce_by_index hist0' (u32.max) (0u32) is vs

entry main [n][w] (is: [n]i64) (vs: [n]u32) (hist: [w]u32) (hist_bar: [w]u32) =
  vjp (histo_max is) (vs, hist) hist_bar