-- ==
-- entry: main
-- random input { [1000000]i64 [1000000]f32 [1000000]f32   [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [3000000]f32   [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [5000000]f32   [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [7000000]f32   [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [10000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [30000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [40000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [50000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [60000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [70000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [80000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [90000000]f32  [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [100000000]f32 [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [110000000]f32 [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [120000000]f32 [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [130000000]f32 [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [140000000]f32 [10]f32 }


let histo_plus [w][n] (is: [n]i64) (vs: [n]f32, hist: [w]f32) : [10]f32 =
  reduce_by_index (copy hist) (+) (0f32) is vs

entry main [n][w] (is: [n]i64) (vs: [n]f32) (hist: *[w]f32) (hist_bar: [10]f32) =
  vjp (histo_plus is) (vs,hist) hist_bar