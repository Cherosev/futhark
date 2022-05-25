-- ==
-- entry: main
-- random input { [100]i64 [100]f32 [10]f32 [10]f32 }
-- random input { [1000]i64 [1000]f32 [20]f32 [20]f32 }
-- random input { [10000]i64 [10000]f32 [50]f32 [50]f32 }
-- random input { [100000]i64 [100000]f32 [100]f32 [100]f32 }
-- random input { [1000000]i64 [1000000]f32 [1000]f32 [1000]f32 }
-- random input { [10000000]i64 [10000000]f32 [10000]f32 [10000]f32 }
-- random input { [100000000]i64 [100000000]f32 [100000]f32 [100000]f32 }
-- random input { [1000000000]i64 [1000000000]f32 [1000000]f32 [1000000]f32 }
-- random input { [10000000000]i64 [10000000000]f32 [10000000]f32 [10000000]f32 }




let histo_plus [w][n] (is: [n]i64) (vs: [n]f32, hist: [w]f32) : [w]f32 =
  reduce_by_index (copy hist) (+) 0.0f32 is vs

entry main [n][w] (is: [n]i64) (vs: [n]f32) (hist: *[w]f32) (hist_bar: [w]f32) =
  vjp (histo_plus is) (vs,hist) hist_bar