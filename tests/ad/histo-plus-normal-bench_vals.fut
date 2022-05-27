-- ==
-- entry: main
-- random input { [100]i64 [100]f32 [10]f32 }
-- random input { [1000]i64 [1000]f32 [10]f32 }
-- random input { [10000]i64 [10000]f32 [10]f32 }
-- random input { [100000]i64 [100000]f32 [10]f32 }
-- random input { [1000000]i64 [1000000]f32 [10]f32 }
-- random input { [3000000]i64 [3000000]f32 [10]f32 }
-- random input { [5000000]i64 [5000000]f32 [10]f32 }
-- random input { [7000000]i64 [7000000]f32 [10]f32 }
-- random input { [10000000]i64 [10000000]f32 [10]f32 }
-- random input { [30000000]i64 [30000000]f32 [10]f32 }
-- random input { [50000000]i64 [50000000]f32 [10]f32 }
-- random input { [70000000]i64 [70000000]f32 [10]f32 }
-- random input { [100000000]i64 [100000000]f32 [10]f32 }
-- random input { [110000000]i64 [110000000]f32 [10]f32 }
-- random input { [120000000]i64 [120000000]f32 [10]f32 }
-- random input { [130000000]i64 [130000000]f32 [10]f32 }
-- random input { [140000000]i64 [140000000]f32 [10]f32 }


let histo_plus [w][n] (is: [n]i64) (vs: [n]f32, hist: [w]f32) : [w]f32 =
  reduce_by_index (copy hist) (+) 0.0f32 is vs

entry main [n][w] (is: [n]i64) (vs: [n]f32) (hist: *[w]f32) =
  reduce_by_index (copy hist) (+) 0.0f32 is vs