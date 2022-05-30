-- ==
-- entry: main
-- random input { [10000000]i64 [10000000]f32 [10000]f32 }
-- random input { [10000000]i64 [10000000]f32 [50000]f32 }
-- random input { [10000000]i64 [10000000]f32 [100000]f32 }
-- random input { [10000000]i64 [10000000]f32 [500000]f32 }
-- random input { [10000000]i64 [10000000]f32 [1000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [3000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [5000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [7000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [10000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [30000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [50000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [70000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [100000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [110000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [120000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [130000000]f32 }
-- random input { [10000000]i64 [10000000]f32 [140000000]f32 }

entry main [n][w] (is: [n]i64) (vs: [n]f32) (hist: *[w]f32) =
  let hist1 = reduce_by_index (copy hist) (+) 0.0f32 is vs
  in map2 (*) hist1 hist1