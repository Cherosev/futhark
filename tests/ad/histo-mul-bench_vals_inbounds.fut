-- ==
-- entry: main
-- compiled input @ histo-mul-bench-data0.txt
-- compiled input @ histo-mul-bench-data1.txt
-- compiled input @ histo-mul-bench-data2.txt
-- compiled input @ histo-mul-bench-data3.txt
-- compiled input @ histo-mul-bench-data4.txt
-- compiled input @ histo-mul-bench-data5.txt


let histo_mul [w][n] (is: [n]i64) (vs: [n]f32, hist: [w]f32) : [w]f32 =
  let hist1 = reduce_by_index (copy hist) (*) 1.0f32 is vs
  in map2 (*) hist1 hist1

entry main [n][w] (is: [n]i64) (vs: [n]f32) (hist: [w]f32) (hist_bar: [w]f32) =
  vjp (histo_mul is) (vs,hist) hist_bar