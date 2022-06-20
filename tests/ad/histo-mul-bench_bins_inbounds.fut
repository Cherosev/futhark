-- ==
-- entry: main
-- compiled input @ histo-mul-bench-bins-data0.txt
-- compiled input @ histo-mul-bench-bins-data1.txt
-- compiled input @ histo-mul-bench-bins-data2.txt
-- compiled input @ histo-mul-bench-bins-data3.txt
-- compiled input @ histo-mul-bench-bins-data4.txt
-- compiled input @ histo-mul-bench-bins-data6.txt
-- compuled input @ histo-mul-bench-bins-data7.txt

let histo_mul [w][n] (is: [n]i64) (vs: [n]f32, hist: [w]f32) : [w]f32 =
  reduce_by_index (copy hist) (*) 1.0f32 is vs

entry main [n][w] (is: [n]i64) (vs: [n]f32) (hist: [w]f32) (hist_bar: [w]f32) =
  vjp (histo_mul is) (vs,hist) hist_bar