-- Simple reduce with multiplication
-- ==
-- entry: main
-- compiled input { [0i64, 0i64, 0i64, 0i64] [1i64, 2i64, 3i64, 4i64] [1i64]} output { [24i64, 12i64, 8i64, 6i64] [24i64] }


let histo_gen [w][n] (is: [n]i64) (vs: [n]i64, dest: [w]i64) : [w]i64 =
    reduce_by_index (copy dest) (*) 1i64 is vs

entry main [n][w] (is: [n]i64) (vs: [n]i64) (hist_bar: [w]i64) =
    vjp (histo_gen is) (vs, replicate w 1i64) hist_bar

-- [0i64, 0i64, 0i64, 0i64] 
-- [1i64, 2i64, 3i64, 4i64] 
-- [1i64]