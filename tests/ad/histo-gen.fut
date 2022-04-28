-- Simple reduce with multiplication
-- ==
-- entry: main
-- compiled input { [0i64, 0i64, 0i64, 0i64] [1f32, 2f32, 3f32, 4f32] [1f32]} output { [24f32, 12f32, 8f32, 6f32] [24f32] }


let histo_gen [w][n] (is: [n]i64) (vs: [n]f32, dest: [w]f32) : [w]f32 =
    reduce_by_index (copy dest) (*) 1f32 is vs

entry main [n][w] (is: [n]i64) (vs: [n]f32) (hist_bar: [w]f32) =
    vjp (histo_gen is) (vs, replicate w 1f32) hist_bar

-- [0i64, 0i64, 0i64, 0i64] 
-- [1f32, 2f32, 3f32, 4f32] 
-- [1f32]