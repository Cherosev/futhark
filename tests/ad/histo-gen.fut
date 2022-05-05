-- Simple histogram with multiplication
-- ==
-- entry: fwd rev

def onehot (n: i64) (i: i64) (inp: f32) : [n]f32 =
  tabulate n (\j -> if (i==j) then inp else 0.0f32)
  
let histo_mul [n][w](is: [n]i64) (dest: [w]f32) (vs: [n]f32) : [w]f32 =
  reduce_by_index (copy dest) (*) 1f32 is vs

entry rev [n][w](is: [n]i64) (vs: [n]f32) (hist_bar': [w]f32) =
  map (\i -> vjp (histo_mul is (replicate w 1f32)) vs (onehot w i hist_bar'[i])) (iota w) |> transpose
  

entry fwd [n][w](is: [n]i64) (vs: [n]f32) (hist_bar': [w]f32) =
  map (jvp (histo_mul is (replicate w 1f32)) vs) 
    (map (\ i -> onehot n i hist_bar'[is[i]]) (iota n))

   