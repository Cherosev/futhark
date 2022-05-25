-- Validation of histogram with multiplication
-- ==
-- entry: rev fwd
-- compiled input @ histo-gen-data1.txt
-- output @ histo-gen-data1Res.txt
-- compiled input @ histo-gen-data2.txt
-- output @ histo-gen-data2Res.txt
-- compiled input @ histo-gen-data3.txt
-- output @ histo-gen-data3Res.txt

def singleadj (n: i64) (i: i64) (adj: f32) : [n]f32 =
  map (\j -> if (i==j) then adj else 0.0f32) (iota n)
  
let histo_mul [n][w](is: [n]i64) (dest: [w]f32) (vs: [n]f32) : [w]f32 =
  reduce_by_index (copy dest) (*) 1f32 is vs

entry rev [n][w](is: [n]i64) (vs: [n]f32) (hist_orig: [w]f32) (hist_bar': [w]f32) =
  map (\i -> vjp (histo_mul is hist_orig) vs (singleadj w i hist_bar'[i])) (iota w)


entry fwd [n][w](is: [n]i64) (vs: [n]f32) (hist_orig: [w]f32) (hist_bar': [w]f32) =
  map (jvp (histo_mul is (hist_orig: [w]f32)) vs) 
    (map (\ i -> let adj = if is[i] < 0i64 then 0f32 else hist_bar'[is[i]]
                 in singleadj n i adj) (iota n))
  |> transpose