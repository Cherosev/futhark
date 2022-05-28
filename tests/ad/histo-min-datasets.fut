-- Simple histogram with i32.min operator
-- ==
-- entry: rev fwd
-- compiled input @ histo-min-data1.txt
-- output @ histo-min-data1Res.txt
-- compiled input @ histo-min-data2.txt
-- output @ histo-min-data2Res.txt

def singleadj (n: i64) (i: i64) (adj: i32) : [n]i32 =
  map (\j -> if (i==j) then adj else 0i32) (iota n)
  
let histo_max [n][w](is: [n]i64) (dest: [w]i32) (vs: [n]i32) : [w]i32 =
  reduce_by_index (copy dest) (i32.min) i32.highest is vs

entry rev [n][w](is: [n]i64) (vs: [n]i32) (hist_orig: [w]i32) (hist_bar': [w]i32) =
  map (\i -> vjp (histo_max is hist_orig) vs (singleadj w i hist_bar'[i])) (iota w)


entry fwd [n][w](is: [n]i64) (vs: [n]i32) (hist_orig: [w]i32) (hist_bar': [w]i32) =
  map (jvp (histo_max is (hist_orig: [w]i32)) vs) 
    (map (\ i -> let adj = if is[i] < 0i64 then 0i32 else hist_bar'[is[i]]
                 in singleadj n i adj) (iota n))
  |> transpose