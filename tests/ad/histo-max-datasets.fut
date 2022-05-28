-- Simple histogram with u32.max operator
-- ==
-- entry: rev fwd
-- compiled input @ histo-max-data1.txt
-- output @ histo-max-data1Res.txt
-- compiled input @ histo-max-data2.txt
-- output @ histo-max-data2Res.txt

def singleadj (n: i64) (i: i64) (adj: u32) : [n]u32 =
  map (\j -> if (i==j) then adj else 0u32) (iota n)
  
let histo_max [n][w](is: [n]i64) (dest: [w]u32) (vs: [n]u32) : [w]u32 =
  reduce_by_index (copy dest) (u32.max) u32.lowest is vs

entry rev [n][w](is: [n]i64) (vs: [n]u32) (hist_orig: [w]u32) (hist_bar': [w]u32) =
  map (\i -> vjp (histo_max is hist_orig) vs (singleadj w i hist_bar'[i])) (iota w)


entry fwd [n][w](is: [n]i64) (vs: [n]u32) (hist_orig: [w]u32) (hist_bar': [w]u32) =
  map (jvp (histo_max is (hist_orig: [w]u32)) vs) 
    (map (\ i -> let adj = if is[i] < 0i64 then 0u32 else hist_bar'[is[i]]
                 in singleadj n i adj) (iota n))
  |> transpose