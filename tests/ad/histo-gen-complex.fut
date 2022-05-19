def pack (higher: f32) (lower: f32) : u64 =
  let high = (u64.f32 higher)<<32
  let low  = u64.f32 lower
  in high + low

def unpack (x : u64) : (f32, f32) =
  let low = f32.u64 (copy x)
  let high = f32.u64 (x >> 32)
  in (high, low)

def multComplex (a: f32, b: f32) (c: f32, d: f32) =
  let real = (a * c) - (b * d)
  let imaginary = (a * d) + (b * c)
  in (real, imaginary)

def multComplexRev (x: u64) (y: u64) : u64 =
  let a = f32.u64 (copy x)
  let b = f32.u64 (x >> 32)
  let c = f32.u64 (copy y)
  let d = f32.u64 (y >> 32)
  let real = (a * c) - (b * d)
  let imaginary = (a * d) + (b * c)
  let high = (u64.f32 real)<<32
  let low  = u64.f32 imaginary
  in high + low

def singleadj (len: i64) (adj_ind: i64) (adj1: f32) (adj2: f32) =
  let adjs1 = map (\j -> if (j==adj_ind) then adj1 else 0.0f32) (iota len)
  let adjs2 = map (\j -> if (j==adj_ind) then adj2 else 0.0f32) (iota len)
  in zip adjs1 adjs2

def singleadjRev (len: i64) (adj_ind: i64) (adj: u64) : [len]u64 =
  map (\j -> if (j==adj_ind) then adj else 0u64) (iota len)

let histo_complex [n][w](is: [n]i64) (dest: [w](f32, f32)) (vs: [n](f32, f32)) : [w](f32, f32) =
  reduce_by_index (copy dest) multComplex (1.0f32, 1.0f32) is vs

let histo_complex_rev [n][w](is: [n]i64) (dest: [w]u64) (vs: [n]u64) : [w]u64 =
  reduce_by_index (copy dest) multComplexRev (pack 1.0f32 1.0f32) is vs

def runRev [n][w](is: [n]i64) (vs: [n]u64) (hist_orig: [w]u64) (hist_bar: [w]u64) =
  let adjoints = map (\i -> singleadjRev w i hist_bar[i]) (iota w)
  let vs_bars = map (\adjoint -> vjp (histo_complex_rev is hist_orig) vs adjoint) adjoints
  let vs_bar  = reduce (\arr1 arr2 -> map2 (+) arr1 arr2) (replicate n 064) vs_bars
  in unzip (map unpack vs_bar)
  
entry rev [n][w](is: [n]i64) (vs1: [n]f32) (vs2: [n]f32) (hist_orig1: [w]f32) (hist_orig2: [w]f32) (hist_bar1: [w]f32) (hist_bar2: [w]f32) =
  let packed_hist_orig = map2 pack hist_orig1 hist_orig2
  let packed_hist_bar  = map2 pack hist_bar1 hist_bar2
  let packed_vs        = map2 pack vs1 vs2
  in runRev is packed_vs packed_hist_orig packed_hist_bar

entry fwd [n][w](is: [n]i64) (vs1: [n]f32) (vs2: [n]f32) (hist_orig1: [w]f32) (hist_orig2: [w]f32) (hist_bar1: [w]f32) (hist_bar2: [w]f32) =
  let vs_bars = map (jvp (histo_complex is (zip hist_orig1 hist_orig2)) (zip vs1 vs2)) 
                  (map (\ i -> let adj1 = if is[i] < 0i64 then 0.0f32 else hist_bar1[is[i]]
                               let adj2 = if is[i] < 0i64 then 0.0f32 else hist_bar2[is[i]]
                               in singleadj n i adj1 adj2) (iota n))
                |> transpose
  in unzip (map unzip vs_bars)