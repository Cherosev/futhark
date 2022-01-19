-- Simple reduce with multiplication
-- ==
-- entry: rev_J
-- compiled input { [1i64, 2i64, 3i64, 4i64] 1i64} output { [24i64, 12i64, 8i64, 6i64] 24i64 }

def red_mult [n] (xs: [n]i64, c: i64) : i64 =
  reduce (*) 1 xs * c

entry fwd_J [n] (xs: [n]i64) (c: i64) = 
    let arrayAdjs = tabulate (n+1) (\i -> jvp red_mult (xs, c) (tabulate n ((==i) >-> i64.bool), if i == n then 1 else 0))
    in (arrayAdjs[:n], arrayAdjs[n])

entry rev_J [n] (xs: [n]i64) (c: i64) = 
    vjp red_mult (xs, c) 1