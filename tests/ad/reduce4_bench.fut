-- ==
-- entry: rev_J
-- random input { [1000]i64 i64 }
-- random input { [10000]i64 i64 }
-- random input { [100000]i64 i64 }
-- random input { [1000000]i64 i64 }
-- random input { [10000000]i64 i64 }
-- random input { [100000000]i64 i64 }

def red_mult [n] (xs: [n]i64, c: i64) : i64 =
  reduce (*) 1 xs * c

entry fwd_J [n] (xs: [n]i64) (c: i64) = 
    let arrayAdjs = tabulate (n+1) (\i -> 
                            jvp red_mult (xs, c)
                            (tabulate n ((==i) >-> i64.bool),
                            if i == n then 1 else 0))
    in (arrayAdjs[:n], arrayAdjs[n])

entry rev_J [n] (xs: [n]i64) (c: i64) = 
    vjp red_mult (xs, c) 1