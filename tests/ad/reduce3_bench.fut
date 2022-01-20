-- ==
-- entry: rev_J
-- random input { [100]i64 i64 }
-- random input { [500]i64 i64 }
-- random input { [1000]i64 i64 }
-- random input { [5000]i64 i64 }
-- random input { [10000]i64 i64 }
-- random input { [50000]i64 i64 }
-- random input { [100000]i64 i64 }
-- random input { [500000]i64 i64 }
-- random input { [1000000]i64 i64 }
-- random input { [5000000]i64 i64 }
-- random input { [10000000]i64 i64 }
-- random input { [50000000]i64 i64 }
-- random input { [100000000]i64 i64 }

def red_mult [n] (xs: [n]f32, c: f32) : f32 =
  reduce (*) 1 xs * c

entry fwd_J [n] (xs: [n]f32) (c: f32) = 
    let arrayAdjs = tabulate (n+1) (\i -> 
                            jvp red_mult (xs, c)
                            (tabulate n ((==i) >-> f32.bool),
                            if i == n then 1.0 else 0.0))
    in (arrayAdjs[:n], arrayAdjs[n])

entry rev_J [n] (xs: [n]f32) (c: f32) = 
    vjp red_mult (xs, c) 1.0