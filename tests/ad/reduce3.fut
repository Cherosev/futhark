-- Simple reduce with multiplication
-- ==
-- entry: rev_J
-- compiled input { [1.0f32, 2.0f32, 3.0f32, 4.0f32] 1.0f32} output { [24.0f32, 12.0f32, 8.0f32, 6.0f32] 24.0f32 }
-- compiled input { [1.0f32, 2.0f32, 0.0f32, 4.0f32] 1.0f32} output { [0.0f32, 0.0f32, 8.0f32, 0.0f32] 0.0f32 }
-- compiled input { [1.0f32, 0.0f32, 0.0f32, 4.0f32] 1.0f32} output { [0.0f32, 0.0f32, 0.0f32, 0.0f32] 0.0f32 }
-- compiled input { [1.0f32, 2.0f32, 3.0f32, 4.0f32] 2.0f32} output { [48.0f32, 24.0f32, 16.0f32, 12.0f32] 24.0f32 }
-- compiled input { [1.0f32, 2.0f32, 0.0f32, 4.0f32] 2.0f32} output { [0.0f32, 0.0f32, 16.0f32, 0.0f32] 0.0f32 }
-- compiled input { [1.0f32, 0.0f32, 0.0f32, 4.0f32] 2.0f32} output { [0.0f32, 0.0f32, 0.0f32, 0.0f32] 0.0f32 }

def red_mult [n] (xs: [n]f32, c: f32)  : f32 =
  reduce (*) 1.0 xs * c

entry fwd_J [n] (xs: [n]f32) (c: f32) = 
    let arrayAdjs = tabulate (n+1) (\i -> 
                            jvp red_mult (xs, c)
                            (tabulate n ((==i) >-> f32.bool),
                            if i == n then 1.0 else 0.0))
    in (arrayAdjs[:n], arrayAdjs[n])

entry rev_J [n] (xs: [n]f32) (c: f32) =
  vjp red_mult (xs, c) 1.0