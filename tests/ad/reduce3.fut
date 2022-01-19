-- Simple reduce with multiplication
-- ==
-- entry: rev
-- compiled input { [1i64, 2i64, 3i64, 4i64] 1i64} output { [24i64, 12i64, 8i64, 6i64] 24i64 }

def red_mult [n] (xs: [n]i64, c: i64)  : i64 =
  reduce (*) 1 xs * c

entry rev [n] (xs: [n]i64) (c: i64) =
  vjp red_mult (xs, c) 1