-- ==
-- tags { disable }

let gather xs is = map (\(i: i64) -> xs[i]) is

let mapgather xss is = map (`gather` is) xss

entry fwd (xs: [][]f64) (is: []i64) y =
  jvp (`mapgather` is) xs y

entry rev (xs: [][]f64) (is: []i64) y =
  vjp (`mapgather` is) xs y