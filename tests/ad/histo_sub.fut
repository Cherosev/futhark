-- Simple histogram with multiplication
-- ==
-- compiled input { [1i64, 3i64, 2i64,-1i64, 2i64, 1i64, 1i64, 2i64, 3i64, 2i64,-1i64, 2i64, 2i64]
--				    [1f32, 1f32, 1f32, 1f32, 1f32, 1f32, 1f32, 1f32, 1f32, 1f32, 1f32, 1f32, 1f32]
--				    [4f32, 3f32, 2f32, 1f32]
--				    [9f32, 8f32, 7f32, 5f32]
--				  }
-- output {         [8f32, 5f32, 7f32, 0f32, 7f32, 8f32, 8f32, 7f32, 5f32, 7f32, 0f32, 7f32, 7f32]
--					[9f32, 8f32, 7f32, 5f32]
--        }

let histo_plus [w][n] (is: [n]i64) (vs: [n]i64, hist: [w]i64) : [w]i64 =
  reduce_by_index (copy hist) (-) 0i64 is vs

entry main [n][w] (is: [n]i64) (vs: [n]i64) (hist: *[w]i64) (hist_bar: [w]i64) =
  vjp (histo_plus is) (vs,hist) hist_bar