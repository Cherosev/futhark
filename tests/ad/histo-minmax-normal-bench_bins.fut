-- ==
-- entry: main
-- random input { [1000000]i64 [1000000]i64 [10000]i64     }
-- random input { [1000000]i64 [1000000]i64 [50000]i64     }
-- random input { [1000000]i64 [1000000]i64 [100000]i64    }
-- random input { [1000000]i64 [1000000]i64 [500000]i64    }
-- random input { [1000000]i64 [1000000]i64 [1000000]i64   }
-- random input { [1000000]i64 [1000000]i64 [3000000]i64   }
-- random input { [1000000]i64 [1000000]i64 [5000000]i64   }
-- random input { [1000000]i64 [1000000]i64 [7000000]i64   }
-- random input { [1000000]i64 [1000000]i64 [10000000]i64  }
-- random input { [1000000]i64 [1000000]i64 [30000000]i64  }
-- random input { [1000000]i64 [1000000]i64 [50000000]i64  }
-- random input { [1000000]i64 [1000000]i64 [70000000]i64  }
-- random input { [1000000]i64 [1000000]i64 [100000000]i64 }
-- random input { [1000000]i64 [1000000]i64 [110000000]i64 }
-- random input { [1000000]i64 [1000000]i64 [120000000]i64 }
-- random input { [1000000]i64 [1000000]i64 [130000000]i64 }
-- random input { [1000000]i64 [1000000]i64 [140000000]i64 }


entry main [n][w] (is: [n]i64) (vs: [n]i64) (hist: [w]i64) =
  reduce_by_index hist (i64.max) (0i64) is vs