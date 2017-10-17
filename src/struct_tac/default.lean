meta def simp_coe :=
  `[unfold coe lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe,
    try { dsimp * at * }]


