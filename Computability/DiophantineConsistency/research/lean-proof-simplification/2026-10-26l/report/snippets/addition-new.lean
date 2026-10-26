theorem addRel_zero_iff (H : ZFAxioms mem) (x y : V) :
    AddRel H x y (vempty H) ↔ x = vempty H ∧ y = vempty H := by
  constructor
  · intro hxy
    rcases nat_zero_or_succ H y hxy.2.1 with rfl | ⟨n, hn, rfl⟩
    · exact ⟨(addRel_unique H hxy (addRel_zero H hxy.1)).symm, rfl⟩
    · obtain ⟨b, hb⟩ := addRel_total H hxy.1 hn
      have he : vempty H = vsucc H b := addRel_unique H hxy (addRel_succ H hb)
      exact False.elim (vempty_spec H b (he.symm ▸ vsucc_self H b))
  · rintro ⟨rfl, rfl⟩
    exact addRel_zero H (vempty_in_omega H)
