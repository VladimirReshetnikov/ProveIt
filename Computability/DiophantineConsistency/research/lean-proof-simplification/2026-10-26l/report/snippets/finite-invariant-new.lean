  have heven : ∀ j, S j % 2 = 0 → S (sigma j) % 2 = 0 := by
    intro j hj
    have hm := successor_mod_four sigma S epsilon he hstep hgate' j hj
    omega
  have hpre : S (sigma.symm i) % 2 = 0 :=
    Equiv.Perm.perm_symm_on_of_perm_on_finite heven (by omega)
  have hm := successor_mod_four sigma S epsilon he hstep hgate' _ hpre
  simp only [Equiv.apply_symm_apply, hi] at hm
  omega
