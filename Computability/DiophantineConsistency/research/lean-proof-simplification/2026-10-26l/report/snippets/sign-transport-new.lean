  have hJp_of_sign {t : ℤ} (hJs : (J : ℤ) ≡ t * s [ZMOD c])
      (ht : t = 1 ∨ t = -1) :
      (c : ℤ) ∣ (J : ℤ) - p ∨ (c : ℤ) ∣ (J : ℤ) + p := by
    have hJs' := Int.modEq_iff_dvd.1 hJs
    rcases ht with rfl | rfl <;> simp only [one_mul, neg_one_mul] at hJs'
    · exact hsp'.imp
        (fun h => by convert! dvd_sub h hJs' using 1; ring)
        (fun h => by convert! dvd_sub h hJs' using 1; ring)
    · exact hsp'.symm.imp
        (fun h => by convert! dvd_neg.mpr (dvd_add h hJs') using 1; ring)
        (fun h => by convert! dvd_neg.mpr (dvd_add h hJs') using 1; ring)
