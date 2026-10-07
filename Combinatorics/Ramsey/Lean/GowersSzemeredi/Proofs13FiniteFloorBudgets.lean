import GowersSzemeredi.Proofs13FiniteRowBudgets

/-! Account for the floor and possible missing endpoint in the initial
progression, using explicit finite coefficient reserves. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finite_floor_progression_lower {c d e u : Real}
    (hc : 0 < c) (hd : 0 < d) (hexp : 2 * e ≤ u) (hcoeff : 4 * c ^ 2 ≤ d)
    (N p L : Nat) (hN : 1 ≤ N) (hlarge : 1 ≤ c * (N : Real) ^ e)
    (hfloor : IsNatFloor (d * (N : Real) ^ u) p) (hL : L = p ∨ L + 1 = p) :
    d / 2 * (N : Real) ^ u ≤ L := by
  have hNone : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : Real) ≤ N := Nat.cast_nonneg _
  have hroot : 4 ≤ d * (N : Real) ^ u := by
    calc
      _ ≤ 4 * (c * (N : Real) ^ e) ^ 2 := by nlinarith only [hlarge]
      _ = (4 * c ^ 2) * (N : Real) ^ (2 * e) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hN0]
        ring_nf
      _ ≤ d * (N : Real) ^ (2 * e) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNone hexp) hd.le
  have hp := hfloor.2
  rcases hL with hL | hL
  · subst L
    nlinarith only [hp, hroot]
  · have hLc : (L : Real) + 1 = p := by exact_mod_cast hL
    nlinarith only [hp, hroot, hLc]

theorem finite_floor_row_budgets {c d z e u v w : Real}
    (hc : 0 < c) (hd : 0 < d) (hz : 0 < z) (hu : 0 < u)
    (hv : 0 < v) (hvone : v ≤ 1) (hw : 0 < w) (hwone : w ≤ 1)
    (hcsmall : 2 * c ≤ 1) (hdsmall : d ≤ 2)
    (hsquare : 2 * e ≤ 1) (hrec : 2 * e ≤ u * v) (hbohr : 2 * e ≤ u * w)
    (hrecCoeff : 12 * c ^ 2 ≤ d) (hbohrCoeff : 4 * c ^ 2 ≤ z * d)
    (N p L Q : Nat) (hN : 1 ≤ N) (hlarge : 1 ≤ c * (N : Real) ^ e)
    (hfloor : IsNatFloor (d * (N : Real) ^ u) p) (hL : L = p ∨ L + 1 = p)
    (hQ : (L : Real) ^ v / 2 ≤ Q) :
    ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
      c * (N : Real) ^ e ≤ m ∧ (L : Real) ^ (-w) ≤ z / m := by
  have hdhalf : 0 < d / 2 := by positivity
  have hdhalf1 : d / 2 ≤ 1 := by linarith only [hdsmall]
  have hlower := finite_floor_progression_lower hc hd
    (hrec.trans (by nlinarith only [hu, hvone] : u * v ≤ u))
    (by nlinarith only [hrecCoeff, sq_nonneg c] : 4 * c ^ 2 ≤ d)
    N p L hN hlarge hfloor hL
  have hpow (s : Real) (hs : s ≤ 1) : d / 2 ≤ (d / 2) ^ s := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hdhalf hdhalf1 hs
  obtain ⟨m, hm, hmsq, hmQ, hmlower, hmbohr⟩ := finite_rounded_row_budgets
    hc hdhalf hz hv hw hcsmall hsquare hrec hbohr
    ((by linarith only [hrecCoeff] : 6 * c ^ 2 ≤ d / 2).trans (hpow v hvone))
    ((by nlinarith only [hbohrCoeff] : 2 * c ^ 2 ≤ z * (d / 2)).trans
      (mul_le_mul_of_nonneg_left (hpow w hwone) hz.le))
    N hN L Q hlarge hlower hQ
  exact ⟨m, hm, by simpa only [pow_two] using hmsq, by exact_mod_cast hmQ, hmlower, hmbohr⟩

end LeanProofs.GowersSzemeredi
