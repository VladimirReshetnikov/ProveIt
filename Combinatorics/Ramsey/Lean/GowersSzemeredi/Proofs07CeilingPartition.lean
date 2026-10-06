import GowersSzemeredi.Proofs07SimultaneousLinearity

/-!
# Rounding the Corollary 7.11 target upward

The direct numerical budget of the partition construction permits a ceiling
target. Increasing the explicit scale threshold by a factor of four removes
the floor loss while preserving the real-power exponent. This addresses the
integer-rounding obligation in Section 13; the scale condition is retained.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The direct Corollary 7.11 budget holds for the ceiling of the power target
once that target is at least `4096*pi/alpha`. -/
theorem cor711_ceiling_budget {l q : Nat} {alpha : Real}
    (hl : 0 < l) (hq : 0 < q) (hα : 0 < alpha)
    (hlarge : 4096 * Real.pi / alpha ≤ (l : Real) ^ cor711Exponent alpha q) :
    (1024 * Real.pi / alpha) *
        (Nat.ceil ((l : Real) ^ cor711Exponent alpha q) : Real) ^ 2 ≤
      (l : Real) ^ (3 * cor711Exponent alpha q) := by
  let X : Real := (l : Real) ^ cor711Exponent alpha q
  have he : 0 < cor711Exponent alpha q := by unfold cor711Exponent; positivity
  have hX : 1 ≤ X := Real.one_le_rpow (by exact_mod_cast hl) he.le
  have hm : (Nat.ceil X : Real) ≤ 2 * X := by
    have hceil := Nat.ceil_lt_add_one (zero_le_one.trans hX)
    linarith
  have hC : 0 ≤ 1024 * Real.pi / alpha := by positivity
  calc
    _ ≤ (1024 * Real.pi / alpha) * (2 * X) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2) hC
    _ = (4096 * Real.pi / alpha) * X ^ 2 := by ring
    _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right hlarge (sq_nonneg X)
    _ = (l : Real) ^ (3 * cor711Exponent alpha q) := by
      rw [show X * X ^ 2 = X ^ 3 by ring]
      dsimp only [X]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring

/-- A simultaneous affine partition at the ceiling of the real-power target,
with an explicit rounding-safe size hypothesis. -/
theorem corollary_7_11_ceiling (N q : Nat) [NeZero N] (R : IntAP)
    (A : Fin q → Finset Int) (phi : Fin q → Int → ZMod N) (alpha : Real)
    (hq : 0 < q) (hα : 0 < alpha) (hl : 0 < R.length) (hR : R.IsProper)
    (hA : ∀ i, A i ⊆ R.carrier ∧ alpha * R.length ≤ (A i).card ∧
      FreimanHom 8 (A i) (phi i))
    (hlarge : 4096 * Real.pi / alpha ≤
      (R.length : Real) ^ cor711Exponent alpha q) :
    Cor711Conclusion (Nat.ceil ((R.length : Real) ^ cor711Exponent alpha q)) R A phi := by
  have hm : 0 < Nat.ceil ((R.length : Real) ^ cor711Exponent alpha q) :=
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hl) _)
  exact corollary_7_11_of_budget N q _ R A phi alpha hq hm hα hl hR hA
    (cor711_ceiling_budget hl hq hα hlarge)

/-- All cells can be at least the full real-power target, with no floor loss,
under the rounding-safe threshold. -/
theorem corollary_7_11_real_lower_bound (N q : Nat) [NeZero N] (R : IntAP)
    (A : Fin q → Finset Int) (phi : Fin q → Int → ZMod N) (alpha : Real)
    (hq : 0 < q) (hα : 0 < alpha) (hl : 0 < R.length) (hR : R.IsProper)
    (hA : ∀ i, A i ⊆ R.carrier ∧ alpha * R.length ≤ (A i).card ∧
      FreimanHom 8 (A i) (phi i))
    (hlarge : 4096 * Real.pi / alpha ≤
      (R.length : Real) ^ cor711Exponent alpha q) :
    ∃ M : Nat, ∃ P : Fin M → IntAP,
      IsIntAPPartition P R ∧
      (∀ j, (P j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha q ≤ (P j).length) ∧
      (∃ d : Nat, 0 < d ∧ ∀ j, (P j).step = d) ∧
      ∀ i j, IntAPLinearOn (P j) (A i) (phi i) := by
  obtain ⟨M, P, hP, hcell, hstep, hlinear⟩ :=
    corollary_7_11_ceiling N q R A phi alpha hq hα hl hR hA hlarge
  refine ⟨M, P, hP, ?_, hstep, hlinear⟩
  intro j
  refine ⟨(hcell j).1, ?_⟩
  rcases (hcell j).2 with hj | hj
  · rw [hj]
    exact Nat.le_ceil _
  · rw [hj, Nat.cast_add, Nat.cast_one]
    exact (Nat.le_ceil _).trans (by linarith)

/-- The improved direct budget allows upward rounding as soon as the
real-power target reaches eight, independently of the density. -/
theorem cor711_constant_ceiling_budget {l q : Nat} {alpha : Real}
    (hl : 0 < l)
    (hlarge : 8 ≤ (l : Real) ^ cor711Exponent alpha q) :
    34 * (Nat.ceil ((l : Real) ^ cor711Exponent alpha q) : Real) ^ 2 ≤
      (l : Real) ^ ((23 / 6) * cor711Exponent alpha q) := by
  let X : Real := (l : Real) ^ cor711Exponent alpha q
  have hX : 0 < X := Real.rpow_pos_of_pos (by exact_mod_cast hl) _
  have hm : (Nat.ceil X : Real) ≤ (9 / 8) * X := by
    have hceil := Nat.ceil_lt_add_one hX.le
    linarith
  have hpower : (44 : Real) ≤ (8 : Real) ^ (11 / 6 : Real) := by
    apply (Real.rpow_le_rpow_iff (by norm_num)
      (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0 : Real) < 6)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have hlargePower : 44 ≤ X ^ (11 / 6 : Real) := hpower.trans
    (Real.rpow_le_rpow (by norm_num) hlarge (by norm_num))
  calc
    _ ≤ 34 * ((9 / 8) * X) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2) (by norm_num)
    _ ≤ 44 * X ^ 2 := by nlinarith only [sq_nonneg X]
    _ ≤ X ^ (11 / 6 : Real) * X ^ 2 :=
      mul_le_mul_of_nonneg_right hlargePower (sq_nonneg _)
    _ = X ^ (23 / 6 : Real) := by
      rw [← Real.rpow_two, ← Real.rpow_add hX]
      norm_num
    _ = (l : Real) ^ ((23 / 6) * cor711Exponent alpha q) := by
      dsimp only [X]
      rw [← Real.rpow_mul (by exact_mod_cast hl.le)]
      congr 1
      ring

/-- A ceiling-sized simultaneous affine partition with a density-independent
power-target threshold. -/
theorem corollary_7_11_constant_ceiling (N q : Nat) [NeZero N] (R : IntAP)
    (A : Fin q → Finset Int) (phi : Fin q → Int → ZMod N) (alpha : Real)
    (hq : 0 < q) (hα : 0 < alpha) (hl : 0 < R.length) (hR : R.IsProper)
    (hA : ∀ i, A i ⊆ R.carrier ∧ alpha * R.length ≤ (A i).card ∧
      FreimanHom 8 (A i) (phi i))
    (hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha q) :
    Cor711Conclusion (Nat.ceil ((R.length : Real) ^ cor711Exponent alpha q)) R A phi := by
  exact corollary_7_11_constant_budget N q _ R A phi alpha hq
    (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hl) _)) hα hl hR hA
    (cor711_constant_ceiling_budget hl hlarge)

/-- All cells can be at least the full real-power target, with no floor loss,
under the rounding-safe threshold. -/
theorem corollary_7_11_constant_real_lower_bound (N q : Nat) [NeZero N] (R : IntAP)
    (A : Fin q → Finset Int) (phi : Fin q → Int → ZMod N) (alpha : Real)
    (hq : 0 < q) (hα : 0 < alpha) (hl : 0 < R.length) (hR : R.IsProper)
    (hA : ∀ i, A i ⊆ R.carrier ∧ alpha * R.length ≤ (A i).card ∧
      FreimanHom 8 (A i) (phi i))
    (hlarge : 8 ≤
      (R.length : Real) ^ cor711Exponent alpha q) :
    ∃ M : Nat, ∃ P : Fin M → IntAP,
      IsIntAPPartition P R ∧
      (∀ j, (P j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha q ≤ (P j).length) ∧
      (∃ d : Nat, 0 < d ∧ ∀ j, (P j).step = d) ∧
      ∀ i j, IntAPLinearOn (P j) (A i) (phi i) := by
  obtain ⟨M, P, hP, hcell, hstep, hlinear⟩ :=
    corollary_7_11_constant_ceiling N q R A phi alpha hq hα hl hR hA hlarge
  refine ⟨M, P, hP, ?_, hstep, hlinear⟩
  intro j
  refine ⟨(hcell j).1, ?_⟩
  rcases (hcell j).2 with hj | hj
  · rw [hj]
    exact Nat.le_ceil _
  · rw [hj, Nat.cast_add, Nat.cast_one]
    exact (Nat.le_ceil _).trans (by linarith)

end LeanProofs.GowersSzemeredi
