import GowersSzemeredi.Proofs07SimultaneousLinearity

/-!
# Rounding the Corollary 7.11 target upward

This module keeps `cor711_constant_ceiling_budget` and
`corollary_7_11_universal_real_lower_bound`; the rest of the development, with
its description, is in `Proofs07CeilingPartitionSide`, outside the final route. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The improved direct budget allows upward rounding as soon as the
real-power target reaches eight, independently of the density. -/
theorem cor711_constant_ceiling_budget {l q : Nat} {alpha : Real}
    (hl : 0 < l)
    (hlarge : 8 ≤ (l : Real) ^ cor711Exponent alpha q) :
    34 * (Nat.ceil ((l : Real) ^ cor711Exponent alpha q) : Real) ^ 2 ≤
      (l : Real) ^ ((23 / 6) * cor711Exponent alpha q) := by
  have hX : 0 < (l : Real) ^ cor711Exponent alpha q := by positivity
  rw [mul_comm (23 / 6 : Real), Real.rpow_mul (Nat.cast_nonneg l),
    show (23 / 6 : Real) = 11 / 6 + 2 by norm_num, Real.rpow_add hX, Real.rpow_two]
  generalize (l : Real) ^ cor711Exponent alpha q = X at hX hlarge ⊢
  -- `X ^ (11 / 6) ≥ 8 ^ (11 / 6) ≥ 44`, compared through sixth powers
  have h44 : 44 ≤ X ^ (11 / 6 : Real) := by
    refine le_trans ?_ (Real.rpow_le_rpow (by norm_num) hlarge (by norm_num))
    apply (Real.rpow_le_rpow_iff (by norm_num)
      (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0 : Real) < 6)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  -- `⌈X⌉ < X + 1 ≤ 9 X / 8` as `X ≥ 8`, and `34 * (9 / 8) ^ 2 < 44`
  have hc := Nat.ceil_lt_add_one hX.le
  nlinarith [mul_pos (sub_pos.2 hc) (by positivity : (0 : Real) < X + 1 + ⌈X⌉₊),
    mul_nonneg (sub_nonneg.2 hlarge) (by linarith : (0 : Real) ≤ 17 * X + 8),
    mul_nonneg (sub_nonneg.2 h44) (sq_nonneg X), sq_nonneg X]

/-- A domain-dependent partition with the full real-power cell length works
for every Freiman map, with no loss for multiple maps on the same domain. -/
theorem corollary_7_11_universal_real_lower_bound (N q : Nat) [NeZero N] (R : IntAP)
    (A : Fin q → Finset Int) (alpha : Real)
    (hq : 0 < q) (hα : 0 < alpha) (hl : 0 < R.length) (hR : R.IsProper)
    (hA : ∀ i, A i ⊆ R.carrier ∧ alpha * R.length ≤ (A i).card)
    (hlarge : 8 ≤ (R.length : Real) ^ cor711Exponent alpha q) :
    ∃ M : Nat, ∃ P : Fin M → IntAP,
      IsIntAPPartition P R ∧
      (∀ j, (P j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha q ≤ (P j).length) ∧
      (∃ d : Nat, 0 < d ∧ ∀ j, (P j).step = d) ∧
      ∀ phi : Fin q → Int → ZMod N, (∀ i, FreimanHom 8 (A i) (phi i)) →
        ∀ i j, IntAPLinearOn (P j) (A i) (phi i) := by
  obtain ⟨M, P, hP, hcell, hstep, hlinear⟩ :=
    corollary_7_11_universal_budget N q
      (Nat.ceil ((R.length : Real) ^ cor711Exponent alpha q)) R A alpha hq
      (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hl) _)) hα hl hR hA
      (cor711_constant_ceiling_budget hl hlarge)
  refine ⟨M, P, hP, ?_, hstep, hlinear⟩
  intro j
  refine ⟨(hcell j).1, ?_⟩
  rcases (hcell j).2 with hj | hj
  · rw [hj]
    exact Nat.le_ceil _
  · rw [hj, Nat.cast_add, Nat.cast_one]
    exact (Nat.le_ceil _).trans (by linarith)

end LeanProofs.GowersSzemeredi
