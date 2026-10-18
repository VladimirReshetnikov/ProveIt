import GowersSzemeredi.Proofs18QuadraticSharperEnvelope
import GowersSzemeredi.Proofs18GeneralIteration
import GowersSzemeredi.Proofs18DoubleExponentialBounds

/-! The fully explicit four-term iteration fits the source's stated
quantitative Szemeredi threshold. This is a restricted instance only.

`four_term_explicit_tower_lt_source`,
`quadraticIntervalClosedThreshold_le_source` and `theorem_18_2_four_holds` are
in `Proofs18QuadraticSourceThresholdSide`, outside the final route. -/
set_option autoImplicit false
set_option maxRecDepth 12000
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A concrete base-two double-exponential bound, throughout
0 < delta <= 1/2, with no unspecified multiplicative constant. -/
theorem quadraticIntervalClosedThreshold_le_explicit_tower {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 21))) := by
  let u : Real := delta⁻¹
  let p : Nat := 12402
  let q : Nat := 153 * p
  let E : Nat := 2 ^ 21
  have hu : 2 ≤ u := by
    change 2 ≤ delta⁻¹
    rw [← one_div]
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hb : 2 / intervalQuadraticUniformityParameter delta ≤ u ^ (153 : Nat) :=
    two_div_intervalQuadraticUniformityParameter_le_inv_pow hδ hδhalf
  have habsorb : (2 / intervalQuadraticUniformityParameter delta) ^ p ≤ u ^ q := by
    have h := pow_le_pow_left₀
      (by positivity : (0 : Real) ≤ 2 / intervalQuadraticUniformityParameter delta) hb p
    simpa only [← pow_mul] using h
  have hqE : q + 2 ≤ E := by norm_num [q, p, E]
  have hexp := exp_exp_pow_le_two_rpow_two_rpow hu hqE
  apply (quadraticIntervalClosedThreshold_le_double_exp_alpha_sharp hδ (by linarith)).trans
  exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans hexp

/-- A smaller explicit threshold suffices in the four-term natural-interval
case: the innermost exponent is 2^21 instead of the source's 2^8192. -/
theorem natural_four_term_explicit_tower
    (delta : Real) (N : Nat) (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2)
    (hN : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 21))) ≤ N)
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) : HasNatAP A 4 :=
  hasNatAP_Icc_of_fin_interval
    (fun B hB => quadratic_interval_szemeredi_closed delta hδ (by linarith) N
      ((quadraticIntervalClosedThreshold_le_explicit_tower hδ hδhalf).trans hN) B hB) A hA hcard

end LeanProofs.GowersSzemeredi
