import GowersSzemeredi.Proofs18QuadraticThresholdGrowth

/-! A fully quantified one-step alternative for progressions of length four.
Iteration between cyclic and interval models is not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A convenient explicit single-exponential sufficient modulus. -/
def quadraticExponentialThreshold (alpha : Real) : Real :=
  Real.exp ((4 + 6 * section5LocalRefinementConstant 2 1) *
    (2 / alpha) ^ (12380 * 2048 + 24744 : Nat))

/-- The density-increment conclusion under a single-exponential bound. -/
theorem quadratic_density_increment_of_exp_power
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : quadraticExponentialThreshold alpha ≤ N)
    (A : Finset (ZMod N)) (hnot : ¬ UniformSetOfDegree A alpha 2) :
    ∃ P : ModAP N, P.IsProper ∧
      quadraticDiscrepancyParameter alpha / 4 * (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
        (P.carrier.card : Real) ∧
      (density A + quadraticDiscrepancyParameter alpha / 4) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  exact quadratic_nonuniformity_density_increment_explicit alpha hα hαone N
    ((quadraticDensityThreshold_le_exp_power hα hαone).trans hN) A hnot

/-- Above the explicit analytic and uniform-counting thresholds, every set
of positive density either contains a nonconstant four-term progression or
has a positive density increment on a long proper progression. -/
theorem quadratic_explicit_cyclic_dichotomy
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : quadraticExponentialThreshold alpha ≤ N)
    (A : Finset (ZMod N)) (hkN : 4 ≤ N) (hδ : 0 < density A)
    (hαδ : alpha ≤ (density A / 2) ^ (64 : Nat))
    (hscale : 512 * (density A) ^ (-(4 : Real)) ≤ N) :
    HasModAP A 4 ∨ ∃ P : ModAP N, P.IsProper ∧
      quadraticDiscrepancyParameter alpha / 4 * (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
        (P.carrier.card : Real) ∧
      (density A + quadraticDiscrepancyParameter alpha / 4) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  by_cases hU : UniformSetOfDegree A alpha 2
  · left
    apply corollary_3_6_holds N 4 hkN A alpha (density A) hδ (by omega)
    · unfold density
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp
    · exact hU
    · norm_num
      exact hαδ
    · norm_num at hscale ⊢
      exact hscale
  · exact Or.inr (quadratic_density_increment_of_exp_power alpha hα hαone N hN A hU)

end LeanProofs.GowersSzemeredi
