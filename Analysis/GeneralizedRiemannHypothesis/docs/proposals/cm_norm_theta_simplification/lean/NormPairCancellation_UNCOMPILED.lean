/-
Candidate source-level replacement for part of
New.Derivatives.Sharpness.LeastValuation.

Portions adapted from the readable GRH development:
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Upstream attribution details are retained in ATTRIBUTION.md.

Adapted source proofs:
  src/New/Derivatives/Sharpness/LeastValuation.lean
    prod_rescale_theta_mem and LeastValLE.add/leastValLE_zero;
  src/Lib/CM/Integrality/LogTheta.lean
    expSubst_sub_rescale_eq and expSubst_sub_rescale_mem.
Changes in this proposal: replace the rational-square norm parameters by
arbitrary pairs in normPairClosure; specialize to a norm parameter of -1;
add an explicit zero-degree copy-padding wrapper.
Repository: https://github.com/VladimirReshetnikov/ProveIt
Project path: Analysis/GeneralizedRiemannHypothesis/Lean/grh

STATUS: NOT ELABORATED OR KERNEL-CHECKED IN THIS SESSION.
This module contains no sorry or added axioms, but its Lean syntax/API use
still requires validation against the pinned project. It is not a completed
four-copy refactor or an independently checked proof of RH.

Pinned ProveIt commit: 89d12dd40424f1217fd818d84877b3da52396a3b.
-/
import New.Derivatives.Sharpness.LeastValuation

open PowerSeries Finset

namespace New.CMLattice

variable {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p]

/-- CM norms, rather than rational squares, suffice for cancellation.
The right coordinate of each pair is the local CM norm parameter. -/
lemma prod_rescale_theta_mem_of_normPairs (C : CMLattice d) {n : ℕ}
    (δ s : Fin n → ℂ_[p])
    (h_pair : ∀ c, (δ c, s c) ∈ normPairClosure d)
    (h_sum : ∑ c, s c = 0) :
    ∏ c, (taylorVia ιₚ C.θ).rescale (δ c) ∈ C.integralSeriesRing := by
  let g : PowerSeries ℂ_[p] := C.negLogTheta
  have hg : PowerSeries.constantCoeff g = 0 := C.constantCoeff_negLogTheta
  have h_prod : ∏ c, (taylorVia ιₚ C.θ).rescale (δ c) =
      ∏ c, expSubst (s c • g - g.rescale (δ c)) := calc
    _ = ∏ c, expSubst (-g.rescale (δ c)) := by
      simp only [taylorVia_theta_eq_expSubst, ← map_neg, g,
        ← rescale_subst (show PowerSeries.constantCoeff (-g) = 0 by simp [hg])]
    _ = expSubst (∑ c, -g.rescale (δ c)) :=
      (expSubst_sum fun c ↦ by simpa using hg).symm
    _ = expSubst (∑ c, (s c • g - g.rescale (δ c))) := by
      simp [sum_sub_distrib, ← sum_smul, h_sum]
    _ = ∏ c, expSubst (s c • g - g.rescale (δ c)) :=
      expSubst_sum fun c ↦ by simp [hg]
  rw [h_prod]
  exact prod_mem fun c _ ↦ C.expSubst_sub_rescale_mem (h_pair c)

/-- A single local CM norm-minus-one multiplier cancels two theta copies. -/
lemma theta_mul_rescale_mem_of_normPair (C : CMLattice d) {δ : ℂ_[p]}
    (h_pair : (δ, -1) ∈ normPairClosure d) :
    taylorVia ιₚ C.θ * (taylorVia ιₚ C.θ).rescale δ ∈ C.integralSeriesRing := by
  have h := C.expSubst_sub_rescale_mem h_pair
  rw [C.expSubst_sub_rescale_eq] at h
  simpa only [neg_one_smul, ← C.taylorVia_theta_eq_expSubst] using h

/-- The two-copy cancellation product is a unit because its constant term is 1. -/
lemma exists_theta_mul_rescale_mul_eq_one (C : CMLattice d) {δ : ℂ_[p]}
    (h_pair : (δ, -1) ∈ normPairClosure d) :
    ∃ V ∈ C.integralSeriesRing,
      (taylorVia ιₚ C.θ * (taylorVia ιₚ C.θ).rescale δ) * V = 1 := by
  have h_mem := C.theta_mul_rescale_mem_of_normPair h_pair
  have h_const : PowerSeries.constantCoeff
      (taylorVia ιₚ C.θ * (taylorVia ιₚ C.θ).rescale δ) = 1 := by
    simp [C.constantCoeff_taylorVia_theta]
  exact C.isSeriesGenerator_translatedY.exists_mul_eq_one h_mem (by simp [h_const])

/-- Extra zero-degree copies let a four-copy bound preserve the old
twelve-copy interface without any change to its valuation budget. -/
lemma LeastValLE.pad {C : CMLattice d} {J X : Type} [Fintype J] [Fintype X]
    {μ : J → X → ℂ_[p]} {m : J → ℕ} {n : ℕ} {ν : X →₀ ℕ} {r : ℝ}
    (h : C.LeastValLE μ m n ν r) (k : ℕ) :
    C.LeastValLE μ m (n + k) ν r := by
  simpa using h.add (leastValLE_zero (n := k))

end New.CMLattice
