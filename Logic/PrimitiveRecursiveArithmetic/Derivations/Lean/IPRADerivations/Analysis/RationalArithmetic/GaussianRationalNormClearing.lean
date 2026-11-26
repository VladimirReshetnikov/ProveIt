import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantScoreWeights
import IPRADerivations.Analysis.Geometry.GaussianRelativeNormTriangle
import IPRADerivations.Core.LinearCombination

/-!
# Exact transport of relative norm bounds through a common denominator

These local arithmetic rules retain the actual rational operations and
value representations. A derived positive denominator permits cancelling
its square from a weighted norm comparison. Conversely, the exact integer
9-versus-4 bound at a scaled denominator gives the literal rational bound.
No rounding, square root or coefficient nonzeroness is needed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalNormClearing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (represents positive_product)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale add)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def three : PTm n := two+one
def nine : PTm n := three*three
def weightedNorm (K q : PTm n) : PTm n := RationalArithmetic.multiply (fraction K one) (GaussianRationalMetric.qnormSq q)

@[simp] theorem subst_three {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (three : PTm n) = (three : PTm m) := by simp [three]
@[simp] theorem subst_nine {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (nine : PTm n) = (nine : PTm m) := by simp [nine]
@[simp] theorem subst_weightedNorm {m : ℕ} (σ : Fin n → PTm m) (K q : PTm n) :
    Syn.subst σ (weightedNorm K q) = weightedNorm (Syn.subst σ K) (Syn.subst σ q) := by simp [weightedNorm]

theorem weighted_norm_represents (K q a D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] represents q a D) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (weightedNorm K q) (ZT.ofNat (K*normSq a)) (D*D) := by
  have raw := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents K one (le_refl one)) (GaussianRationalMetric.qnormSq_represents q a D hD hq)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := raw)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

/-- Only the derived positive common denominator is cancelled. The
weight and both Gaussian numerators may be zero. -/
theorem weighted_clear (W q r a b D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] represents q a D) (hr : Γ ⊢[PRAAx] represents r b D)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (weightedNorm W q) (GaussianRationalMetric.qnormSq r)) :
    Γ ⊢[PRAAx] le (W*normSq a) (normSq b) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (weighted_norm_represents W q a D hD hq) (GaussianRationalMetric.qnormSq_represents r b D hD hr) h
  exact RationalValueBounds.positive_cancel (positive_product D D hD hD)
    (le_congr (.eqRefl _) (by ipra_ring) raw)

/-- An integer relative bound at the actual scaled denominator transports
back to the literal normalized scalar operations, with the exact 9 and 4. -/
theorem scaled_bound (q r a b C D : PTm n) (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] represents q a (C*D)) (hr : Γ ⊢[PRAAx] represents r b D)
    (h : Γ ⊢[PRAAx] le (nine*normSq a) (four*C*C*normSq b)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (weightedNorm nine q) (weightedNorm four r) := by
  have hCD := positive_product C D hC hD
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ hCD hCD) (positive_product D D hD hD)
    (weighted_norm_represents nine q a (C*D) hCD hq) (weighted_norm_represents four r b D hD hr)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (D*D) h))

theorem norm_sum_scaled (A u v : PTm n) : Γ ⊢[PRAAx]
    normSq (add (scale A u) (scale A v)) ≐ A*A*normSq (add u v) := by
  ipra_lc [ComplexLogarithmRemainder.normSq_eval, GaussianRootAlgebra.re_add, GaussianRootAlgebra.im_add, GaussianRootAlgebra.re_scale, GaussianRootAlgebra.im_scale]

/-- Combine the two actual finite Gaussian sums without applying a linear
norm estimate to their squared norms. -/
theorem two_sum_bound (u v C R : PTm n)
    (hu : Γ ⊢[PRAAx] le (nine*normSq u) (C*C*R))
    (hv : Γ ⊢[PRAAx] le (nine*normSq v) (C*C*R)) : Γ ⊢[PRAAx]
    le (nine*normSq (add u v)) (four*C*C*R) := by
  have left : Γ ⊢[PRAAx] le (normSq (scale three u)) (C*C*R) :=
    le_congr (ComplexLogarithmRemainder.normSq_scale three u).eqSymm (.eqRefl _) hu
  have right : Γ ⊢[PRAAx] le (normSq (scale three v)) (C*C*R) :=
    le_congr (ComplexLogarithmRemainder.normSq_scale three v).eqSymm (.eqRefl _) hv
  exact le_congr (norm_sum_scaled three u v) (by unfold four; ipra_ring)
    (GaussianRelativeNormTriangle.relative_triangle _ _ C C R left right)

theorem weighted_common_denominator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ represents (var 1) (var 3) (var 5) ⟶ represents (var 2) (var 4) (var 5) ⟶
      RationalArgmin.rationalLE (weightedNorm (var 0) (var 1)) (GaussianRationalMetric.qnormSq (var 2)) ⟶
      le (var 0*normSq (var 3)) (normSq (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (weighted_clear _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem scaled_relative_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ le one (var 5) ⟶ represents (var 0) (var 2) (var 4*var 5) ⟶
      represents (var 1) (var 3) (var 5) ⟶ le (nine*normSq (var 2)) (four*var 4*var 4*normSq (var 3)) ⟶
      RationalArgmin.rationalLE (weightedNorm nine (var 0)) (weightedNorm four (var 1))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (scaled_bound _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem two_actual_sum_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (nine*normSq (var 0)) (var 2*var 2*var 3) ⟶ le (nine*normSq (var 1)) (var 2*var 2*var 3) ⟶
      le (nine*normSq (add (var 0) (var 1))) (four*var 2*var 2*var 3)) :=
  closeUniv 4 (.impI (.impI (two_sum_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalNormClearing
