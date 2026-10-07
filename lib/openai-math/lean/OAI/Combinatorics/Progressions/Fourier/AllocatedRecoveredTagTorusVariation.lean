/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Fourier.IntegerPolynomialTorusPeriod
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal

namespace OAI

section

namespace Erdos3

theorem unitCircle_dist_div_integer_parts {q : ℕ} (hq : 0 < q)
    (center r₀ r₁ : ℝ) (z₀ z₁ : ℤ)
    (hz : (((z₀ : ℝ) / q : ℝ) : UnitAddCircle) =
      (((z₁ : ℝ) / q : ℝ) : UnitAddCircle)) :
    dist (((center + r₀ + z₀) / q : ℝ) : UnitAddCircle)
      (((center + r₁ + z₁) / q : ℝ) : UnitAddCircle) ≤ |r₀ - r₁| / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [add_div, AddCircle.coe_add, hz, dist_add_right, dist_add_left]
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  calc
    _ ≤ ‖r₀ / (q : ℝ) - r₁ / q‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |r₀ - r₁| / q := by rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hqR]

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem physicalGridFactorInput_dist_le_of_integer_remainders
    (q : ℕ) (hq : 0 < q) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u v : X → ℝ) (center r₀ r₁ : ∀ j, J j → ℝ) (z₀ z₁ : ∀ j, J j → ℤ)
    (hu : ∀ j i, eval u (poly j) i = center j i + r₀ j i + (z₀ j i : ℝ))
    (hv : ∀ j i, eval v (poly j) i = center j i + r₁ j i + (z₁ j i : ℝ))
    (hz : ∀ j i, (((z₀ j i : ℝ) / q : ℝ) : UnitAddCircle) =
      (((z₁ j i : ℝ) / q : ℝ) : UnitAddCircle))
    {ε : ℝ} (hε : 0 ≤ ε) (herr : ∀ j i, |r₀ j i - r₁ j i| ≤ ε) :
    dist (physicalGridFactorInput q poly u) (physicalGridFactorInput q poly v) ≤ ε / q := by
  apply (dist_pi_le_iff (div_nonneg hε (Nat.cast_nonneg q))).mpr
  intro z
  change dist (((eval u (poly z.1) z.2 / q : ℝ) : UnitAddCircle))
    (((eval v (poly z.1) z.2 / q : ℝ) : UnitAddCircle)) ≤ _
  rw [hu, hv]
  exact (unitCircle_dist_div_integer_parts hq _ _ _ _ _ (hz z.1 z.2)).trans
    (div_le_div_of_nonneg_right (herr z.1 z.2) (Nat.cast_nonneg q))

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G : Type*} [Fintype G] {I E : Fin m → Type*}
variable [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder_at_site
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℤ) (j : Fin m) (i : J j) :
    eval (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)) (poly j) i =
      (c j).val i + mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (x k : ℝ)) i +
      (MvPolynomial.eval x (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)) : ℝ) := by
  have hr := h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read
    (fun k => (x k : ℝ)) j i
  rw [← eval_jointIntegerPhysicalSite_eq_frame a v, integerSampledRealChart_eval] at hr
  linarith

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_torus_dist
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (q : ℕ) (hq : 0 < q) (x y : LayerSamplerVariables G I n B → ℤ)
    (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q))
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j i, |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (x k : ℝ)) i -
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (y k : ℝ)) i| ≤ ε) :
    dist (physicalGridFactorInput q poly (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)))
      (physicalGridFactorInput q poly (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))) ≤ ε / q := by
  apply physicalGridFactorInput_dist_le_of_integer_remainders q hq poly
    (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ))
    (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))
    (fun j => (c j).val)
    (fun j => mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 (fun k => (x k : ℝ)))
    (fun j => mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 (fun k => (y k : ℝ)))
    (fun j i => MvPolynomial.eval x
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample (Sum.inr ⟨j, i⟩)))
    (fun j i => MvPolynomial.eval y
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample (Sum.inr ⟨j, i⟩)))
    (h.integerFullChart_remainder_at_site B U b hb o S hR hσ poly hm hp c a v sample read x)
    (h.integerFullChart_remainder_at_site B U b hb o S hR hσ poly hm hp c a v sample read y)
    (fun j i => integerPolynomial_eval_addCircle_div_eq _ q x y hxy) hε herr

theorem AllocatedCenteredFramedRecoveredSampleAt.frozenIntegerFullChart_torus_dist
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬ keep i} → ℤ)
    (q : ℕ) (hq : 0 < q) (x y : {i // keep i} → ℤ)
    (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q))
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j i, |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => ((finiteSplitPoint keep x fixed k : ℤ) : ℝ)) i -
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => ((finiteSplitPoint keep y fixed k : ℤ) : ℝ)) i| ≤ ε) :
    dist (physicalGridFactorInput q poly (fun z => (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) x z : ℝ)))
      (physicalGridFactorInput q poly (fun z => (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) y z : ℝ))) ≤ ε / q := by
  rw [allocatedFrozenIntegerFullChart_spatial, allocatedFrozenIntegerFullChart_spatial]
  apply h.integerFullChart_torus_dist B U b hb o S hR hσ poly hm hp c a v sample read q hq
    (finiteSplitPoint keep x fixed) (finiteSplitPoint keep y fixed) _ hε herr
  intro k
  classical
  by_cases hk : keep k
  · simpa only [finiteSplitPoint, dite_eq_left hk] using hxy ⟨k, hk⟩
  · simp only [finiteSplitPoint, dite_eq_right hk]

end VectorPolynomial
end Erdos3

end

end OAI
