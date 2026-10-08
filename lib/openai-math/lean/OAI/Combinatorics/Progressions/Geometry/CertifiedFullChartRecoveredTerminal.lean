/-
Modified for ProveIt: use MvPolynomial.coeff_add in the recovered
coefficient sum, matching the Mathlib 4.32 polynomial coefficient API.
All theorem statements are unchanged from the pinned upstream source.
-/
import OAI.Combinatorics.Progressions.Estimates.Separation
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
import OAI.Combinatorics.Progressions.Polynomial.FrozenPolynomialAffineRange

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientSample_floor_coeff_sum
    (sample : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o sample = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    (fun i => mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (sample j) d i) +
      (fun i => (((coefficientIntegerFloorPolynomial U b o sample c j i).coeff d.val : ℤ) : ℝ)) =
      (c ⟨j, d⟩).val := by
  funext i
  have h := congrArg (fun polynomial : MvPolynomial K ℝ => polynomial.coeff d.val)
    (canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample c hc j i).1
  simp only [coefficientRowPolynomial, monomialArrayPolynomial_coeff _ Subtype.val_injective,
    MvPolynomial.coeff_add,
    mixedLiftPolynomial_coeff _ _ _ _ Subtype.val_injective, coeff_map,
    Int.coe_castRingHom] at h
  exact h.symm

theorem canonicalCoefficientSample_floor_coeff_separate
    (sample : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o sample = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1))
    {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {D : ℝ} (hD : 0 < D)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hsmall : ∀ t, |Q (fun i => mixedLiftCoefficient (euclideanSubspace (U j))
      (b j) (o j) (sample j) d i) t| < 1 / D) :
    Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample c j i).coeff d.val : ℤ) : ℝ)) = 0 := by
  apply (separate_kernel Q _ _ hD ?_ (hgrid _) hsmall).2
  rw [canonicalCoefficientSample_floor_coeff_sum U b hb o sample c hc j d]
  exact hQU (c ⟨j, d⟩).property

end Erdos3.VectorPolynomial

namespace Erdos3

theorem monomialScale_mapDomain_embedding {A B : Type*}
    (f : A ↪ B) (T : B → ℝ) (α : A →₀ ℕ) :
    monomialScale T (α.mapDomain f) = monomialScale (fun i => T (f i)) α := by
  exact Finsupp.prod_mapDomain_index_inj f.injective

end Erdos3

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_long_coeff
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T Long : Type*}
    (keep : Long ↪ LayerSamplerVariables G I n B)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D) (hH : 1 ≤ H)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, H ≤ layerSamplerBox B U b S (keep i))
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (α : Long →₀ ℕ) (hα : α ≠ 0) (hdegree : α.degree ≤ j.val + 1) :
    Q (fun i => (((allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).coeff (α.mapDomain keep) : ℤ) : ℝ)) = 0 := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a, v) k z : ℝ)
  let d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) :=
    ⟨α.mapDomain keep, by simpa only [Finsupp.degree_mapDomain] using hdegree⟩
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  change Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample
    (centeredAffineCoefficientArray U poly hm c frame) j i).coeff d.val : ℤ) : ℝ)) = 0
  apply canonicalCoefficientSample_floor_coeff_separate U b hb o sample _ hc j d Q hQU hD hgrid
  let M : ℝ := C * (((Fintype.card (I j) : ℝ) + 1) * R j)
  let scale : ℝ := monomialScale (layerSamplerBox B U b S) d.val
  have hscale : 0 < scale := monomialScale_pos _
    (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)) d.val
  have hM : 0 ≤ M := mul_nonneg hC (mul_nonneg (by positivity) (hR j).le)
  have hnorm : ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
      (b j) (o j) (sample j) d i‖ ≤ M / scale := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hM hscale.le)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using
      allocatedLayerLiftCoefficient_radius_bound B U b hR hσ S hσ1 o j hC hchart
        (sample j) (h.2.2.1 j).2 d i
  have hscaleH : H ≤ scale := by
    change H ≤ monomialScale (layerSamplerBox B U b S) (α.mapDomain keep)
    rw [monomialScale_mapDomain_embedding]
    exact le_monomialScale_of_ne_zero _ hH hlong hα
  intro t
  calc
    _ ≤ CQ * ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
        (b j) (o j) (sample j) d i‖ := hQ _ t
    _ ≤ CQ * (M / scale) := mul_le_mul_of_nonneg_left hnorm hCQ
    _ = (CQ * M) / scale := (mul_div_assoc CQ M scale).symm
    _ < 1 / D := (div_lt_div_iff₀ hscale hD).mpr (by
      simpa only [one_mul] using hthreshold.trans_le hscaleH)

theorem allocatedRecoveredIntegerFullChart_tag_degree
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) (i : J j) :
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).totalDegree ≤ j.val + 1 :=
  coefficientIntegerFloorPolynomial_degree U b o sample _ j i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*}
    (keep : LayerSamplerVariables G I n B → Prop)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    (Ktarget : Submodule ℝ (J j → ℝ)) (hker : LinearMap.ker Q ≤ Ktarget)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D) (hH : 1 ≤ H)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (j.val + 1)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
          (Sum.inr ⟨j, i⟩)))))) ∈ Ktarget := by
  apply longChart_frozen_top_eval_mem
    (fun i => allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)) keep fixed (j.val + 1)
    (allocatedRecoveredIntegerFullChart_tag_degree B U b o poly hm c a v sample j)
  intro α hdegree
  apply hker
  apply h.integerFullChart_long_coeff B U b hb o S hR hσ poly hm hσ1 c a v sample read j
    ⟨Subtype.val, Subtype.val_injective⟩ Q hQU hC hCQ hD hH hchart hQ hgrid
    (fun i => hlong i.val i.property) hthreshold α _ hdegree.le
  intro hz
  simp [hz] at hdegree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_certified_frozen_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart
        (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i))) ∈ K := by
  obtain ⟨cs, _, hbudget, hK⟩ := hcertificate
  rw [hK]
  refine ⟨Set.mem_univ _, ?_⟩
  intro constraint hc
  have hspan : U constraint.tag ≤
      span ℝ (Set.range (fun q i => (constraint.generators q i : ℝ))) := by
    apply constraint.retained_le_span U hretained
    intro point hpoint
    rw [hK] at hpoint
    exact hpoint.2 constraint hc
  obtain ⟨d, _, Q, hker, hQ, D, hD, hDbound, hgrid⟩ :=
    exists_rationalTaggedSpanProjection constraint.generators hp (hJ constraint.tag)
      ((hbudget constraint hc).1.trans hBp)
      (fun q i => ((hbudget constraint hc).2 q i).trans hBp)
  have hQU : U constraint.tag ≤ LinearMap.ker Q := by
    rw [hker]
    exact hspan
  have hgrid' : ∀ z : J constraint.tag → ℤ, ∀ t,
      ∃ a : ℤ, (D : ℝ) * Q (fun i => (z i : ℝ)) t = a := by
    intro z t
    obtain ⟨w, hw⟩ := hgrid z
    exact ⟨w t, (hw t).symm⟩
  have hnumeric : Real.exp ((p + 2) ^ 9) *
      (C constraint.tag * (((Fintype.card (I constraint.tag) : ℝ) + 1) * R constraint.tag)) *
        (D : ℝ) < H := by
    have hE := Real.exp_nonneg ((p + 2) ^ 9)
    calc
      _ ≤ Real.exp ((p + 2) ^ 9) * M * (D : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcap constraint.tag) hE)
          (Nat.cast_nonneg D)
      _ ≤ Real.exp ((p + 2) ^ 9) * M * Real.exp ((p + 2) ^ 9) :=
        mul_le_mul_of_nonneg_left hDbound (mul_nonneg hE hM)
      _ = Real.exp ((p + 2) ^ 9) ^ 2 * M := by ring
      _ < H := hthreshold
  exact h.integerFullChart_frozen_top_range B U b hb o S hR hσ poly hm hσ1 c a v sample read
    constraint.tag keep Q hQU _ (le_of_eq hker) (hC constraint.tag)
    (Real.exp_nonneg _) (by exact_mod_cast hD) hH (hchart constraint.tag) hQ hgrid'
    hlong hnumeric fixed x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_certified_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) i))) ∈ K := by
  exact h.integerFullChart_certified_frozen_top_range B U b hb o S hR hσ poly hm
    hσ1 c a v sample read K hcertificate hretained hp hBp hJ C hC hchart hM hcap
    keep hH hlong hthreshold fixed x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {G X ι η L : Type} [Fintype G] [Fintype η]
  [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
  (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) =
    projectedIntegerLattice (euclideanSubspace (Utag j)))
  (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
  {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B Utag btag R σ)
  (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {N : X → ℕ} {Bphase Bcertificate p M H : ℝ}

theorem allocatedRecovered_terminal_mem_fast_of_certificate
    (history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
      Z Set.univ Utag poly N Bphase s)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bcertificate
      (s * (Fintype.card η * m)))
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, Utag j) (origin : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag
      S hR hσ poly hm c origin v sample read)
    (hp : 0 ≤ p) (hBp : Bcertificate ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B Utag btag S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬keep i} → ℤ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g = Z) :
    let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm
      c origin v sample keep fixed
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (fun z => homogeneousComponent (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
      (fun z => sampledTopPhase_coordinate_homogeneous
        (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
    ∀ u : {i // keep i} → ℝ,
      eval₂ u (F.realGradedSymbolPolynomial b ω hF (fun _ : {i // keep i} => 1)
        ((pull history.outer.1)⁻¹ *
          F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
            (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
              (fun _ : {i // keep i} => 1) (integerSampledRealChart β)
              (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm
                c origin v sample keep fixed) g) *
          (pull history.outer.2)⁻¹).coord) ∈ fast.baseChange ℝ := by
  apply history.allocatedFrozen_terminal_mem_fast B Utag btag otag poly hm hfast
    c origin v sample keep fixed g hZ
  intro u
  exact hrecovered.integerFrozenFullChart_certified_top_range B Utag btag hbtag otag
    S hR hσ poly hm hσ1 c origin v sample read history.K hcertificate
    (fun t ht => history.retained t (Set.mem_univ _) ht) hp hBp hJ C hC hchart hM hcap
    keep hH hlong hthreshold fixed u

theorem allocatedRecovered_terminal_mem_symbolPointwiseSubalgebra_of_certificate
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    {basisW : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
    {liftW : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basisW liftW
      Z Set.univ Utag poly N Bphase s)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bcertificate
      (s * (Fintype.card η * m)))
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, Utag j) (origin : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag
      S hR hσ poly hm c origin v sample read)
    (hp : 0 ≤ p) (hBp : Bcertificate ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B Utag btag S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬keep i} → ℤ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g = Z) :
    let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm
      c origin v sample keep fixed
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (fun z => homogeneousComponent (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
      (fun z => sampledTopPhase_coordinate_homogeneous
        (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
    ((pull history.outer.1)⁻¹ *
      F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i // keep i} => 1) (integerSampledRealChart β)
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm
            c origin v sample keep fixed) g) *
      (pull history.outer.2)⁻¹).coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i // keep i} => 1) W) := by
  intro β pull
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
    (fun _ : {i // keep i} => 1) W _).mpr
  exact history.allocatedRecovered_terminal_mem_fast_of_certificate B Utag btag hbtag otag S hR hσ
    poly hm hcertificate hW hσ1 c origin v sample read hrecovered hp hBp hJ C hC hchart hM hcap
    keep hH hlong hthreshold fixed g hZ

theorem StageBounds.allocatedRecovered_terminal_mem_symbolPointwiseSubalgebra
    {cap cumulative : ℕ → ℝ}
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    {basisW : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
    {liftW : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basisW liftW
      Z Set.univ Utag poly N Bphase s)
    (hstage : StageBounds cap cumulative history)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, Utag j) (origin : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag
      S hR hσ poly hm c origin v sample read)
    (hp : 0 ≤ p) (hBp : cumulative s ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B Utag btag S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬keep i} → ℤ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g = Z) :
    let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm
      c origin v sample keep fixed
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (fun z => homogeneousComponent (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
      (fun z => sampledTopPhase_coordinate_homogeneous
        (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
    ((pull history.outer.1)⁻¹ *
      F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i // keep i} => 1) (integerSampledRealChart β)
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm
            c origin v sample keep fixed) g) *
      (pull history.outer.2)⁻¹).coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i // keep i} => 1) W) := by
  exact history.allocatedRecovered_terminal_mem_symbolPointwiseSubalgebra_of_certificate
    B Utag btag hbtag otag S hR hσ poly hm W hstage.certificate hW hσ1
    c origin v sample read hrecovered hp hBp hJ C hC hchart hM hcap
    keep hH hlong hthreshold fixed g hZ

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
