/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.FastCoefficientOperationBounds
import OAI.Combinatorics.Progressions.Linear.RationalSpanDerivativeSystem

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def realLayerOneLieSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ] (ℝ ⊗[ℚ] L) :=
  (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2)).baseChange ℝ

theorem realLayerOneLieSection_rightInverse (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.layer 2).mkQ.baseChange ℝ (F.realLayerOneLieSection e ω hF x) = x :=
  realSupportedQuotientSection_rightInverse e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x

theorem realLayerOneLieSection_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : LayerOneBasisIndex ω) :
    (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF x) i =
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr x i :=
  realSupportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i

theorem realLayerOneLieSection_coordinate_zero
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : ι) (hi : 2 ≤ ω i) :
    (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF x) i = 0 :=
  realSupportedQuotientSection_coordinate_zero e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i hi

theorem realLayerOneLieSection_norm [Fintype ι] (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ‖(e.baseChange ℝ).equivFun (F.realLayerOneLieSection e ω hF x)‖ =
      ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ :=
  realSupportedQuotientSection_norm e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x

theorem realLayerOneLieSection_grid [Fintype ι] (l : ℕ)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (hx : ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (F.realLayerOneLieSection e ω hF x) ∈ realDenominatorGrid l :=
  realSupportedQuotientSection_grid e (F.layer 2) {i | 2 ≤ ω i} (hF 2) l x hx

variable [Fintype σ]

noncomputable def layerOnePolynomialCorrection (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  F.realification.linearPolynomialGroup (fun i => F.realLayerOneLieSection e ω hF (a i))

theorem layerOnePolynomialCorrection_log (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ((F.layerOnePolynomialCorrection e ω hF a).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      linearPolynomial (fun i => F.realLayerOneLieSection e ω hF (a i)) := rfl

theorem layerOnePolynomialCorrection_horizontal (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : σ) :
    (F.layer 2).mkQ.baseChange ℝ
      (coefficients ((F.layerOnePolynomialCorrection e ω hF a).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (Finsupp.single i 1)) = a i := by
  rw [F.layerOnePolynomialCorrection_log, coefficients_linearPolynomial_single,
    F.realLayerOneLieSection_rightInverse]

theorem layerOnePolynomialCorrection_constant (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    coefficients ((F.layerOnePolynomialCorrection e ω hF a).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  rw [F.layerOnePolynomialCorrection_log, coefficients_linearPolynomial_zero]

theorem layerOnePolynomialCorrection_slow [Fintype ι]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (a i)‖ ≤ M / T i) :
    F.PolynomialSlowBound e (fun _ => 1) T M (F.layerOnePolynomialCorrection e ω hF a) := by
  apply F.polynomialSlowBound_linear e T hT hM
  intro i j
  have h := norm_le_pi_norm ((e.baseChange ℝ).equivFun (F.realLayerOneLieSection e ω hF (a i))) j
  rw [F.realLayerOneLieSection_norm] at h
  exact h.trans (ha i)

theorem layerOnePolynomialCorrection_grid (l : ℕ)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : (fun z : σ × LayerOneBasisIndex ω =>
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid l) :
    F.PolynomialRationalGrid e (fun _ => 1) l (F.layerOnePolynomialCorrection e ω hF a) := by
  apply F.polynomialRationalGrid_linear
  classical
  obtain ⟨v, hv⟩ := ha
  refine ⟨fun z => if hz : 2 ≤ ω z.2 then 0 else v (z.1, ⟨z.2, hz⟩), ?_⟩
  funext z
  change ((if hz : 2 ≤ ω z.2 then 0 else v (z.1, ⟨z.2, hz⟩) : ℤ) : ℝ) =
    (l : ℝ) * (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF (a z.1)) z.2
  by_cases hz : 2 ≤ ω z.2
  · rw [dite_eq_left hz, F.realLayerOneLieSection_coordinate_zero e ω hF _ _ hz]
    simp only [Int.cast_zero, mul_zero]
  · rw [dite_eq_right hz, F.realLayerOneLieSection_coordinate e ω hF _ ⟨z.2, hz⟩]
    exact congrFun hv (z.1, ⟨z.2, hz⟩)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def realLayerOneCorrection (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.RealAdaptedPolynomialGroup (fun _ : σ => 1) :=
  F.realAdaptedPolynomialGroupLift (fun _ => 1) e ω hF (F.layerOnePolynomialCorrection e ω hF a)

theorem realLayerOneCorrection_realize (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realAdaptedPolynomialGroupHom (fun _ => 1) (F.realLayerOneCorrection e ω hF a) =
      F.layerOnePolynomialCorrection e ω hF a :=
  F.realAdaptedPolynomialGroupHom_lift (fun _ => 1) e ω hF _

theorem realLayerOneCorrection_log (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realLayerOneCorrection e ω hF a).coord =
      linearPolynomial (fun i => F.realLayerOneLieSection e ω hF (a i)) := by
  have he := congrArg (fun g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group =>
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) (F.realLayerOneCorrection_realize e ω hF a)
  exact he

theorem realLayerOneCorrection_slow [Fintype ι]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (a i)‖ ≤ M / T i) :
    F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M (F.realLayerOneCorrection e ω hF a).coord := by
  apply (F.realAdaptedCoefficientBound_polynomial_iff e ω hF (fun _ => 1) T hT hM _).mpr
  rw [F.realLayerOneCorrection_realize]
  exact F.layerOnePolynomialCorrection_slow e ω hF T hT hM a ha

theorem realLayerOneCorrection_grid (l : ℕ)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : (fun z : σ × LayerOneBasisIndex ω =>
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid l) :
    F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l (F.realLayerOneCorrection e ω hF a).coord := by
  apply (F.realAdaptedCoefficientGrid_polynomial_iff e ω hF (fun _ => 1) l _).mpr
  rw [F.realLayerOneCorrection_realize]
  exact F.layerOnePolynomialCorrection_grid e ω hF l a ha

omit [Fintype σ] in
theorem realLayerOneProjection_coordinate (x : ℝ ⊗[ℚ] L) (i : LayerOneBasisIndex ω) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr ((F.layer 2).mkQ.baseChange ℝ x) i =
      (e.baseChange ℝ).repr x i :=
  baseChange_coordinate_eq e (F.layerOneBasis e ω hF) (F.layer 2).mkQ Subtype.val
    (F.layerOneBasis_repr_mk e ω hF) x i

theorem realAdaptedLogDerivative_constant_unit [DecidableEq σ] (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) :
    coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realAdaptedLogDerivative (Pi.single i 1) x)) 0 =
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1) := by
  have he := congrArg
    (fun q : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => coefficients q.val 0)
    (F.realAdaptedLogDerivative_tensor (Pi.single i 1) x)
  exact he.trans (F.realification.adaptedLogDerivative_constant_unit i
    (F.realAdaptedPolynomialTensor (fun _ => 1) x) hx)

include e ω hF in
theorem realFirstCoefficientDirectionMap_horizontal_unit [DecidableEq σ] (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) =
      (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1)) := by
  classical
  have hunit : (Pi.single i (1 : ℝ)) = (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  apply ((F.layerOneBasis e ω hF).baseChange ℝ).repr.injective
  ext j
  rw [F.realFirstCoefficientHorizontal_coordinates e ω hF, hunit,
    F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientBasis_polynomial_coordinate]
  change (e.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
    (F.realAdaptedLogDerivative (Pi.single i 1) x)) 0) j.val = _
  rw [F.realAdaptedLogDerivative_constant_unit i x hx, F.realLayerOneProjection_coordinate]

theorem realLayerOneCorrection_horizontal_derivative [DecidableEq σ]
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : σ) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap (F.realLayerOneCorrection e ω hF a).coord (Pi.single i 1)) =
      a i := by
  have hz : coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF a).coord) 0 = 0 := by
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  rw [F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i _ hz,
    F.realLayerOneCorrection_log, coefficients_linearPolynomial_single,
    F.realLayerOneLieSection_rightInverse]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace VectorPolynomial

theorem homogeneous_one_eq_linearPolynomial {σ R V : Type*} [Fintype σ]
    [CommRing R] [AddCommGroup V] [Module R V] (P : VectorPolynomial σ R V)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients P α = 0) :
    P = linearPolynomial (fun i => coefficients P (Finsupp.single i 1)) := by
  have hdegree : DegreeLE (fun _ : σ => 1) 1 P := fun α hα => hP α (by omega)
  have hzero : coefficients P 0 = 0 := hP 0 (by simp)
  have h := eq_affine_of_degreeLE_one P hdegree
  simpa only [hzero, monomial, TensorProduct.tmul_zero, zero_add] using h

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem realLayerOneLieSection_of_grade (x : ℝ ⊗[ℚ] L)
    (hx : basisGradeProjection (e.baseChange ℝ) ω 1 x = x) :
    F.realLayerOneLieSection e ω hF ((F.layer 2).mkQ.baseChange ℝ x) = x := by
  apply (e.baseChange ℝ).repr.injective
  apply Finsupp.ext
  intro i
  by_cases hi : 2 ≤ ω i
  · rw [F.realLayerOneLieSection_coordinate_zero e ω hF _ i hi]
    have h := congrArg (fun y => (e.baseChange ℝ).repr y i) hx
    rw [basisGradeProjection_repr, ite_eq_right (by omega)] at h
    exact h
  · rw [F.realLayerOneLieSection_coordinate e ω hF _ ⟨i, hi⟩,
      F.realLayerOneProjection_coordinate e ω hF x ⟨i, hi⟩]

theorem homogeneous_one_eq_realLayerOneCorrection_log [Fintype σ]
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients P α = 0)
    (hgrade : ∀ α, basisGradeProjection (e.baseChange ℝ) ω 1 (coefficients P α) = coefficients P α) :
    F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF
        (fun i => (F.layer 2).mkQ.baseChange ℝ (coefficients P (Finsupp.single i 1)))).coord = P := by
  rw [F.realLayerOneCorrection_log]
  have hcoeff : (fun i => F.realLayerOneLieSection e ω hF
      ((F.layer 2).mkQ.baseChange ℝ (coefficients P (Finsupp.single i 1)))) =
        fun i => coefficients P (Finsupp.single i 1) := by
    funext i
    exact F.realLayerOneLieSection_of_grade e ω hF _ (hgrade _)
  rw [hcoeff]
  exact (homogeneous_one_eq_linearPolynomial P hP).symm

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def layerOneGradedMap : (L ⧸ F.layer 2) →ₗ[ℚ] F.AssociatedGraded :=
  (F.gradedPieceProjection e ω hF 1).comp
    (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2))

theorem layerOneGradedMap_mk (x : L) :
    F.layerOneGradedMap e ω hF ((F.layer 2).mkQ x) = F.gradedPieceProjection e ω hF 1 x := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  change (F.associatedGradedBasis e ω hF).repr
    (F.gradedPieceProjection e ω hF 1
      (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2) ((F.layer 2).mkQ x))) i = _
  rw [F.gradedPieceProjection_coordinate, F.gradedPieceProjection_coordinate]
  by_cases hi : ω i = 1
  · rw [ite_eq_left hi, ite_eq_left hi]
    have hni : ¬2 ≤ ω i := by omega
    exact (supportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) ((F.layer 2).mkQ x) ⟨i, hni⟩).trans
        (supportedQuotientBasis_repr_mk e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x ⟨i, hni⟩)
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem realLayerOneGradedMap_mk (x : ℝ ⊗[ℚ] L) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ x) =
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, F.layerOneGradedMap_mk]

theorem realLayerOneGradedMap_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ x =
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ (F.realLayerOneLieSection e ω hF x) := by
  change ((F.gradedPieceProjection e ω hF 1).comp
    (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2))).baseChange ℝ x = _
  rw [LinearMap.baseChange_comp]
  rfl

noncomputable def layerOneGradedSubmodule (U : LieSubalgebra ℚ F.AssociatedGraded) :
    Submodule ℚ (L ⧸ F.layer 2) :=
  U.toSubmodule.comap (F.layerOneGradedMap e ω hF)

theorem mem_realLayerOneGradedSubmodule (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    x ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ↔
      (F.layerOneGradedMap e ω hF).baseChange ℝ x ∈ realificationLieSubalgebra U := by
  rw [layerOneGradedSubmodule, realification_comap]
  rfl

theorem mem_realLayerOneGradedSubmodule_mk (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] L) :
    (F.layer 2).mkQ.baseChange ℝ x ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ↔
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ x ∈ realificationLieSubalgebra U := by
  rw [F.mem_realLayerOneGradedSubmodule, F.realLayerOneGradedMap_mk]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem realLayerOneCorrection_mem_pointwise (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    F.realExtendedSymbolMap (fun _ => 1) (F.realLayerOneCorrection e ω hF a).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1) U _).mpr
  intro α
  rw [← F.realSymbolOfPolynomial_realAdaptedPolynomialMap e ω hF,
    F.realGradedSymbolPolynomial_coefficient_of_polynomial,
    F.realLayerOneCorrection_log]
  by_cases hα : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := hα
    rw [coefficients_linearPolynomial_single]
    simp only [Finsupp.weight_single, one_smul]
    rw [← F.realLayerOneGradedMap_section]
    exact (F.mem_realLayerOneGradedSubmodule e ω hF U (a i)).mp (ha i)
  · rw [coefficients_linearPolynomial_of_ne _ α (by simpa only [not_exists] using hα), map_zero]
    exact (realificationLieSubalgebra U).zero_mem

omit [Fintype σ] in
theorem pointwise_horizontal_coefficient_mem
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.realExtendedSymbolMap (fun _ => 1) x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U)) (i : σ) :
    (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1)) ∈
        (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ := by
  apply (F.mem_realLayerOneGradedSubmodule_mk e ω hF U _).mpr
  have h := (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1) U _).mp hx
    (Finsupp.single i 1)
  rw [← F.realSymbolOfPolynomial_realAdaptedPolynomialMap e ω hF,
    F.realGradedSymbolPolynomial_coefficient_of_polynomial] at h
  simpa only [Finsupp.weight_single, one_smul] using h

theorem pointwise_horizontal_derivative_mem [DecidableEq σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.realExtendedSymbolMap (fun _ => 1) x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U))
    (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) (i : σ) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) ∈
        (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ := by
  rw [F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i x hzero]
  exact F.pointwise_horizontal_coefficient_mem e ω hF U x hx i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

noncomputable def realFastCoefficientDirectionMap
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] F.RealFastCoefficientModule (fun _ => 1) (fun _ => Nat.zero_lt_one) U :=
  (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ.comp
      (F.realFirstCoefficientDirectionMap g.coord)

variable {ι : Type*} (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFastCoefficientDirectionMap_mul
    (g h : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ) :
    F.realFastCoefficientDirectionMap U (g * h).val v =
      F.realFastCoefficientDirectionMap U g.val v +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g
          (F.realFastCoefficientDirectionMap U h.val v) := by
  change (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
      (F.realFirstCoefficientDirectionMap (g.val * h.val).coord v) = _
  rw [F.realFirstCoefficientDirectionMap_mul e ω hF, map_add]
  rfl

theorem realFastCoefficientDirectionMap_triple
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ) :
    F.realFastCoefficientDirectionMap U (a * b * c).val v =
      F.realFastCoefficientDirectionMap U a.val v +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a
          (F.realFastCoefficientDirectionMap U b.val v) +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a
          (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b
            (F.realFastCoefficientDirectionMap U c.val v)) := by
  exact linear_cocycle_triple (F.realFastCoefficientAction (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) U)
    (fun g => F.realFastCoefficientDirectionMap U g.val v)
    (fun g h => F.realFastCoefficientDirectionMap_mul U e ω hF g h v) a b c

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFastCoefficient_remove_derivative
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ)
    (small rational z : F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (hsystem : F.realFastCoefficientDirectionMap U (a * b * c).val v = small +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U (a * b * c) rational + z) :
    F.realFastCoefficientDirectionMap U b.val v =
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm
        (small - F.realFastCoefficientDirectionMap U a.val v) +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b
        (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c rational -
          F.realFastCoefficientDirectionMap U c.val v) +
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm z := by
  let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
  apply linear_derivative_remove (ρ a) (ρ c) (ρ (a * b * c)) (ρ b)
    (linear_action_triple ρ a b c)
    _ _ _ _ small rational z
    (F.realFastCoefficientDirectionMap_triple U e ω hF a b c v) hsystem

omit e ω hF [Fintype σ] in
theorem realFastCoefficient_remove_lifts {K : Type*} [AddCommGroup K] [Module ℝ K]
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (S R : K →ₗ[ℝ] F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (hSR : S = (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U (a * b * c)).toLinearMap.comp R) :
    (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm.toLinearMap.comp S =
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b).toLinearMap.comp
        ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c).toLinearMap.comp R) := by
  let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
  exact linear_lift_remove (ρ a) (ρ c) (ρ (a * b * c)) (ρ b)
    (linear_action_triple ρ a b c) S R hSR

omit [Fintype σ] in
theorem realFastCoefficient_remove_horizontal_lifts {K : Type*}
    [AddCommGroup K] [Module ℝ K]
    (a c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (S R : K →ₗ[ℝ] F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (I : K →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (hS : (F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).comp S = I)
    (hR : (F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).comp R = I) :
    let P := F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    P.comp ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm.toLinearMap.comp S) = I ∧
      P.comp ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c).toLinearMap.comp R) = I := by
  exact horizontal_lift_remove _ _ _
    (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) U e ω hF a)
    (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) U e ω hF c) S R I hS hR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def realPointwisePolynomialSubgroup : Subgroup (F.RealAdaptedPolynomialGroup w) :=
  (show Subgroup (F.RealPolynomialSymbolGroup w) from
    realLieSubgroup (realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U))).comap
      ((F.realPolynomialSymbolHom e ω hF w).comp (F.realAdaptedPolynomialGroupHom w))

theorem mem_realPointwisePolynomialSubgroup (g : F.RealAdaptedPolynomialGroup w) :
    g ∈ F.realPointwisePolynomialSubgroup e ω hF w U ↔
      F.realExtendedSymbolMap w g.coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U) := by
  change F.realSymbolOfPolynomial e ω hF w (F.realAdaptedPolynomialMap w g.coord) ∈
    realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U) ↔ _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

omit w in
theorem realLayerOneCorrection_mem_pointwiseSubgroup [Fintype σ]
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    F.realLayerOneCorrection e ω hF a ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U := by
  apply (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U _).mpr
  exact F.realLayerOneCorrection_mem_pointwise e ω hF U a ha

end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem adaptedReducedRealSymbolHom_coord (g : F.RealAdaptedPolynomialGroup w) :
    (F.adaptedReducedRealSymbolHom w g).coord =
      (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w g.coord) := by
  change ((F.quotientTopSymbolMap w).toLinearMap.comp
    (F.polynomialSymbolMap w).toLinearMap).baseChange ℝ g.coord = _
  rw [LinearMap.baseChange_comp]
  rfl

theorem realPointwisePolynomialSubgroup_le_fast
    (hU : (F.symbolPointwiseSubalgebra e ω hF w U).map (F.quotientTopSymbolMap w) ≤
      F.reducedSquareFastDiagonalSubalgebra w W) :
    F.realPointwisePolynomialSubgroup e ω hF w U ≤ F.realFastDiagonalSubgroup w W := by
  intro g hg
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF w U g).mp hg
  apply (F.mem_realFastDiagonalSubgroup w W g).mpr
  rw [F.adaptedReducedRealSymbolHom_coord]
  have hm : (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ
      (F.realExtendedSymbolMap w g.coord) ∈
      ((F.symbolPointwiseSubalgebra e ω hF w U).toSubmodule.map
        (F.quotientTopSymbolMap w).toLinearMap).baseChange ℝ := by
    rw [realification_map]
    exact ⟨_, hs, rfl⟩
  exact Submodule.baseChange_mono ℝ hU hm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

theorem realAdaptedCoefficientBound_inv {σ ι L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealAdaptedPolynomialGroup w)
    (hg : F.RealAdaptedCoefficientBound e ω hF w T M g.coord) :
    F.RealAdaptedCoefficientBound e ω hF w T M (g⁻¹).coord := by
  simpa only [RealAdaptedCoefficientBound, coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hg

theorem realFastCoefficientAction_symm {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.realFastDiagonalSubgroup w U) (x : F.RealFastCoefficientModule w hw U) :
    (F.realFastCoefficientAction w hw U g).symm x = F.realFastCoefficientAction w hw U g⁻¹ x :=
  congrArg (fun A : F.RealFastCoefficientModule w hw U ≃ₗ[ℝ] F.RealFastCoefficientModule w hw U => A x)
    (map_inv (F.realFastCoefficientAction w hw U) g).symm

theorem fastCoefficientAdjoint_norm_bound {σ ι κ L : Type*}
    [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (b : Basis κ ℝ (F.RealFastCoefficientModule w hw U))
    (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw
      (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y)
    (rows : κ → FirstCoefficientIndex w ω) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (Cproj Clift D : ℝ) (hCproj : 0 ≤ Cproj) (hClift : 0 ≤ Clift) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      ∀ i, |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
        (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
          Cproj * M / monomialScale T (rows i).val.1)
    (hlift : ∀ M, 0 ≤ M → ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (Clift * M) (R y))
    (g : F.realFastDiagonalSubgroup w U)
    (had : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      F.FirstCoefficientSlowBound e ω hF w T (D * M) (F.realFirstCoefficientAdjoint w g.val x))
    (x : F.RealFastCoefficientModule w hw U) :
    ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
        (F.realFastCoefficientAction w hw U g x)‖ ≤
      (Cproj * D * Clift) * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖ := by
  apply basisWeightedCoordinates_operator_bound b (fun i => monomialScale T (rows i).val.1)
    (fun i => monomialScale_pos T hT _) (F.realFastCoefficientAction w hw U g).toLinearMap
    (Cproj * D * Clift) (mul_nonneg (mul_nonneg hCproj hD) hClift)
  intro M hM y hy
  exact F.fastCoefficientAdjoint_weighted_bound e ω hF w hw U b R hR rows T
    Cproj Clift D hClift hD hproj hlift g had hM y hy

theorem fastCoefficientDirection_norm_bound {σ ι κ L : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (Cproj D : ℝ) (hCproj : 0 ≤ Cproj) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
      ∀ j, |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) j| ≤
          Cproj * M / monomialScale T (rows j).val.1)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hg : ∀ i, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (D / T i)
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1))) (i : σ) :
    ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1)
        (F.realFastCoefficientDirectionMap U g (Pi.single i 1))‖ ≤ Cproj * D / T i := by
  apply (basisWeightedCoordinates_norm_le_iff b (fun j => monomialScale T (rows j).val.1)
    (fun j => monomialScale_pos T hT _) (div_nonneg (mul_nonneg hCproj hD) (hT i).le) _).mpr
  intro j
  have h := hproj (D / T i) (div_nonneg hD (hT i).le) _ (hg i) j
  change |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1))) j| ≤ _
  simpa only [mul_div_assoc] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
    (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)

noncomputable def realFastLayerOneCorrection (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) : 𝓖 :=
  ⟨F.realLayerOneCorrection e ω hF a,
    F.realPointwisePolynomialSubgroup_le_fast e ω hF (fun _ => 1) U W hU
      (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U a ha)⟩

theorem realFastLayerOneCorrection_horizontal [DecidableEq σ] (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) (i : σ) :
    𝓟 (F.realFastCoefficientDirectionMap W
      (F.realFastLayerOneCorrection e ω hF U W hU a ha).val (Pi.single i 1)) = a i := by
  change F.realFirstCoefficientHorizontal (fun _ => 1)
    (F.realFirstCoefficientDirectionMap (F.realLayerOneCorrection e ω hF a).coord (Pi.single i 1)) = _
  exact F.realLayerOneCorrection_horizontal_derivative e ω hF a i

theorem realFastLayerOneCorrection_slow [Fintype ι]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M) (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hbound : ∀ i, ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (a i)‖ ≤ M / T i) :
    F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M
      (F.realFastLayerOneCorrection e ω hF U W hU a ha).val.coord :=
  F.realLayerOneCorrection_slow e ω hF T hT hM a hbound

theorem realFastLayerOneCorrection_grid (l : ℕ) (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hgrid : (fun z : σ × LayerOneBasisIndex ω =>
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid l) :
    F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l
      (F.realFastLayerOneCorrection e ω hF U W hU a ha).val.coord :=
  F.realLayerOneCorrection_grid e ω hF l a hgrid

include hU in
theorem realFast_horizontal_normalization [DecidableEq σ]
    (B : 𝓖) (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔)
    (hSR : S = (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W B).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap W B.val (Pi.single i 1) = small i +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W B (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hrational : ∀ i, 𝓟 (rational i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hk : ∀ i, (k i).val ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    ∃ a B' c : 𝓖,
      a.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (small i)) ∧
      c.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (rational i)) ∧
      (B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
        B'.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U) ∧
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) 0 =
        coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 ∧
      (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 = 0 →
        ∀ i, (F.layer 2).mkQ.baseChange ℝ
          (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      let ρ := F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W
      let Y := fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W g.val (Pi.single i 1)
      let S' := (ρ a).symm.toLinearMap.comp S
      let R' := (ρ c).toLinearMap.comp R
      let small' := fun i => (ρ a).symm (small i - Y a i)
      let rational' := fun i => ρ c (rational i) - Y c i
      a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp R' ∧
        (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
        ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k i) ∧
          𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧ 𝓟 (Y B' i) = (k i).val ∧
          𝓟 (Y B' i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ⊓ K := by
  let a := F.realFastLayerOneCorrection e ω hF U W hU (fun i => 𝓟 (small i)) hsmall
  let c := F.realFastLayerOneCorrection e ω hF U W hU (fun i => 𝓟 (rational i)) hrational
  let ρ := F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W
  let Y := fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W g.val (Pi.single i 1)
  have hdata := cocycle_horizontal_normalization ρ Y
    (fun g h i => F.realFastCoefficientDirectionMap_mul W e ω hF g h (Pi.single i 1))
    𝓟 (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) W e ω hF)
    ((F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) K B a c S R hSR hS hR small rational k hsystem
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hsmall i)
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hrational i) hk
  have hpointwise : B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
      (a⁻¹ * B * c⁻¹).val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U := by
    intro hB
    let G := F.realPointwisePolynomialSubgroup e ω hF (fun _ : σ => 1) U
    exact G.mul_mem (G.mul_mem (G.inv_mem
      (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hsmall)) hB)
        (G.inv_mem (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hrational))
  have hzeroa : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) a.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hzeroc : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) c.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hconst := F.realAdapted_factor_middle_constant (fun _ => 1) B.val a.val
    (a⁻¹ * B * c⁻¹).val c.val (congrArg Subtype.val hdata.1) hzeroa hzeroc
  have hlinear : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 = 0 →
      ∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
          (Finsupp.single i 1)) = (k i).val := by
    intro hz i
    have hd := F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i
      (a⁻¹ * B * c⁻¹).val.coord (hconst.trans hz)
    have he : 𝓟 (Y (a⁻¹ * B * c⁻¹) i) = (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
          (Finsupp.single i 1)) := hd
    exact he.symm.trans (hdata.2.2.2.2 i).2.2.2.1
  exact ⟨a, a⁻¹ * B * c⁻¹, c, rfl, rfl, hpointwise, hconst, hlinear, hdata⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF U)
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W (Subtype.val g) (Pi.single i 1))

theorem realFast_bounded_horizontal_normalization
    (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
      (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ 𝓤) (hrational : ∀ i, 𝓟 (rational i) ∈ 𝓤)
    (hk : ∀ i, (k i).val ∈ 𝓤)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, ‖cH (𝓟 (small i))‖ ≤ M / T i)
    (l : ℕ) (hgrid : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l) :
    ∃ a g' q : 𝓖,
      a.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (small i)) ∧
      q.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (rational i)) ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l q.val.coord ∧
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) 0 = 0 ∧
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      let S' := (ρ a).symm.toLinearMap.comp S
      let R' := (ρ q).toLinearMap.comp R
      let small' := fun i => (ρ a).symm (small i - Y a i)
      let rational' := fun i => ρ q (rational i) - Y q i
      a * g' * q = g ∧ S' = (ρ g').toLinearMap.comp R' ∧
        (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
        ∀ i, Y g' i = small' i + ρ g' (rational' i) + S' (k i) ∧
          𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧ 𝓟 (Y g' i) = (k i).val ∧
          𝓟 (Y g' i) ∈ 𝓤 ⊓ K := by
  classical
  have h := F.realFast_horizontal_normalization (σ := σ) (ι := ι) e ω hF U W hU
    g K S R hSR hS hR small rational k hsystem hsmall hrational hk
  obtain ⟨a, g', q, ha, hq, _, hconst, hlinear, hnew⟩ := h
  refine ⟨a, g', q, ha, hq, ?_, ?_, hconst.trans hzero, hlinear hzero, hnew⟩
  · rw [ha]
    exact F.realLayerOneCorrection_slow e ω hF T hT hM (fun i => 𝓟 (small i)) hbound
  · rw [hq]
    apply F.realLayerOneCorrection_grid e ω hF
    choose z hz using hgrid
    refine ⟨fun x => z x.1 x.2, ?_⟩
    funext x
    exact congrFun (hz x.1) x.2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF U)
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W (Subtype.val g) (Pi.single i 1))

theorem realFast_controlled_horizontal_factorization
    (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
      (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)
    (g₀ : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g₀.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g₀).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g₀ i = small i + ρ g₀ (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ 𝓤) (hrational : ∀ i, 𝓟 (rational i) ∈ 𝓤)
    (hk : ∀ i, (k i).val ∈ 𝓤)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, ‖cH (𝓟 (small i))‖ ≤ M / T i)
    (l : ℕ) (hgrid : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l) :
    ∃ a g c : 𝓖, a * g * c = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l c.val.coord ∧
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      (∀ i, 𝓟 (Y a i) = 𝓟 (small i)) ∧ (∀ i, 𝓟 (Y c i) = 𝓟 (rational i)) := by
  have hnorm := F.realFast_bounded_horizontal_normalization e ω hF U W hU
    g₀ hzero K S R hSR hS hR small rational k hsystem hsmall hrational hk T hT M hM hbound l hgrid
  obtain ⟨a, g, c, ha, hc, habound, hcgrid, _, hlinear, hnew⟩ := hnorm
  refine ⟨a, g, c, hnew.1, habound, hcgrid, hlinear, ?_, ?_⟩
  · intro i
    change F.realFirstCoefficientHorizontal (fun _ : σ => 1)
      (F.realFirstCoefficientDirectionMap a.val.coord (Pi.single i 1)) = _
    rw [ha]
    exact F.realLayerOneCorrection_horizontal_derivative e ω hF (fun j => 𝓟 (small j)) i
  · intro i
    change F.realFirstCoefficientHorizontal (fun _ : σ => 1)
      (F.realFirstCoefficientDirectionMap c.val.coord (Pi.single i 1)) = _
    rw [hc]
    exact F.realLayerOneCorrection_horizontal_derivative e ω hF (fun j => 𝓟 (rational j)) i

end Erdos3.NilpotentLieFiltration

end

end OAI
