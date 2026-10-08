/- Modified for ProveIt: import Lean 4.32 compatibility declarations and use
MvPolynomial.coeff_zero explicitly in the zero-coordinate simplifications.
The theorem statements are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.MajorTranslationJointLower
import OAI.Combinatorics.Progressions.Estimates.MajorTranslationPureFactorValues
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationRealPureFactors
import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_sub_degree_top_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A -
      majorTranslationJointPolynomial
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) A ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  rw [← majorTranslationJointPolynomial_sub]
  exact majorTranslationJointPolynomial_lower w
    (weightedTopPart_remainder_lt (Sum.elim (fun _ : U => 1) w) hD) A hA

theorem majorTranslationJointPolynomial_degree_weightedHomogeneousComponent (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (majorTranslationJointPolynomial D A) =
      majorTranslationJointPolynomial
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (majorTranslationTopCoordinates w A) := by
  have hlower := majorTranslationJointPolynomial_sub_degree_top_lower w hD A hA
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (majorTranslationJointPolynomial D A -
        majorTranslationJointPolynomial
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) A) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero]
  exact majorTranslationJointPolynomial_weightedHomogeneousComponent w
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _) A hA

theorem majorTranslationJointPolynomial_degree_slot_top (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) (α : B →₀ ℕ) :
    weightedHomogeneousComponent (fun _ : U => 1) (d - Finsupp.weight w α)
        (polynomialSlotCoefficient α (majorTranslationJointPolynomial D A)) =
      polynomialSlotCoefficient α
        (majorTranslationJointPolynomial
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
          (majorTranslationTopCoordinates w A)) := by
  rw [polynomialSlotCoefficient_weightedHomogeneousComponent (fun _ : U => 1) w
    (majorTranslationJointPolynomial_degree w hD A hA),
    majorTranslationJointPolynomial_degree_weightedHomogeneousComponent w hD A hA]

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem ofCoordinates_mem_gradedPolynomialSubmodule
    {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [IsScalarTower ℚ ℝ L] (b : Basis ι ℝ L) (ω : ι → ℕ) (v : σ → ℕ)
    (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous v (ω i)) :
    ofCoordinates (R := ℚ) b P ∈ gradedPolynomialSubmodule b ω v := by
  classical
  intro α
  change basisGradeProjection b ω (Finsupp.weight v α)
    (coefficients (ofCoordinates (R := ℚ) b P) α) = _
  apply b.repr.injective
  ext i
  have hc : b.repr (coefficients (ofCoordinates (R := ℚ) b P) α) i =
      (P i).coeff α := by
    change (b.coord i).toAddMonoidHom (coefficients (ofCoordinates (R := ℚ) b P) α) = _
    rw [← coeff_coordinate, coordinate_ofCoordinates]
  rw [basisGradeProjection_repr, hc]
  by_cases hi : ω i = Finsupp.weight v α
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, (hP i).coeff_eq_zero α (Ne.symm hi)]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realSymbolRepresentative_of_gradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    F.realSymbolRepresentative b ω hlayers v (F.realSymbolOfPolynomial b ω hlayers v P) = P := by
  apply coefficients.injective
  ext α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight v α = ω i
  · rw [F.realSymbolRepresentative_coefficient b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v P) ⟨(α, i), h⟩]
    exact F.realSymbolOfPolynomial_coordinate b ω hlayers v P ⟨(α, i), h⟩
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers v _ α i h]
    have hi := congrArg (fun x => (b.baseChange ℝ).repr x i) (hP α)
    simp only [LinearMap.restrictScalars_apply] at hi
    rw [basisGradeProjection_repr, ite_eq_right (Ne.symm h)] at hi
    exact hi

theorem realSymbolRepresentative_polynomialOrbit
    (p : F.realification.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    F.realSymbolRepresentative b ω hlayers v
      ((F.realPolynomialSymbolHom b ω hlayers v
        (F.realification.polynomialOrbitCoordinates v p)).coord) = p.log := by
  rw [F.realPolynomialSymbolHom_coord, F.realPolynomialSymbolMap_apply,
    F.realification.polynomialOrbitCoordinates_log]
  exact F.realSymbolRepresentative_of_gradedPolynomial b ω hlayers v p.log hp

theorem realCoordinatePolynomialOrbit_log_mem_graded [Fintype ι]
    (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))
    (hhom : ∀ i, (P i).IsWeightedHomogeneous v (ω i)) :
    (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log ∈
      gradedPolynomialSubmodule (b.baseChange ℝ) ω v := by
  rw [F.realCoordinatePolynomialOrbit_log]
  exact ofCoordinates_mem_gradedPolynomialSubmodule (b.baseChange ℝ) ω v P hhom

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem exists_translation_coordinate_polynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d) :
    ∃ p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
            (fun _ : U => 1) u p) =
          ⟨fun i => eval u (A i), specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let F := weightedFiltration w d hwd
  let b := weightedBasis w d hw
  let ω := weightedBasisGrade w d
  have hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}) :=
    weightedFiltration_layer_eq_span w d hw hwd
  let Acoord : WeightedBasisIndex w d → MvPolynomial U ℝ := Sum.elim A (fun _ => 0)
  let Pcoord : WeightedBasisIndex w d → MvPolynomial U ℝ :=
    Sum.elim (fun _ => 0) (fun α => polynomialSlotCoefficient α.val P)
  have hAcoord : ∀ i, Acoord i ∈ weightedSupportLE (fun _ : U => 1) (ω i) := by
    intro i
    cases i with
    | inl i => exact (mem_weightedSupportLE_one_iff _ _).mpr (hA i)
    | inr α => exact Submodule.zero_mem _
  have hPcoord : ∀ i, Pcoord i ∈ weightedSupportLE (fun _ : U => 1) (ω i) := by
    intro i
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr α => exact polynomialSlotCoefficient_degree (fun _ : U => 1) w hP α.val
  let a := F.realCoordinatePolynomialOrbit b ω hlayers (fun _ : U => 1) Acoord hAcoord
  let q := F.realCoordinatePolynomialOrbit b ω hlayers (fun _ : U => 1) Pcoord hPcoord
  have ha (u : U → ℝ) : bchRealTranslationHom w d hwd
      (F.realification.polynomialOrbitRealEval (fun _ : U => 1) u a) =
        ⟨fun i => eval u (A i), 0⟩ := by
    let g := F.realification.polynomialOrbitRealEval (fun _ : U => 1) u a
    have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord
      (fun i => eval u (A i)) (0 : weightedSupportLT (R := ℝ) w d) ?_ ?_
    · exact bchRealTranslationHom_pure_base_of_shape w d hwd g.coord _ hs.1
        (by simpa only [ZeroMemClass.coe_zero, map_zero] using hs.2)
    · intro i
      exact F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Acoord hAcoord u (Sum.inl i)
    · intro α
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Acoord hAcoord u (Sum.inr α)
      simpa only [Acoord, Sum.elim_inr, map_zero, ZeroMemClass.coe_zero,
        MvPolynomial.coeff_zero] using h
  have hq (u : U → ℝ) : bchRealTranslationHom w d hwd
      (F.realification.polynomialOrbitRealEval (fun _ : U => 1) u q) =
        ⟨0, specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
    let g := F.realification.polynomialOrbitRealEval (fun _ : U => 1) u q
    let Pu : weightedSupportLT (R := ℝ) w d :=
      ⟨specializeMajorParameters (RingHom.id ℝ) P u, hPslot u⟩
    have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord 0 Pu ?_ ?_
    · exact bchRealTranslationHom_pure_polynomial_of_shape w d hwd g.coord Pu.val
        (fun i => by simpa only [Pi.zero_apply, map_zero] using hs.1 i) hs.2
    · intro i
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Pcoord hPcoord u (Sum.inl i)
      simpa only [Pcoord, Sum.elim_inl, map_zero, Pi.zero_apply] using h
    · intro α
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Pcoord hPcoord u (Sum.inr α)
      change (b.baseChange ℝ).repr g.coord (Sum.inr α) = eval u (polynomialSlotCoefficient α.val P) at h
      rw [h]
      simpa only [MvPolynomial.aeval_eq_eval, Pu, specializeMajorParameters,
        RingHom.comp_id, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
        Algebra.algebraMap_self, MvPolynomial.eval₂_id, MvPolynomial.coe_eval₂Hom] using
        polynomialSlotCoefficient_eval u α.val P
  refine ⟨a * q, fun u => ?_⟩
  rw [map_mul, map_mul, ha, hq]
  apply PolynomialTranslationGroupOver.ext <;> simp

theorem exists_majorTranslation_polynomialOrbit_of_degree
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    ∃ p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
            (fun _ : U => 1) u p) =
          algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) A u := by
  obtain ⟨p, hp⟩ := exists_translation_coordinate_polynomialOrbit w d hw hwd A hA
    (majorTranslationJointPolynomial D A)
    (majorTranslationJointPolynomial_degree w hD A hA)
    (majorTranslationJointPolynomial_specialize_lower w hw hD A)
  refine ⟨p, fun u => ?_⟩
  rw [hp u, majorTranslationJointPolynomial_specialize]
  rfl

theorem exists_majorTranslation_polynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    ∃ p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
            (fun _ : U => 1) u p) =
          algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) A u :=
  exists_majorTranslation_polynomialOrbit_of_degree w d hw hwd D
    (fun _ hα => (hD (mem_support_iff.mp hα)).le) A hA

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {U B : Type*}

noncomputable def translationBaseCoordinatePolynomial
    (w : B → ℕ) (d : ℕ) (A : B → MvPolynomial U ℝ) :
    WeightedBasisIndex w d → MvPolynomial U ℝ :=
  Sum.elim A (fun _ => 0)

noncomputable def translationPolynomialCoordinatePolynomial
    (w : B → ℕ) (d : ℕ) (P : MvPolynomial (U ⊕ B) ℝ) :
    WeightedBasisIndex w d → MvPolynomial U ℝ :=
  Sum.elim (fun _ => 0) (fun α => polynomialSlotCoefficient α.val P)

theorem translationBaseCoordinatePolynomial_adapted
    (w : B → ℕ) (d : ℕ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ i, (A i).totalDegree ≤ w i) (i : WeightedBasisIndex w d) :
    translationBaseCoordinatePolynomial w d A i ∈
      weightedSupportLE (fun _ : U => 1) (weightedBasisGrade w d i) := by
  cases i with
  | inl i => exact (mem_weightedSupportLE_one_iff _ _).mpr (hA i)
  | inr α => exact Submodule.zero_mem _

theorem translationPolynomialCoordinatePolynomial_adapted
    (w : B → ℕ) (d : ℕ) (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (i : WeightedBasisIndex w d) :
    translationPolynomialCoordinatePolynomial w d P i ∈
      weightedSupportLE (fun _ : U => 1) (weightedBasisGrade w d i) := by
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr α => exact polynomialSlotCoefficient_degree (fun _ : U => 1) w hP α.val

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def translationBasePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) := by
  letI := weightedBasisIndex_finite w d hw
  letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA)

noncomputable def translationPurePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) := by
  letI := weightedBasisIndex_finite w d hw
  letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP)

noncomputable def translationCoordinatePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  translationBasePolynomialOrbit w d hw hwd A hA *
    translationPurePolynomialOrbit w d hw hwd P hP

@[simp] theorem translationBasePolynomialOrbit_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    letI := weightedBasisIndex_finite w d hw
    letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
    (translationBasePolynomialOrbit w d hw hwd A hA).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis w d hw).baseChange ℝ)
        (translationBaseCoordinatePolynomial w d A) := rfl

@[simp] theorem translationPurePolynomialOrbit_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    letI := weightedBasisIndex_finite w d hw
    letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
    (translationPurePolynomialOrbit w d hw hwd P hP).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis w d hw).baseChange ℝ)
        (translationPolynomialCoordinatePolynomial w d P) := rfl

@[simp] theorem translationBasePolynomialOrbit_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (i : WeightedBasisIndex w d) :
    VectorPolynomial.coordinate (((weightedBasis w d hw).baseChange ℝ).coord i).toAddMonoidHom
      (translationBasePolynomialOrbit w d hw hwd A hA).log =
        translationBaseCoordinatePolynomial w d A i := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_coordinate
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA) i

@[simp] theorem translationPurePolynomialOrbit_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (i : WeightedBasisIndex w d) :
    VectorPolynomial.coordinate (((weightedBasis w d hw).baseChange ℝ).coord i).toAddMonoidHom
      (translationPurePolynomialOrbit w d hw hwd P hP).log =
        translationPolynomialCoordinatePolynomial w d P i := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_coordinate
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP) i

theorem translationBasePolynomialOrbit_eval_coordinates
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) (i : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)).coord i =
      eval u (translationBaseCoordinatePolynomial w d A i) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_eval_coordinates
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA) u i

theorem translationPurePolynomialOrbit_eval_coordinates
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (u : U → ℝ) (i : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)).coord i =
      eval u (translationPolynomialCoordinatePolynomial w d P i) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_eval_coordinates
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP) u i

theorem translationBasePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)) =
      ⟨fun i => eval u (A i), 0⟩ := by
  let g := (weightedFiltration w d hwd).realification.polynomialOrbitRealEval
    (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)
  have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord
    (fun i => eval u (A i)) (0 : weightedSupportLT (R := ℝ) w d) ?_ ?_
  · exact bchRealTranslationHom_pure_base_of_shape w d hwd g.coord _ hs.1
      (by simpa only [ZeroMemClass.coe_zero, map_zero] using hs.2)
  · intro i
    exact translationBasePolynomialOrbit_eval_coordinates w d hw hwd A hA u (Sum.inl i)
  · intro α
    simpa only [translationBaseCoordinatePolynomial, Sum.elim_inr, map_zero,
      ZeroMemClass.coe_zero, MvPolynomial.coeff_zero] using
      translationBasePolynomialOrbit_eval_coordinates w d hw hwd A hA u (Sum.inr α)

theorem translationPurePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)) =
      ⟨0, specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  let g := (weightedFiltration w d hwd).realification.polynomialOrbitRealEval
    (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)
  let Pu : weightedSupportLT (R := ℝ) w d :=
    ⟨specializeMajorParameters (RingHom.id ℝ) P u, hPslot u⟩
  have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord 0 Pu ?_ ?_
  · exact bchRealTranslationHom_pure_polynomial_of_shape w d hwd g.coord Pu.val
      (fun i => by simpa only [Pi.zero_apply, map_zero] using hs.1 i) hs.2
  · intro i
    simpa only [translationPolynomialCoordinatePolynomial, Sum.elim_inl, map_zero,
      Pi.zero_apply] using
      translationPurePolynomialOrbit_eval_coordinates w d hw hwd P hP u (Sum.inl i)
  · intro α
    have h := translationPurePolynomialOrbit_eval_coordinates w d hw hwd P hP u (Sum.inr α)
    change ((weightedBasis w d hw).baseChange ℝ).repr g.coord (Sum.inr α) =
      eval u (polynomialSlotCoefficient α.val P) at h
    rw [h]
    simpa only [MvPolynomial.aeval_eq_eval, Pu, specializeMajorParameters,
      RingHom.comp_id, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_self, MvPolynomial.eval₂_id, MvPolynomial.coe_eval₂Hom] using
      polynomialSlotCoefficient_eval u α.val P

theorem translationCoordinatePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationCoordinatePolynomialOrbit w d hw hwd A hA P hP)) =
      ⟨fun i => eval u (A i), specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  rw [translationCoordinatePolynomialOrbit, map_mul, map_mul,
    translationBasePolynomialOrbit_realEval, translationPurePolynomialOrbit_realEval
      w d hw hwd P hP hPslot]
  apply PolynomialTranslationGroupOver.ext <;> simp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module VectorPolynomial
open NilpotentLieFiltration
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def translationPolynomialSymbolHom
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) →*
      (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realPolynomialSymbolHom
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)).comp
      ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
        (fun _ : U => 1)).toMonoidHom

@[simp] theorem translationPolynomialSymbolHom_coord
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1)) :
    (translationPolynomialSymbolHom w d hw hwd p).coord =
      (weightedFiltration w d hwd).realSymbolOfPolynomial
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log := rfl

noncomputable def translationPolynomialSymbolLift
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
    (fun _ : U => 1)).symm
      ((weightedFiltration w d hwd).realPolynomialSymbolLift
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) x)

@[simp] theorem translationPolynomialSymbolLift_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (translationPolynomialSymbolLift w d hw hwd x).log =
      (weightedFiltration w d hwd).realSymbolRepresentative
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) x.coord := rfl

@[simp] theorem translationPolynomialSymbolHom_lift
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolHom w d hw hwd
      (translationPolynomialSymbolLift w d hw hwd x) = x := by
  simp only [translationPolynomialSymbolHom, translationPolynomialSymbolLift,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    realPolynomialSymbolHom_lift]

theorem translationBasePolynomialOrbit_symbol_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolHom w d hw hwd
      (translationBasePolynomialOrbit w d hw hwd A hA) =
    translationPolynomialSymbolHom w d hw hwd
      (translationBasePolynomialOrbit w d hw hwd (majorTranslationTopCoordinates w A)
        (majorTranslationTopCoordinates_degree w A)) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  have hcoords : (fun i : WeightedBasisIndex w d =>
      weightedHomogeneousComponent (fun _ : U => 1) (weightedBasisGrade w d i)
        (translationBaseCoordinatePolynomial w d A i)) =
      translationBaseCoordinatePolynomial w d (majorTranslationTopCoordinates w A) := by
    funext i
    cases i with
    | inl i => rfl
    | inr α => exact map_zero _
  apply NilpotentLieBCHGroup.ext
  simp only [translationPolynomialSymbolHom_coord, translationBasePolynomialOrbit_log]
  rw [(weightedFiltration w d hwd).realSymbolOfPolynomial_ofCoordinates_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)]
  rw [hcoords]

theorem translationPurePolynomialOrbit_symbol_eq_of_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P Q : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hQ : Q ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (htop : ∀ α : B →₀ ℕ,
      weightedHomogeneousComponent (fun _ : U => 1) (d - Finsupp.weight w α)
        (polynomialSlotCoefficient α P) = polynomialSlotCoefficient α Q) :
    translationPolynomialSymbolHom w d hw hwd
      (translationPurePolynomialOrbit w d hw hwd P hP) =
    translationPolynomialSymbolHom w d hw hwd
      (translationPurePolynomialOrbit w d hw hwd Q hQ) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  have hcoords : (fun i : WeightedBasisIndex w d =>
      weightedHomogeneousComponent (fun _ : U => 1) (weightedBasisGrade w d i)
        (translationPolynomialCoordinatePolynomial w d P i)) =
      translationPolynomialCoordinatePolynomial w d Q := by
    funext i
    cases i with
    | inl i => exact map_zero _
    | inr α => exact htop α.val
  apply NilpotentLieBCHGroup.ext
  simp only [translationPolynomialSymbolHom_coord, translationPurePolynomialOrbit_log]
  rw [(weightedFiltration w d hwd).realSymbolOfPolynomial_ofCoordinates_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)]
  rw [hcoords]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def majorTranslationPolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  translationCoordinatePolynomialOrbit w d hw hwd A hA
    (majorTranslationJointPolynomial D A) (majorTranslationJointPolynomial_degree w hD A hA)

theorem majorTranslationPolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)) =
      algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) A u := by
  rw [majorTranslationPolynomialOrbit, translationCoordinatePolynomialOrbit_realEval
    w d hw hwd A hA _ _ (majorTranslationJointPolynomial_specialize_lower w hw hD A),
    majorTranslationJointPolynomial_specialize]
  rfl

theorem majorTranslationPolynomialOrbit_top_log_graded
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) :
    (majorTranslationPolynomialOrbit w d hw hwd D
      (fun _ hα => (hD (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log ∈
      gradedPolynomialSubmodule ((weightedBasis w d hw).baseChange ℝ)
        (weightedBasisGrade w d) (fun _ : U => 1) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  apply (weightedFiltration w d hwd).realPolynomialOrbit_log_mul_mem_graded
    (weightedBasis w d hw) (weightedBasisGrade w d) (fun _ : U => 1)
    (weightedBasis_homogeneous_brackets w d hw)
  · rw [translationBasePolynomialOrbit_log]
    apply ofCoordinates_mem_gradedPolynomialSubmodule
    intro i
    cases i with
    | inl i => exact majorTranslationTopCoordinates_homogeneous w A i
    | inr α => exact isWeightedHomogeneous_zero ℝ _ _
  · rw [translationPurePolynomialOrbit_log]
    apply ofCoordinates_mem_gradedPolynomialSubmodule
    intro i
    cases i with
    | inl i => exact isWeightedHomogeneous_zero ℝ _ _
    | inr α =>
      change (polynomialSlotCoefficient α.val
        (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A))).IsWeightedHomogeneous
          (fun _ : U => 1) (d - Finsupp.weight w α.val)
      have htop := majorTranslationJointPolynomial_top_homogeneous w hD A
      have hle : majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) ∈
          weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
        fun _ hβ => (htop (mem_support_iff.mp hβ)).le
      have he := polynomialSlotCoefficient_weightedHomogeneousComponent
        (fun _ : U => 1) w hle α.val
      rw [htop.weightedHomogeneousComponent_same] at he
      rw [← he]
      exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem majorTranslationPolynomialOrbit_symbol_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D
        (fun _ hα => (hD (mem_support_iff.mp hα)).le) A hA) =
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D
        (fun _ hα => (hD (mem_support_iff.mp hα)).le)
        (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)) := by
  simp only [majorTranslationPolynomialOrbit, translationCoordinatePolynomialOrbit, map_mul]
  rw [translationBasePolynomialOrbit_symbol_top w d hw hwd A hA]
  rw [translationPurePolynomialOrbit_symbol_eq_of_top w d hw hwd
    (majorTranslationJointPolynomial D A)
    (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A))
    (majorTranslationJointPolynomial_degree w
      (fun _ hα => (hD (mem_support_iff.mp hα)).le) A hA)
    (majorTranslationJointPolynomial_degree w
      (fun _ hα => (hD (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A))
    (majorTranslationJointPolynomial_slot_top w hD A hA)]

theorem majorTranslationPolynomialOrbit_symbol_representative
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realSymbolRepresentative
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D
          (fun _ hα => (hD (mem_support_iff.mp hα)).le) A hA)).coord =
    (majorTranslationPolynomialOrbit w d hw hwd D
      (fun _ hα => (hD (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log := by
  rw [majorTranslationPolynomialOrbit_symbol_top w d hw hwd D hD A hA]
  rw [translationPolynomialSymbolHom_coord]
  exact (weightedFiltration w d hwd).realSymbolRepresentative_of_gradedPolynomial
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) _
    (majorTranslationPolynomialOrbit_top_log_graded w d hw hwd D hD A)

theorem majorTranslationPolynomialOrbit_symbolLift_eq
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolLift w d hw hwd
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D
          (fun _ hα => (hD (mem_support_iff.mp hα)).le) A hA)) =
    majorTranslationPolynomialOrbit w d hw hwd D
      (fun _ hα => (hD (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (translationPolynomialSymbolLift w d hw hwd
    (translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D
        (fun _ hα => (hD (mem_support_iff.mp hα)).le) A hA))).log =
    (majorTranslationPolynomialOrbit w d hw hwd D
      (fun _ hα => (hD (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log
  rw [translationPolynomialSymbolLift_log,
    majorTranslationPolynomialOrbit_symbol_representative w d hw hwd D hD A hA]

theorem majorTranslationPolynomialOrbit_symbolLift_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u
        (translationPolynomialSymbolLift w d hw hwd
          (translationPolynomialSymbolHom w d hw hwd
            (majorTranslationPolynomialOrbit w d hw hwd D
              (fun _ hα => (hD (mem_support_iff.mp hα)).le) A hA)))) =
      algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0)
        (majorTranslationTopCoordinates w A) u := by
  rw [majorTranslationPolynomialOrbit_symbolLift_eq w d hw hwd D hD A hA]
  exact majorTranslationPolynomialOrbit_realEval w d hw hwd D _ _ _ u

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

 theorem majorTranslationPolynomialOrbit_symbol_degree_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA) =
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
          (mem_support_iff.mp hα)).le)
        (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)) := by
  simp only [majorTranslationPolynomialOrbit, translationCoordinatePolynomialOrbit, map_mul]
  rw [translationBasePolynomialOrbit_symbol_top w d hw hwd A hA]
  rw [translationPurePolynomialOrbit_symbol_eq_of_top w d hw hwd
    (majorTranslationJointPolynomial D A)
    (majorTranslationJointPolynomial
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (majorTranslationTopCoordinates w A))
    (majorTranslationJointPolynomial_degree w hD A hA)
    (majorTranslationJointPolynomial_degree w
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A))
    (majorTranslationJointPolynomial_degree_slot_top w hD A hA)]

 theorem majorTranslationPolynomialOrbit_degree_symbol_representative
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realSymbolRepresentative
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)).coord =
    (majorTranslationPolynomialOrbit w d hw hwd
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log := by
  rw [majorTranslationPolynomialOrbit_symbol_degree_top w d hw hwd D hD A hA,
    translationPolynomialSymbolHom_coord]
  exact (weightedFiltration w d hwd).realSymbolRepresentative_of_gradedPolynomial
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) _
    (majorTranslationPolynomialOrbit_top_log_graded w d hw hwd _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) A)

 theorem majorTranslationPolynomialOrbit_degree_symbolLift_eq
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolLift w d hw hwd
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)) =
    majorTranslationPolynomialOrbit w d hw hwd
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (translationPolynomialSymbolLift w d hw hwd
    (translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA))).log = _
  rw [translationPolynomialSymbolLift_log,
    majorTranslationPolynomialOrbit_degree_symbol_representative w d hw hwd D hD A hA]
  rfl

 theorem majorTranslationPolynomialOrbit_degree_symbolLift_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u
        (translationPolynomialSymbolLift w d hw hwd
          (translationPolynomialSymbolHom w d hw hwd
            (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)))) =
      algebraicMajorSymbol
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (specializeMajorParameters (RingHom.id ℝ)
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) 0)
        (majorTranslationTopCoordinates w A) u := by
  rw [majorTranslationPolynomialOrbit_degree_symbolLift_eq w d hw hwd D hD A hA]
  exact majorTranslationPolynomialOrbit_realEval w d hw hwd _ _ _ _ u

end Erdos3.PolynomialTranslationLie

end

end OAI
