/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def constantDirection : PolynomialTranslationLie σ := ⟨0, 1⟩

noncomputable def topProjection (w : σ → ℕ) (d : ℕ) :
    PolynomialTranslationLie σ →ₗ[ℚ] PolynomialTranslationLie σ where
  toFun x := ⟨fun i => if w i = d then x.base i else 0, C (x.polynomial.coeff 0)⟩
  map_add' x y := by
    ext i
    · by_cases hi : w i = d <;> simp [hi]
    · simp
  map_smul' r x := by
    ext i
    · by_cases hi : w i = d <;> simp [hi]
    · simp

omit [Fintype σ] in
@[simp] theorem topProjection_base (w : σ → ℕ) (d : ℕ)
    (x : PolynomialTranslationLie σ) (i : σ) :
    (topProjection w d x).base i = if w i = d then x.base i else 0 := rfl

omit [Fintype σ] in
@[simp] theorem topProjection_polynomial (w : σ → ℕ) (d : ℕ)
    (x : PolynomialTranslationLie σ) :
    (topProjection w d x).polynomial = C (x.polynomial.coeff 0) := rfl

omit [Fintype σ] in
theorem topProjection_mem_top (w : σ → ℕ) (d : ℕ) (x : PolynomialTranslationLie σ) :
    topProjection w d x ∈ weightedLayer w d d := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp [Nat.ne_of_lt hi]
  · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

omit [Fintype σ] in
theorem topProjection_pure (w : σ → ℕ) (d : ℕ) (P : MvPolynomial σ ℚ) :
    topProjection w d ⟨0, P⟩ = P.coeff 0 • (constantDirection : PolynomialTranslationLie σ) := by
  apply PolynomialTranslationLie.ext
  · funext i
    simp [constantDirection]
  · simp [constantDirection, MvPolynomial.C_eq_smul_one]

theorem pure_constant_zero_of_top_frequency (w : σ → ℕ) (d : ℕ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : MvPolynomial σ ℚ) (hP : (⟨0, P⟩ : PolynomialTranslationLie σ) ∈ U) :
    P.coeff 0 = 0 := by
  have h := hkill _ (hgraded _ hP) (topProjection_mem_top w d ⟨0, P⟩)
  rw [topProjection_pure, map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right hfrequency

theorem raw_lie_mem (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (x z : σ → ℚ) (P Q : MvPolynomial σ ℚ)
    (hx : (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U)
    (hz : (⟨z,Q⟩ : PolynomialTranslationLie σ) ∈ U) :
    (⟨0, scalarDirectionalDerivative x Q - scalarDirectionalDerivative z P⟩ :
      PolynomialTranslationLie σ) ∈ U :=
  U.lie_mem (x := ⟨x,P⟩) (y := ⟨z,Q⟩) hx hz

noncomputable def relationSpace (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) :
    Submodule ℚ ((σ → ℚ) × MvPolynomial σ ℚ) :=
  U.toSubmodule.comap toProdl.symm.toLinearMap

theorem mem_relationSpace (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    (x,P) ∈ relationSpace U ↔ (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U := Iff.rfl

noncomputable def potentialRelationOfTopFrequency (w : σ → ℕ) (d : ℕ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    Erdos3.PolynomialPotentialRelation σ where
  space := relationSpace U
  bracket_mem := by
    intro x P z Q hx hz
    exact (mem_relationSpace U _ _).mpr (raw_lie_mem U x z P Q
      ((mem_relationSpace U _ _).mp hx) ((mem_relationSpace U _ _).mp hz))
  pure_constant_zero := fun P hP => pure_constant_zero_of_top_frequency w d U hgraded
    frequency hfrequency hkill P ((mem_relationSpace U _ _).mp hP)

@[simp] theorem mem_potentialRelationOfTopFrequency (w : σ → ℕ) (d : ℕ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    (x,P) ∈ (potentialRelationOfTopFrequency w d U hgraded frequency hfrequency hkill).space ↔
      (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U := Iff.rfl

theorem exists_weighted_potential_of_top_frequency [DecidableEq σ]
    (w : σ → ℕ) {d : ℕ} (hd : 0 < d) (hw : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : σ → MvPolynomial σ ℚ)
    (hlift : ∀ i, (⟨Pi.single i 1, P i⟩ : PolynomialTranslationLie σ) ∈ U)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i)) :
    ∃ V : MvPolynomial σ ℚ, V.IsWeightedHomogeneous w d ∧
      ∀ x ∈ U, scalarDirectionalDerivative x.base V = x.polynomial := by
  let A := potentialRelationOfTopFrequency w d U hgraded frequency hfrequency hkill
  have hA : ∀ i, (Pi.single i 1, P i) ∈ A.space := hlift
  obtain ⟨V,hV,h⟩ := A.exists_weighted_potential P hA w hd hw hhom
  exact ⟨V,hV,fun x hx => h x.base x.polynomial hx⟩

theorem exponential_closure_potential_of_top_frequency [DecidableEq σ]
    (w : σ → ℕ) {d : ℕ} (hd : 0 < d) (hw : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : σ → MvPolynomial σ ℚ)
    (hlift : ∀ i, (⟨Pi.single i 1, P i⟩ : PolynomialTranslationLie σ) ∈ U)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i)) :
    ∃ V : MvPolynomial σ ℚ, V.IsWeightedHomogeneous w d ∧
      ∀ g ∈ Subgroup.closure
        ((fun x : U => PolynomialTranslationGroup.exponentialElement
          x.val.base x.val.polynomial) '' Set.univ),
        g.polynomial = V - polynomialTranslate (-g.base) V := by
  obtain ⟨V,hV,h⟩ := exists_weighted_potential_of_top_frequency w hd hw U hgraded
    frequency hfrequency hkill P hlift hhom
  refine ⟨V,hV,fun g hg => PolynomialTranslationGroup.potential_identity_of_mem_closure V ?_ hg⟩
  rintro a ⟨x,_,rfl⟩
  exact ⟨x.val.base, by rw [h x.val x.property]⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module

variable {σ : Type*} [Fintype σ]

noncomputable def weightedCoordinatesEquiv (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) :
    weightedSubalgebra w d ≃ₗ[ℚ] (σ → ℚ) × weightedSupportLT (R := ℚ) w d where
  toFun x := (x.val.base, ⟨x.val.polynomial,
    by simpa only [← weightedSupportDrop_one] using x.property.2⟩)
  invFun x := ⟨⟨x.1, x.2.val⟩, ⟨fun i hi => by have := hw i; omega,
    by simpa only [weightedSupportDrop_one] using x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev WeightedBasisIndex (w : σ → ℕ) (d : ℕ) :=
  σ ⊕ {a : σ →₀ ℕ | Finsupp.weight w a < d}

noncomputable def weightedBasis (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Basis (WeightedBasisIndex w d) ℚ (weightedSubalgebra w d) :=
  ((Pi.basisFun ℚ σ).prod
    (MvPolynomial.basisRestrictSupport ℚ {a : σ →₀ ℕ | Finsupp.weight w a < d})).map
    (weightedCoordinatesEquiv w d hw).symm

noncomputable def weightedBasisGrade (w : σ → ℕ) (d : ℕ) : WeightedBasisIndex w d → ℕ :=
  Sum.elim w (fun a => d - Finsupp.weight w a.val)

@[simp] theorem weightedBasis_repr_inl (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) (i : σ) :
    (weightedBasis w d hw).repr x (Sum.inl i) = x.val.base i := by
  change (Pi.basisFun ℚ σ).repr x.val.base i = _
  simp only [Pi.basisFun_repr]

@[simp] theorem weightedBasis_repr_inr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw).repr x (Sum.inr a) = x.val.polynomial.coeff a.val := by
  rfl

omit [Fintype σ] in
@[simp] theorem weightedBasisGrade_inl (w : σ → ℕ) (d : ℕ) (i : σ) :
    weightedBasisGrade w d (Sum.inl i) = w i := rfl

omit [Fintype σ] in
@[simp] theorem weightedBasisGrade_inr (w : σ → ℕ) (d : ℕ)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    weightedBasisGrade w d (Sum.inr a) = d - Finsupp.weight w a.val := rfl

@[simp] theorem weightedBasis_projection_base (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) (i : σ) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.base i =
      if w i = j then x.val.base i else 0 := by
  simpa only [weightedBasis_repr_inl, weightedBasisGrade_inl] using
    basisGradeProjection_repr (weightedBasis w d hw) (weightedBasisGrade w d) j x (Sum.inl i)

@[simp] theorem weightedBasis_projection_coeff (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.coeff a.val =
      if d - Finsupp.weight w a.val = j then x.val.polynomial.coeff a.val else 0 := by
  simpa only [weightedBasis_repr_inr, weightedBasisGrade_inr] using
    basisGradeProjection_repr (weightedBasis w d hw) (weightedBasisGrade w d) j x (Sum.inr a)

theorem weightedBasis_top_projection_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val.polynomial =
      C (x.val.polynomial.coeff 0) := by
  classical
  let : Finsupp.NonTorsionWeight ℕ w := Finsupp.nonTorsionWeight_of ℕ w (fun i => (hw i).ne')
  apply MvPolynomial.ext
  intro a
  by_cases ha : Finsupp.weight w a < d
  · rw [weightedBasis_projection_coeff w d d hw x ⟨a, ha⟩]
    have he : d - Finsupp.weight w a = d ↔ a = 0 := by
      rw [← Finsupp.weight_eq_zero_iff_eq_zero w]
      omega
    simp only [he]
    by_cases ha0 : a = 0
    · subst a
      simp
    · simp [ha0, Ne.symm ha0]
  · have ha0 : a ≠ 0 := by
      intro h
      subst a
      simp only [map_zero] at ha
      omega
    rw [coeff_C, ite_eq_right (Ne.symm ha0)]
    by_contra hne
    have hh := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).property.2
      (MvPolynomial.mem_support_iff.mpr hne)
    change Finsupp.weight w a + 1 ≤ d at hh
    omega

theorem weightedBasis_top_projection_val (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val =
      ⟨fun i => if w i = d then x.val.base i else 0, C (x.val.polynomial.coeff 0)⟩ := by
  apply PolynomialTranslationLie.ext
  · funext i
    exact weightedBasis_projection_base w d d hw x i
  · exact weightedBasis_top_projection_polynomial w d hw hd x

theorem weightedFiltration_layer_eq_span (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (j : ℕ) :
    (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (weightedBasis w d hw '' {i | j ≤ weightedBasisGrade w d i}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx a ha
    change (∀ i, w i < j → x.val.base i = 0) ∧
      x.val.polynomial ∈ weightedSupportDrop w d j at hx
    cases a with
    | inl i =>
        rw [weightedBasis_repr_inl]
        exact hx.1 i (by change ¬ j ≤ w i at ha; omega)
    | inr a =>
        rw [weightedBasis_repr_inr]
        by_contra hne
        have hh := hx.2 (MvPolynomial.mem_support_iff.mpr hne)
        change Finsupp.weight w a.val + j ≤ d at hh
        change ¬ j ≤ d - Finsupp.weight w a.val at ha
        omega
  · intro hx
    change (∀ i, w i < j → x.val.base i = 0) ∧
      x.val.polynomial ∈ weightedSupportDrop w d j
    constructor
    · intro i hi
      exact (weightedBasis_repr_inl w d hw x i) ▸ hx (Sum.inl i) (by
        change ¬ j ≤ w i
        omega)
    · intro a ha
      have hb := x.property.2 ha
      change Finsupp.weight w a + 1 ≤ d at hb
      change Finsupp.weight w a + j ≤ d
      by_contra hnot
      have haLT : Finsupp.weight w a < d := by omega
      have hh := hx (Sum.inr ⟨a, haLT⟩) (by
        change ¬ j ≤ d - Finsupp.weight w a
        omega)
      rw [weightedBasis_repr_inr] at hh
      exact (MvPolynomial.mem_support_iff.mp ha) hh

theorem weightedBasis_top_projection_eq (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val =
      topProjection w d x.val :=
  weightedBasis_top_projection_val w d hw hd x

theorem topProjection_mem_map_of_basisGraded (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U)
    {x : PolynomialTranslationLie σ}
    (hx : x ∈ U.map (weightedSubalgebra w d).subtype) :
    topProjection w d x ∈ U.map (weightedSubalgebra w d).subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨_, hU d y hy, weightedBasis_top_projection_eq w d hw hd y⟩

theorem topProjection_mem_of_basisGraded (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype))
    {x : PolynomialTranslationLie σ} (hx : x ∈ U) : topProjection w d x ∈ U := by
  let y : weightedSubalgebra w d := ⟨x, hU hx⟩
  have hy := hgraded d y hx
  change (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d y).val ∈ U at hy
  rw [weightedBasis_top_projection_eq w d hw hd] at hy
  exact hy

theorem weightedBasis_projection_isWeightedHomogeneous (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.IsWeightedHomogeneous w (d - j) := by
  classical
  intro a ha
  have hbound := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).property.2
    (MvPolynomial.mem_support_iff.mpr ha)
  change Finsupp.weight w a + 1 ≤ d at hbound
  have haLT : Finsupp.weight w a < d := by omega
  rw [weightedBasis_projection_coeff w d j hw x ⟨a, haLT⟩] at ha
  have hgrade : d - Finsupp.weight w a = j := by
    by_contra hne
    simp only [hne, ↓reduceIte, ne_self_iff_false] at ha
  omega

theorem exists_homogeneous_coordinate_lifts [DecidableEq σ] (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (weightedSubalgebra w d))
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U)
    (hsurj : Function.Surjective (fun x : U => x.val.val.base)) :
    ∃ P : σ → MvPolynomial σ ℚ,
      (∀ i, (⟨Pi.single i 1, P i⟩ : PolynomialTranslationLie σ) ∈
        U.map (weightedSubalgebra w d).subtype) ∧
      ∀ i, (P i).IsWeightedHomogeneous w (d - w i) := by
  classical
  have h : ∀ i : σ, ∃ P : MvPolynomial σ ℚ,
      (⟨Pi.single i 1, P⟩ : PolynomialTranslationLie σ) ∈
        U.map (weightedSubalgebra w d).subtype ∧
      P.IsWeightedHomogeneous w (d - w i) := by
    intro i
    obtain ⟨x, hx⟩ := hsurj (Pi.single i 1)
    change x.val.val.base = Pi.single i 1 at hx
    let y := basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) (w i) x.val
    have hy : y ∈ U := hgraded (w i) x.val x.property
    have hbase : y.val.base = Pi.single i 1 := by
      funext k
      rw [weightedBasis_projection_base, hx]
      by_cases hk : k = i
      · subst k
        simp
      · simp [hk]
    refine ⟨y.val.polynomial, ⟨y, hy, ?_⟩,
      weightedBasis_projection_isWeightedHomogeneous w d (w i) hw x.val⟩
    exact PolynomialTranslationLie.ext hbase rfl
  choose P hP hhom using h
  exact ⟨P, hP, hhom⟩

theorem exists_ambient_homogeneous_coordinate_lifts [DecidableEq σ] (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype))
    (hsurj : Function.Surjective (fun x : U => x.val.base)) :
    ∃ P : σ → MvPolynomial σ ℚ,
      (∀ i, (⟨Pi.single i 1, P i⟩ : PolynomialTranslationLie σ) ∈ U) ∧
      ∀ i, (P i).IsWeightedHomogeneous w (d - w i) := by
  let U' := U.comap (weightedSubalgebra w d).subtype
  have hs : Function.Surjective (fun x : U' => x.val.val.base) := by
    intro b
    obtain ⟨x, hx⟩ := hsurj b
    exact ⟨⟨⟨x.val, hU x.property⟩, x.property⟩, hx⟩
  obtain ⟨P, hP, hhom⟩ := exists_homogeneous_coordinate_lifts w d hw U' hgraded hs
  refine ⟨P, fun i => ?_, hhom⟩
  obtain ⟨x, hx, he⟩ := hP i
  exact he ▸ hx

omit [Fintype σ] in
theorem weightedBasisGrade_pos (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (i : WeightedBasisIndex w d) : 0 < weightedBasisGrade w d i := by
  cases i with
  | inl i => exact hw i
  | inr a => exact Nat.sub_pos_of_lt a.property

omit [Fintype σ] in
theorem weightedBasisGrade_le (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (i : WeightedBasisIndex w d) : weightedBasisGrade w d i ≤ d := by
  cases i with
  | inl i => exact hw i
  | inr a => exact Nat.sub_le _ _

theorem weightedBasisIndex_finite (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Finite (WeightedBasisIndex w d) := by
  let : Finite {a : σ →₀ ℕ | Finsupp.weight w a < d} :=
    (Finsupp.finite_of_nat_weight_lt w (fun i => (hw i).ne') d).to_subtype
  infer_instance

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ}

theorem weightedBasis_base_height
    (hall : ∀ i : WeightedBasisIndex w d,
      RationalHeightLE ((weightedBasis w d hw).repr x i) H) :
    ∀ i, RationalHeightLE (x.val.base i) H := by
  intro i
  simpa only [weightedBasis_repr_inl] using hall (Sum.inl i)

theorem weightedBasis_polynomial_height (hH : 1 ≤ H)
    (hall : ∀ i : WeightedBasisIndex w d,
      RationalHeightLE ((weightedBasis w d hw).repr x i) H) :
    RationalPolynomialHeightLE x.val.polynomial H := by
  intro α
  by_cases hα : Finsupp.weight w α < d
  · exact hall (Sum.inr ⟨α, hα⟩)
  · have hzero : x.val.polynomial.coeff α = 0 := by
      by_contra hne
      have h := x.property.2 (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w α + 1 ≤ d at h
      omega
    rw [hzero]
    exact rationalHeightLE_zero hH

theorem weightedBasis_height_iff (hH : 1 ≤ H) :
    (∀ i : WeightedBasisIndex w d,
      RationalHeightLE ((weightedBasis w d hw).repr x i) H) ↔
    (∀ i, RationalHeightLE (x.val.base i) H) ∧
      RationalPolynomialHeightLE x.val.polynomial H := by
  constructor
  · intro hall
    exact ⟨weightedBasis_base_height w d hw x hall,
      weightedBasis_polynomial_height w d hw x hH hall⟩
  · rintro ⟨hbase, hpoly⟩ (i | α)
    · simpa only [weightedBasis_repr_inl] using hbase i
    · exact hpoly α.val

end Erdos3.PolynomialTranslationLie

end

end OAI
