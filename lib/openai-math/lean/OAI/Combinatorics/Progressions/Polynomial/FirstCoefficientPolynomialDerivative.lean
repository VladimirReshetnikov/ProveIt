/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.FastHorizontalFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def adaptedShiftedGradedPolynomial (k : ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  (F.shiftedGradedPolynomial b ω hF w k).comp (F.adaptedLieSubalgebra w).incl.toLinearMap

@[simp] theorem adaptedShiftedGradedPolynomial_apply (k : ℕ) (p : F.adaptedLieSubalgebra w) :
    F.adaptedShiftedGradedPolynomial b ω hF w k p =
      F.shiftedGradedPolynomial b ω hF w k p.val := rfl

noncomputable def adaptedGradedPolynomialLie :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ F.AssociatedGraded :=
  (F.gradedSymbolPolynomialLie b ω hF w).comp (F.polynomialSymbolMap w)

theorem adaptedGradedPolynomialLie_apply (p : F.adaptedLieSubalgebra w) :
    F.adaptedGradedPolynomialLie b ω hF w p = F.adaptedShiftedGradedPolynomial b ω hF w 0 p := by
  exact (F.shiftedGradedPolynomial_zero b ω hF w p).symm

theorem adaptedShiftedGradedPolynomial_lie (p q : F.adaptedLieSubalgebra w)
    (hq : q ∈ F.shiftedPolynomialIdeal w 1) :
    F.adaptedShiftedGradedPolynomial b ω hF w 1 ⁅p, q⁆ =
      ⁅F.adaptedGradedPolynomialLie b ω hF w p, F.adaptedShiftedGradedPolynomial b ω hF w 1 q⁆ := by
  have hp : p.val ∈ F.shiftedAdaptedSubmodule w 0 := by
    intro α
    simpa only [Nat.add_zero] using p.property α
  rw [F.adaptedGradedPolynomialLie_apply]
  have hq' : q.val ∈ F.shiftedAdaptedSubmodule w 1 := hq
  rw [F.adaptedShiftedGradedPolynomial_apply, F.adaptedShiftedGradedPolynomial_apply,
    F.adaptedShiftedGradedPolynomial_apply, LieSubalgebra.coe_bracket]
  have he := F.shiftedGradedPolynomial_lie b ω hF w (i := 0) (j := 1)
    (p := p.val) (q := q.val) hp hq'
  rw [Nat.zero_add] at he
  rw [he]

noncomputable def firstCoefficientGradedPolynomial :
    F.FirstCoefficientModule w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).liftQ
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).comp
        (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype) (by
          intro p hp
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
            F.adaptedShiftedGradedPolynomial_apply]
          have hp' : p.val.val ∈ F.shiftedAdaptedSubmodule w 1 := p.property
          have hp'' : p.val.val ∈ F.shiftedAdaptedSubmodule w 2 := hp
          exact (F.shiftedGradedPolynomial_eq_zero_iff b ω hF w 1 hp').mpr hp'')

@[simp] theorem firstCoefficientGradedPolynomial_map (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientGradedPolynomial b ω hF w (F.firstCoefficientMap w p) =
      F.adaptedShiftedGradedPolynomial b ω hF w 1 p.val := by
  unfold firstCoefficientGradedPolynomial firstCoefficientMap
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  rfl

theorem firstCoefficientGradedPolynomial_coordinate (x : F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) (i : ι) :
    (F.associatedGradedBasis b ω hF).repr
      (coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α) i =
      if h : Finsupp.weight w α + 1 = ω i then
        (F.firstCoefficientBasis b ω hF w).repr x ⟨(α, i), h⟩ else 0 := by
  classical
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_coefficient, F.gradedPieceProjection_coordinate]
  by_cases h : Finsupp.weight w α + 1 = ω i
  · rw [dite_eq_left h, ite_eq_left h.symm, F.firstCoefficientBasis_repr_map]
  · rw [dite_eq_right h, ite_eq_right (Ne.symm h)]

theorem firstCoefficientGradedPolynomial_injective :
    Function.Injective (F.firstCoefficientGradedPolynomial b ω hF w) := by
  intro x y hxy
  apply (F.firstCoefficientBasis b ω hF w).repr.injective
  ext z
  have h := congrArg (fun P => (F.associatedGradedBasis b ω hF).repr (coefficients P z.val.1) z.val.2) hxy
  simpa only [F.firstCoefficientGradedPolynomial_coordinate, dite_eq_left z.property] using h

theorem firstCoefficientGradedPolynomial_homogeneous (x : F.FirstCoefficientModule w) (α : σ →₀ ℕ) :
    basisGradeProjection (F.associatedGradedBasis b ω hF) ω (Finsupp.weight w α + 1)
      (coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α) =
        coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α := by
  apply (F.associatedGradedBasis b ω hF).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases hi : ω i = Finsupp.weight w α + 1
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, F.firstCoefficientGradedPolynomial_coordinate, dite_eq_right (Ne.symm hi)]

theorem firstCoefficientGradedPolynomial_horizontal (x : F.FirstCoefficientModule w) :
    coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) 0 =
      F.layerOneGradedMap b ω hF (F.firstCoefficientHorizontal w x) := by
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_coefficient, F.firstCoefficientHorizontal_map, F.layerOneGradedMap_mk]
  simp only [map_zero, zero_add]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientGradedPolynomial :
    F.RealFirstCoefficientModule w →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationRealLinearEquiv.toLinearMap.comp
    (((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ).comp
      (F.firstCoefficientRealEquiv w).symm.toLinearMap)

theorem realFirstCoefficientGradedPolynomial_realEquiv (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.firstCoefficientRealEquiv w x) =
      realificationRealLinearEquiv ((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ x) := by
  simp only [realFirstCoefficientGradedPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem realFirstCoefficientGradedPolynomial_tmul (a : ℝ) (x : F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) :
    coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w
      (F.firstCoefficientRealEquiv w (a ⊗ₜ[ℚ] x))) α =
      a ⊗ₜ[ℚ] coefficients (F.firstCoefficientGradedPolynomial b ω hF w x) α := by
  rw [F.realFirstCoefficientGradedPolynomial_realEquiv, LinearMap.baseChange_tmul,
    realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul]

theorem realFirstCoefficientGradedPolynomial_coordinate (x : F.RealFirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) z.val.1) z.val.2 =
      (F.realFirstCoefficientBasis b ω hF w).repr x z := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  rw [F.firstCoefficientRealEquiv_coordinates]
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, Basis.baseChange_repr_tmul,
      F.firstCoefficientGradedPolynomial_coordinate, dite_eq_left z.property,
      Basis.baseChange_repr_tmul]

theorem realFirstCoefficientGradedPolynomial_coordinate_of_ne (x : F.RealFirstCoefficientModule w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α + 1 ≠ ω i) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) α) i = 0 := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, Basis.baseChange_repr_tmul,
      F.firstCoefficientGradedPolynomial_coordinate, dite_eq_right h, zero_smul]

theorem realFirstCoefficientGradedPolynomial_injective :
    Function.Injective (F.realFirstCoefficientGradedPolynomial b ω hF w) := by
  intro x y hxy
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [← F.realFirstCoefficientGradedPolynomial_coordinate,
    ← F.realFirstCoefficientGradedPolynomial_coordinate, hxy]

theorem realFirstCoefficientGradedPolynomial_homogeneous (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w x ∈
      shiftedGradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w 1 := by
  intro α
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [LinearMap.restrictScalars_apply, basisGradeProjection_repr]
  by_cases hi : ω i = Finsupp.weight w α + 1
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i (Ne.symm hi)]

theorem realFirstCoefficientGradedPolynomial_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound b ω hF w T M x) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  intro α i
  by_cases hi : Finsupp.weight w α + 1 = ω i
  · rw [F.realFirstCoefficientGradedPolynomial_coordinate b ω hF w x ⟨(α, i), hi⟩]
    exact hx ⟨(α, i), hi⟩
  · rw [F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i hi, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realFirstCoefficientGradedPolynomial_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid b ω hF w l x) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) l
      (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  classical
  obtain ⟨v, hv⟩ := hx
  intro α
  refine ⟨fun i => if h : Finsupp.weight w α + 1 = ω i then v ⟨(α, i), h⟩ else 0, ?_⟩
  funext i
  change ((if h : Finsupp.weight w α + 1 = ω i then v ⟨(α, i), h⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) α) i
  by_cases hi : Finsupp.weight w α + 1 = ω i
  · rw [dite_eq_left hi, F.realFirstCoefficientGradedPolynomial_coordinate b ω hF w x ⟨(α, i), hi⟩]
    exact congrFun hv ⟨(α, i), hi⟩
  · rw [dite_eq_right hi, Int.cast_zero,
      F.realFirstCoefficientGradedPolynomial_coordinate_of_ne b ω hF w x α i hi, mul_zero]

theorem realFirstCoefficientGradedPolynomial_horizontal (x : F.RealFirstCoefficientModule w) :
    coefficients (F.realFirstCoefficientGradedPolynomial b ω hF w x) 0 =
      (F.layerOneGradedMap b ω hF).baseChange ℝ (F.realFirstCoefficientHorizontal w x) := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change _ = (F.layerOneGradedMap b ω hF).baseChange ℝ
    ((F.firstCoefficientHorizontal w).baseChange ℝ ((F.firstCoefficientRealEquiv w).symm
      (F.firstCoefficientRealEquiv w y)))
  rw [LinearEquiv.symm_apply_apply]
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realFirstCoefficientGradedPolynomial_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, F.firstCoefficientGradedPolynomial_horizontal]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realAdaptedShiftedGradedPolynomial (k : ℕ) :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ[ℝ]
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationRealLinearEquiv.toLinearMap.comp
    ((F.adaptedShiftedGradedPolynomial b ω hF w k).baseChange ℝ)

noncomputable def realAdaptedGradedPolynomialLie :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  realificationLieEquiv.toLieHom.comp
    (realLieHomToRat (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w)))

theorem realAdaptedShiftedGradedPolynomial_tensor (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w k x =
      realificationRealLinearEquiv ((F.adaptedShiftedGradedPolynomial b ω hF w k).baseChange ℝ x) := rfl

theorem realAdaptedGradedPolynomialLie_tensor (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      realificationLieEquiv (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w) x) := rfl

theorem realAdaptedGradedPolynomialLie_apply (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      F.realAdaptedShiftedGradedPolynomial b ω hF w 0 x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a p =>
    rw [F.realAdaptedGradedPolynomialLie_tensor, realificationLieHom_tmul,
      F.realAdaptedShiftedGradedPolynomial_tensor, LinearMap.baseChange_tmul,
      F.adaptedGradedPolynomialLie_apply]
    apply coefficients.injective
    ext α
    rw [coefficients_realificationLieEquiv_tmul, realificationRealLinearEquiv_apply,
      coefficients_realificationLinearEquiv_tmul]

theorem realAdaptedGradedPolynomialLie_symbol (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie b ω hF w x =
      F.realGradedSymbolPolynomial b ω hF w
        (realificationLieHom (F.polynomialSymbolMap w) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a p =>
    rw [F.realAdaptedGradedPolynomialLie_tensor, realificationLieHom_tmul,
      realificationLieHom_tmul]
    apply coefficients.injective
    ext α
    rw [coefficients_realificationLieEquiv_tmul, F.realGradedSymbolPolynomial_coefficient_tmul]
    rw [F.adaptedGradedPolynomialLie_apply, F.adaptedShiftedGradedPolynomial_apply,
      F.shiftedGradedPolynomial_zero]

theorem realAdaptedShiftedGradedPolynomial_lie
    (x y : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hy : y ∈ F.realShiftedCoefficientSubmodule w 1) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w 1 ⁅x, y⁆ =
      ⁅F.realAdaptedGradedPolynomialLie b ω hF w x,
        F.realAdaptedShiftedGradedPolynomial b ω hF w 1 y⁆ := by
  change realificationLieEquiv
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ ⁅x, y⁆) =
    ⁅realificationLieEquiv (realificationLieHom (F.adaptedGradedPolynomialLie b ω hF w) x),
      realificationLieEquiv ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ y)⁆
  rw [realification_ideal_intertwining (F.shiftedPolynomialIdeal w 1)
    (F.adaptedGradedPolynomialLie b ω hF w) (F.adaptedShiftedGradedPolynomial b ω hF w 1)
    (F.adaptedShiftedGradedPolynomial_lie b ω hF w) x y hy, LieEquiv.map_lie]

theorem realFirstCoefficientGradedPolynomial_map (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientMap w x) =
      F.realAdaptedShiftedGradedPolynomial b ω hF w 1 x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule).surjective x
  rw [← F.firstCoefficientRealEquiv_map, F.realFirstCoefficientGradedPolynomial_realEquiv]
  have he : (F.firstCoefficientGradedPolynomial b ω hF w).comp (F.firstCoefficientMap w) =
      (F.adaptedShiftedGradedPolynomial b ω hF w 1).comp
        (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype := by
    apply LinearMap.ext
    intro p
    exact F.firstCoefficientGradedPolynomial_map b ω hF w p
  change realificationRealLinearEquiv
      ((F.firstCoefficientGradedPolynomial b ω hF w).baseChange ℝ
        ((F.firstCoefficientMap w).baseChange ℝ y)) =
    realificationRealLinearEquiv
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).baseChange ℝ
        ((F.shiftedPolynomialIdeal w 1).toSubmodule.subtype.baseChange ℝ y))
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he,
    LinearMap.baseChange_comp, LinearMap.comp_apply]

noncomputable def realAdaptedGradedPolynomialHom :
    F.RealAdaptedPolynomialGroup w →*
      PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realAdaptedGradedPolynomialLie b ω hF w)

theorem realAdaptedShiftedGradedPolynomial_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : x ∈ F.realShiftedCoefficientSubmodule w 1) :
    F.realAdaptedShiftedGradedPolynomial b ω hF w 1 (dualAdjoint g x) =
      dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
        (F.realAdaptedShiftedGradedPolynomial b ω hF w 1 x) := by
  let I : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
    { (F.realShiftedCoefficientSubmodule w 1).restrictScalars ℚ with
      lie_mem := fun {a y} hy => F.realShiftedCoefficient_lie_mem w 1 a y hy }
  exact dualLinearLift_adjoint
    (VectorPolynomial.lowerCentralSeries_eq_bot
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    I (F.realAdaptedGradedPolynomialLie b ω hF w)
    ((F.realAdaptedShiftedGradedPolynomial b ω hF w 1).restrictScalars ℚ)
    (F.realAdaptedShiftedGradedPolynomial_lie b ω hF w) g x hx

theorem realFirstCoefficientGradedPolynomial_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientAdjoint w g x) =
      dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
        (F.realFirstCoefficientGradedPolynomial b ω hF w x) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientGradedPolynomial b ω hF w
      (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w y)) =
    dualAdjoint (F.realAdaptedGradedPolynomialHom b ω hF w g)
      (F.realFirstCoefficientGradedPolynomial b ω hF w (F.realFirstCoefficientMap w y))
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientGradedPolynomial_map,
    F.realFirstCoefficientGradedPolynomial_map]
  exact F.realAdaptedShiftedGradedPolynomial_adjoint b ω hF w g y.val y.property

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem adaptedShiftedGradedPolynomial_directionalDerivative (h : σ → ℚ) (k : ℕ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) (k + 1)
        (F.adaptedDirectionalDerivative h p) =
      directionalDerivative h (F.adaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) k p) := by
  rw [F.adaptedShiftedGradedPolynomial_apply, F.adaptedDirectionalDerivative_coe,
    F.adaptedShiftedGradedPolynomial_apply]
  exact F.shiftedGradedPolynomial_directionalDerivative b ω hF h k p.val

theorem realAdaptedShiftedGradedPolynomial_directionalDerivative (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1
        (F.realAdaptedDirectionalDerivative h x) =
      directionalDerivative h (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1) x) := by
  rw [F.realAdaptedGradedPolynomialLie_apply]
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a p =>
    have hd : F.realAdaptedDirectionalDerivative h (a ⊗ₜ[ℚ] p) =
        a ⊗ₜ[ℚ] F.adaptedDirectionalDerivative h p := rfl
    rw [hd, F.realAdaptedShiftedGradedPolynomial_tensor, F.realAdaptedShiftedGradedPolynomial_tensor,
      LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    rw [realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      F.adaptedShiftedGradedPolynomial_directionalDerivative b ω hF h 0]
    rw [coefficients_directionalDerivative, coefficients_directionalDerivative]
    simp only [realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul]

variable [DecidableEq σ]

theorem realAdaptedGradedPolynomial_firstJet (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    dualLinearLift (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1))
        ((F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1).restrictScalars ℚ)
        (F.realAdaptedPolynomialJet (Pi.single i 1) g.coord).coord =
      (formalPolynomialJetHom i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g)).coord := by
  classical
  apply dual_ext
  · rw [dualLinearLift_base, F.realAdaptedPolynomialJet_base, formalPolynomialJet_base]
    rfl
  · rw [dualLinearLift_tangent, F.realAdaptedPolynomialJet_tangent, formalPolynomialJet_tangent,
      LinearMap.restrictScalars_apply, F.realAdaptedShiftedGradedPolynomial_directionalDerivative,
      directionalDerivative_single]
    rfl

theorem realAdaptedGradedPolynomial_logDerivative (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1
        (F.realAdaptedLogDerivative (Pi.single i 1) g.coord) =
      formalLogDerivative i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g) := by
  classical
  let I : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
    { (F.realShiftedCoefficientSubmodule (fun _ : σ => 1) 1).restrictScalars ℚ with
      lie_mem := fun {a y} hy => F.realShiftedCoefficient_lie_mem (fun _ : σ => 1) 1 a y hy }
  apply dualLinearLift_logDerivative_eq
    (VectorPolynomial.lowerCentralSeries_eq_bot
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    I (F.realAdaptedGradedPolynomialLie b ω hF (fun _ : σ => 1))
    ((F.realAdaptedShiftedGradedPolynomial b ω hF (fun _ : σ => 1) 1).restrictScalars ℚ)
    (F.realAdaptedShiftedGradedPolynomial_lie b ω hF (fun _ : σ => 1))
    (F.realAdaptedPolynomialJet (Pi.single i 1) g.coord) _
    (formalPolynomialJetHom i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g))
  · exact F.realAdaptedGradedPolynomial_firstJet b ω hF i g
  · rw [F.realAdaptedPolynomialJet_tangent]
    exact F.realAdaptedDirectionalDerivative_mem_first (Pi.single i 1) g.coord

theorem realFirstCoefficientGradedPolynomial_direction (i : σ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientGradedPolynomial b ω hF (fun _ : σ => 1)
        (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1)) =
      formalLogDerivative i (F.realAdaptedGradedPolynomialHom b ω hF (fun _ : σ => 1) g) := by
  classical
  have he : (Pi.single i (1 : ℝ) : σ → ℝ) =
      (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [he, F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientGradedPolynomial_map]
  exact F.realAdaptedGradedPolynomial_logDerivative b ω hF i g

end Erdos3.NilpotentLieFiltration

end

end OAI
