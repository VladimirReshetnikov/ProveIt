/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinateFreezeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem realPolynomialSymbolHom_frozenChart_independent
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (keep : τ → Prop) (fixed fixed' : {i // ¬keep i} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed (β i))
        (fun i => freezePolynomial_support keep fixed (hβ i)) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed' (β i))
        (fun i => freezePolynomial_support keep fixed' (hβ i)) g) := by
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
    F.realPolynomialSymbolHom_weightedAdaptedRealChart]
  have htop : (fun i => weightedHomogeneousComponent (fun _ : {i // keep i} => 1) (w i)
      (freezePolynomial keep fixed (β i))) =
      (fun i => weightedHomogeneousComponent (fun _ : {i // keep i} => 1) (w i)
        (freezePolynomial keep fixed' (β i))) := by
    funext i
    exact freezePolynomial_top_independent keep fixed fixed'
      ((mem_weightedSupportLE_one_iff _ _).mp (hβ i))
  congr 1
  congr 1

theorem realSymbolFactorization_frozenChart_change_fiber
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (keep : τ → Prop) (fixed fixed' : {i // ¬keep i} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1))
    (hfactor : E * P * R = F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed (β i))
        (fun i => freezePolynomial_support keep fixed (hβ i)) g)) :
    E * P * R = F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed' (β i))
        (fun i => freezePolynomial_support keep fixed' (hβ i)) g) :=
  hfactor.trans (F.realPolynomialSymbolHom_frozenChart_independent b ω hF w β hβ keep fixed fixed' g)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

noncomputable def nestedFrozenCoordinate
    (keepLong keepLater : σ → Prop)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R)
    (i : {i // keepLong i}) : MvPolynomial {i // keepLater i} R :=
  if hi : keepLater i.val then X ⟨i.val, hi⟩ else C (fixed ⟨i, hi⟩)

theorem nestedFrozenCoordinate_support
    (keepLong keepLater : σ → Prop)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R)
    (i : {i // keepLong i}) :
    nestedFrozenCoordinate keepLong keepLater fixed i ∈ weightedSupportLE (fun _ : {i : σ // keepLater i} => 1) 1 := by
  by_cases hi : keepLater i.val
  · simp only [nestedFrozenCoordinate, dite_eq_left hi]
    exact weightedSupportLE_X (R := R) (fun _ : {i : σ // keepLater i} => 1) ⟨i.val, hi⟩
  · simp only [nestedFrozenCoordinate, dite_eq_right hi]
    exact weightedSupportLE_C (fun _ : {i : σ // keepLater i} => 1) 1 (fixed ⟨i, hi⟩)

def nestedFrozenVariableEquiv
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i) :
    {i // keepLater i} ≃ {i : {i // keepLong i} // keepLater i.val} where
  toFun i := ⟨⟨i.val, hsub i.val i.property⟩, i.property⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nestedFrozenCoordinate_eq_freeze_reindex
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R) :
    (fun i => aeval
      (fun j => X ((nestedFrozenVariableEquiv keepLong keepLater hsub).symm j))
      (frozenCoordinate (fun i : {i // keepLong i} => keepLater i.val) fixed i)) =
      nestedFrozenCoordinate keepLong keepLater fixed := by
  funext i
  by_cases hi : keepLater i.val <;>
    simp [frozenCoordinate, nestedFrozenCoordinate, nestedFrozenVariableEquiv, hi]

theorem frozenCoordinate_zero_comp_nested
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i) :
    (fun i => aeval (nestedFrozenCoordinate keepLong keepLater (0 : {i : {i // keepLong i} // ¬keepLater i.val} → R))
      (frozenCoordinate keepLong (0 : {i // ¬keepLong i} → R) i)) =
      frozenCoordinate keepLater (0 : {i // ¬keepLater i} → R) := by
  funext i
  by_cases hlater : keepLater i
  · have hlong := hsub i hlater
    simp [frozenCoordinate, nestedFrozenCoordinate, hlater, hlong]
  · by_cases hlong : keepLong i <;>
      simp [frozenCoordinate, nestedFrozenCoordinate, hlater, hlong]

theorem nestedFrozenCoordinate_top_independent
    (keepOriginal keepLater : σ → Prop)
    (fixed fixed' : {i : {i // keepOriginal i} // ¬keepLater i.val} → R)
    (i : {i // keepOriginal i}) :
    weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
      (nestedFrozenCoordinate keepOriginal keepLater fixed i) =
    weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
      (nestedFrozenCoordinate keepOriginal keepLater fixed' i) := by
  by_cases hi : keepLater i.val
  · simp only [nestedFrozenCoordinate, dite_eq_left hi]
  · simp only [nestedFrozenCoordinate, dite_eq_right hi]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := R) _ _),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := R) _ _)]
    norm_num

theorem nestedFrozenCoordinate_zero_comp
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i) :
    (fun i => aeval
      (nestedFrozenCoordinate keepLong keepLater
        (0 : {i : {i // keepLong i} // ¬keepLater i.val} → R))
      (nestedFrozenCoordinate keepOriginal keepLong
        (0 : {i : {i // keepOriginal i} // ¬keepLong i.val} → R) i)) =
    nestedFrozenCoordinate keepOriginal keepLater
      (0 : {i : {i // keepOriginal i} // ¬keepLater i.val} → R) := by
  funext i
  by_cases hlater : keepLater i.val
  · have hlong := hsub i.val hlater
    simp [nestedFrozenCoordinate, hlater, hlong]
  · by_cases hlong : keepLong i.val <;>
      simp [nestedFrozenCoordinate, hlater, hlong]

namespace NilpotentLieFiltration

open Module VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem weightedAdaptedRealChartHom_nested_zero
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : {i // keepLater i} => 1)
      (frozenCoordinate keepLater 0) (frozenCoordinate_support keepLater 0) g =
    F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
      (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
      (nestedFrozenCoordinate_support keepLong keepLater 0)
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : {i // keepLong i} => 1)
        (frozenCoordinate keepLong 0) (frozenCoordinate_support keepLong 0) g) := by
  have hcomp := F.weightedAdaptedRealChartHom_comp
    (fun _ : σ => 1) (fun _ : {i // keepLong i} => 1) (fun _ : {i // keepLater i} => 1)
    (frozenCoordinate keepLong 0) (nestedFrozenCoordinate keepLong keepLater 0)
    (frozenCoordinate_support keepLong 0) (nestedFrozenCoordinate_support keepLong keepLater 0)
    (weightedRealChart_comp_support _ _ _ _ _
      (frozenCoordinate_support keepLong 0) (nestedFrozenCoordinate_support keepLong keepLater 0)) g
  simpa only [frozenCoordinate_zero_comp_nested keepLong keepLater hsub] using hcomp

theorem realPolynomialSymbolHom_nested_frozenCoordinate
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i // ¬keepLater i} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : {i // keepLater i} => 1)
        (frozenCoordinate keepLater fixed) (frozenCoordinate_support keepLater fixed) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
        (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
        (nestedFrozenCoordinate_support keepLong keepLater 0)
        (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : {i // keepLong i} => 1)
          (frozenCoordinate keepLong 0) (frozenCoordinate_support keepLong 0) g)) := by
  rw [← F.weightedAdaptedRealChartHom_nested_zero keepLong keepLater hsub g]
  simpa only [freezePolynomial, aeval_X] using
    F.realPolynomialSymbolHom_frozenChart_independent b ω hF (fun _ : σ => 1)
      (fun i => X i) (fun i => weightedSupportLE_X (R := ℝ) (fun _ : σ => 1) i)
      keepLater fixed 0 g

theorem weightedAdaptedRealChartHom_nested_nested_zero
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
      (fun _ : {i // keepLater i} => 1)
      (nestedFrozenCoordinate keepOriginal keepLater 0)
      (nestedFrozenCoordinate_support keepOriginal keepLater 0) g =
    F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
      (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
      (nestedFrozenCoordinate_support keepLong keepLater 0)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLong i} => 1) (nestedFrozenCoordinate keepOriginal keepLong 0)
        (nestedFrozenCoordinate_support keepOriginal keepLong 0) g) := by
  have hcomp := F.weightedAdaptedRealChartHom_comp
    (fun _ : {i // keepOriginal i} => 1) (fun _ : {i // keepLong i} => 1)
    (fun _ : {i // keepLater i} => 1)
    (nestedFrozenCoordinate keepOriginal keepLong 0)
    (nestedFrozenCoordinate keepLong keepLater 0)
    (nestedFrozenCoordinate_support keepOriginal keepLong 0)
    (nestedFrozenCoordinate_support keepLong keepLater 0)
    (weightedRealChart_comp_support _ _ _ _ _
      (nestedFrozenCoordinate_support keepOriginal keepLong 0)
      (nestedFrozenCoordinate_support keepLong keepLater 0)) g
  simpa only [nestedFrozenCoordinate_zero_comp keepOriginal keepLong keepLater hsub] using hcomp

theorem realPolynomialSymbolHom_nested_frozenCoordinate_independent
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (keepOriginal keepLater : σ → Prop)
    (fixed fixed' : {i : {i // keepOriginal i} // ¬keepLater i.val} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed)
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed')
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed') g) := by
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
    F.realPolynomialSymbolHom_weightedAdaptedRealChart]
  have htop :
      (fun i => weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
        (nestedFrozenCoordinate keepOriginal keepLater fixed i)) =
      (fun i => weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
        (nestedFrozenCoordinate keepOriginal keepLater fixed' i)) := by
    funext i
    exact nestedFrozenCoordinate_top_independent keepOriginal keepLater fixed fixed' i
  congr 1
  congr 1

theorem realPolynomialSymbolHom_nested_nested_frozenCoordinate
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepOriginal i} // ¬keepLater i.val} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed)
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
        (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
        (nestedFrozenCoordinate_support keepLong keepLater 0)
        (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
          (fun _ : {i // keepLong i} => 1) (nestedFrozenCoordinate keepOriginal keepLong 0)
          (nestedFrozenCoordinate_support keepOriginal keepLong 0) g)) := by
  rw [← F.weightedAdaptedRealChartHom_nested_nested_zero keepOriginal keepLong keepLater hsub g]
  exact F.realPolynomialSymbolHom_nested_frozenCoordinate_independent
    b ω hF keepOriginal keepLater fixed 0 g

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem HasCommonRefilteredOrbitFactors.freeze
    (keep : σ → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℝ) (side : σ → ℝ) (q : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF (fun i : {i // keep i} => side i.val)
      q l W (F.weightedAdaptedRealChartHom (fun _ : σ => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
        (frozenCoordinate_support keep fixed) g) := by
  classical
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, _⟩ := h
  let pull := F.polynomialCoordinateFreezeZeroHom keep
  let actual := F.weightedAdaptedRealChartHom (fun _ : σ => 1)
    (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
    (frozenCoordinate_support keep fixed) g
  let adjusted := (pull left)⁻¹ * actual * (pull right)⁻¹
  let symbol := F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
  have hfiber : symbol actual = symbol (pull g) := by
    symm
    simpa only [symbol, actual, pull, polynomialCoordinateFreezeZeroHom,
      freezePolynomial, aeval_X] using
      F.realPolynomialSymbolHom_frozenChart_independent b ω hF (fun _ : σ => 1)
        (fun i => X i) (fun i => weightedSupportLE_X (R := ℝ) (fun _ : σ => 1) i)
        keep 0 fixed g
  have hcancel : (pull left)⁻¹ * pull g * (pull right)⁻¹ = pull middle := by
    rw [← hprod, map_mul, map_mul]
    group
  have hadjusted : symbol adjusted = symbol (pull middle) := by
    calc
      _ = symbol ((pull left)⁻¹ * pull g * (pull right)⁻¹) := by
        simp only [adjusted, map_mul, map_inv, hfiber]
      _ = _ := congrArg symbol hcancel
  have hactual : pull left * adjusted * pull right = actual := by
    dsimp only [adjusted]
    group
  have he0 := F.polynomialCoordinateFreezeZeroHom_zero_constant keep b left hleft0
  have hr0 := F.polynomialCoordinateFreezeZeroHom_zero_constant keep b right hright0
  refine ⟨pull left, adjusted, pull right, hactual, ?_,
    F.polynomialSlowBound_freeze_zero keep b side left hleft,
    F.polynomialRationalGrid_freeze_zero keep b l right hright, he0, hr0, ?_⟩
  · change ∀ t, VectorPolynomial.eval₂ t (F.realGradedSymbolPolynomial b ω hF
      (fun _ : {i // keep i} => 1) (symbol adjusted).coord) ∈ _
    rw [hadjusted]
    apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : {i // keep i} => 1) W _).mp
    have hsymbol := F.realPolynomialSymbolHom_homogeneousChart b ω hF
      (fun _ : σ => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
      (frozenCoordinate_zero_homogeneous keep) middle (pull middle)
      (F.polynomialCoordinateFreezeZeroHom_coord keep middle)
    change (F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (pull middle)).coord ∈ _
    rw [hsymbol]
    apply F.realSymbolHomogeneousPullback_mem_pointwise b ω hF
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : σ => 1) W _).mpr hmid
  · exact F.realification.polynomial_factor_middle_constant
      (fun _ : {i // keep i} => 1) actual (pull left) adjusted (pull right)
      hactual he0 hr0

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realPolynomialSymbolHom

theorem HasCommonRefilteredOrbitFactors.of_symbol_eq
    (side : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g actual : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g)
    (hsymbol : F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) actual =
      F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) g) :
    F.HasCommonRefilteredOrbitFactors b ω hF side q l W actual := by
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, _⟩ := h
  let adjusted := left⁻¹ * actual * right⁻¹
  let symbol := F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1)
  have hcancel : left⁻¹ * g * right⁻¹ = middle := by
    rw [← hprod]
    group
  have hadjusted : symbol adjusted = symbol middle := by
    calc
      _ = symbol (left⁻¹ * g * right⁻¹) := by
        simp only [adjusted, map_mul, map_inv, show symbol actual = symbol g from hsymbol]
      _ = _ := congrArg symbol hcancel
  have hactual : left * adjusted * right = actual := by
    dsimp only [adjusted]
    group
  refine ⟨left, adjusted, right, hactual, ?_, hleft, hright, hleft0, hright0, ?_⟩
  · change ∀ t, eval₂ t (F.realGradedSymbolPolynomial b ω hF
      (fun _ : σ => 1) (symbol adjusted).coord) ∈ _
    rw [hadjusted]
    exact hmid
  · exact F.realification.polynomial_factor_middle_constant
      (fun _ : σ => 1) actual left adjusted right hactual hleft0 hright0

end Erdos3.NilpotentLieFiltration

end

end OAI
