/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.MvPolynomial.Rename
import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradedCoefficientBound
import OAI.Combinatorics.Progressions.Lattices.IntegerFrozenChart

namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_zero_eq_killCompl (keep : I → Prop) :
    freezePolynomial keep (0 : {i // ¬keep i} → R) =
      MvPolynomial.killCompl (f := (Subtype.val : {i // keep i} → I)) Subtype.val_injective := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  simp only [freezePolynomial, MvPolynomial.killCompl, aeval_X]
  by_cases hi : keep i
  · have hr : i ∈ Set.range (Subtype.val : {i // keep i} → I) := ⟨⟨i, hi⟩, rfl⟩
    simp only [frozenCoordinate, dite_eq_left hi, dite_eq_left hr]
    congr 1
    exact (Equiv.ofInjective_symm_apply Subtype.val_injective ⟨i, hi⟩).symm
  · have hr : i ∉ Set.range (Subtype.val : {i // keep i} → I) := by
      rintro ⟨⟨j, hj⟩, rfl⟩
      exact hi hj
    simp only [frozenCoordinate, dite_eq_right hi, dite_eq_right hr, Pi.zero_apply, map_zero]

theorem coeff_freezePolynomial_zero (keep : I → Prop) (P : MvPolynomial I R)
    (α : {i // keep i} →₀ ℕ) :
    (freezePolynomial keep (0 : {i // ¬keep i} → R) P).coeff α =
      P.coeff (α.mapDomain Subtype.val) := by
  rw [freezePolynomial_zero_eq_killCompl]
  exact MvPolynomial.coeff_killCompl Subtype.val_injective

theorem coeff_aeval_frozenCoordinate_zero (keep : I → Prop) (P : MvPolynomial I R)
    (α : {i // keep i} →₀ ℕ) :
    (aeval (frozenCoordinate keep (0 : {i // ¬keep i} → R)) P).coeff α =
      P.coeff (α.mapDomain Subtype.val) :=
  coeff_freezePolynomial_zero keep P α

end Erdos3

end

section

namespace Erdos3
open Module
open scoped Classical

namespace VectorPolynomial

variable {I ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem coordinate_coeff_realChartSubstitute_freeze_zero
    (keep : I → Prop) (b : Basis ι ℝ V) (P : VectorPolynomial I ℚ V)
    (α : {i // keep i} →₀ ℕ) (i : ι) :
    b.repr (coefficients (realChartSubstitute (frozenCoordinate keep 0) P) α) i =
      b.repr (coefficients P (α.mapDomain Subtype.val)) i := by
  have h := congrArg (fun Q : MvPolynomial {i // keep i} ℝ => Q.coeff α)
    (coordinate_realChartSubstitute_for_grid (frozenCoordinate keep 0) (b.coord i) P)
  rw [coeff_aeval_frozenCoordinate_zero] at h
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply] using h

theorem CoefficientBound.freeze_zero
    (keep : I → Prop) (b : Basis ι ℝ V) (T : I → ℝ) {M : ℝ}
    {P : VectorPolynomial I ℚ V} (hP : CoefficientBound b T M P) :
    CoefficientBound b (fun i : {i // keep i} => T i.val) M
      (Erdos3.VectorPolynomial.realChartSubstitute (frozenCoordinate keep 0) P) := by
  intro α i
  rw [coordinate_coeff_realChartSubstitute_freeze_zero]
  have hscale : monomialScale T (α.mapDomain Subtype.val) =
      monomialScale (fun i : {i // keep i} => T i.val) α :=
    Finsupp.prod_mapDomain_index_inj Subtype.val_injective
  simpa only [hscale] using hP (α.mapDomain Subtype.val) i

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolHomogeneousPullback realGradedSymbolPolynomialHom

variable {I ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolSlowBound_freeze_zero
    (keep : I → Prop) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (E : F.RealPolynomialSymbolGroup (fun _ : I => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ : I => 1) T M E) :
    F.SymbolSlowBound b ω hF (fun _ : {i // keep i} => 1)
      (fun i => T i.val) M
      (F.realSymbolHomogeneousPullbackHom b ω hF (fun _ : I => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
        (frozenCoordinate_zero_homogeneous keep) E) := by
  have hbound : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (F.realGradedSymbolPolynomialHom b ω hF (fun _ : I => 1) E).coord :=
    (F.symbolSlowBound_iff_gradedCoefficientBound b ω hF (fun _ : I => 1)
      T hT hM E).mp hE
  have hfrozen := CoefficientBound.freeze_zero keep
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) T hbound
  exact F.symbolSlowBound_homogeneousPullback_of_coefficientBound b ω hF
    (fun _ : I => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
    (frozenCoordinate_zero_homogeneous keep) E (fun i => T i.val) M hfrozen

end NilpotentLieFiltration
end Erdos3

end

end OAI
