import Surreal.Surcomplex.ComplexEmbedding
import Surreal.Algebra.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Roots of polynomials with ordinary coefficients

The complex and real clauses of `odg:prop:univariate`, in the stronger
form valid on the entire actual fields. Mathlib's algebraic closedness of
ordinary complex numbers and the existing split-polynomial descent theorem
exclude new roots in a larger field. No support restriction is needed here.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A nonzero ordinary complex polynomial has exactly its ordinary roots in the actual field. -/
theorem complex_polynomial_root_iff (P : Polynomial ℂ) (hP : P ≠ 0) (z : Surcomplex.{u}) :
    P.eval₂ ofComplex z = 0 ↔ ∃ c : ℂ, z = ofComplex c ∧ P.eval c = 0 := by
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := FinitePolynomial.root_mem_range P (IsAlgClosed.splits P) hP ofComplex
      (by simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hz)
    refine ⟨c, hc.symm, ?_⟩
    rw [← hc, Polynomial.eval₂_at_apply] at hz
    exact ofComplex.injective (hz.trans (map_zero ofComplex).symm)
  · rintro ⟨c, rfl, hc⟩
    rw [Polynomial.eval₂_at_apply, hc, map_zero]

/-- A nonzero ordinary real polynomial has exactly its ordinary real roots in the surreal field. -/
theorem real_polynomial_root_iff (P : Polynomial ℝ) (hP : P ≠ 0) (x : SignSequence.{u}) :
    P.eval₂ SignSequence.ofReal.toRingHom x = 0 ↔
      ∃ r : ℝ, x = SignSequence.ofReal r ∧ P.eval r = 0 := by
  constructor
  · intro hx
    have hcomp : ofComplex.comp Complex.ofRealHom = ofReal.comp SignSequence.ofReal.toRingHom := by
      apply RingHom.ext
      intro r
      exact ofComplex_ofReal r
    have hz : (P.map Complex.ofRealHom).eval₂ ofComplex (ofReal x) = 0 := by
      rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hx, map_zero]
    obtain ⟨c, hc, _⟩ := (complex_polynomial_root_iff (P.map Complex.ofRealHom)
      ((Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hP) (ofReal x)).mp hz
    have hr : x = SignSequence.ofReal c.re := congrArg QuadraticAlgebra.re hc
    refine ⟨c.re, hr, ?_⟩
    rw [hr] at hx
    change P.eval₂ SignSequence.ofReal.toRingHom
      (SignSequence.ofReal.toRingHom c.re) = 0 at hx
    rw [Polynomial.eval₂_at_apply (p := P) SignSequence.ofReal.{u}.toRingHom c.re] at hx
    exact SignSequence.ofReal_injective (hx.trans (map_zero SignSequence.ofReal).symm)
  · rintro ⟨r, rfl, hr⟩
    change P.eval₂ SignSequence.ofReal.toRingHom (SignSequence.ofReal.toRingHom r) = 0
    rw [Polynomial.eval₂_at_apply (p := P) SignSequence.ofReal.{u}.toRingHom r, hr, map_zero]

end
end Surreal.Surcomplex
