import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Residual detection by small rings

Generic algebra for `osq:thm:residual`. Detection is elementwise and does
not assume a small family of detecting maps. Finite polynomials in any
type of variables over a small ring admit such detection.
-/

universe u v w t
namespace Surreal
noncomputable section

/-- Each nonzero element can be detected in some small unital ring in the target universe. -/
def ResiduallySmall (B : Type v) [Ring B] : Prop :=
  ∀ b : B, b ≠ 0 → ∃ (S : Type w) (_ : Ring S), Small.{u} S ∧
    ∃ φ : B →+* S, φ b ≠ 0

namespace ResiduallySmall

/-- In a residually small ring, equality can be tested by all small-target maps. -/
theorem eq_of_observations {B : Type v} [Ring B] (hB : ResiduallySmall.{u, v, w} B)
    {x y : B} (h : ∀ (S : Type w) [Ring S] [Small.{u} S] (φ : B →+* S), φ x = φ y) : x = y := by
  by_contra hn
  obtain ⟨S, inst, hS, φ, hφ⟩ := hB (x - y) (sub_ne_zero.mpr hn)
  letI := inst
  letI := hS
  exact hφ (by rw [map_sub, h S φ, sub_self])

/-- A universal factorization for small targets extends to any residually small target. -/
theorem factors_through_retraction {A : Type v} [Ring A] {D : Type t} [Ring D]
    (r : A →+* D) (s : D →+* A) (hrs : ∀ d, r (s d) = d)
    (hsmall : ∀ (S : Type w) [Ring S] [Small.{u} S] (φ : A →+* S) (x : A),
      φ x = φ (s (r x))) {B : Type*} [Ring B] (hB : ResiduallySmall.{u, _, w} B)
    (φ : A →+* B) : ∃! ψ : D →+* B, ψ.comp r = φ := by
  have he (x : A) : φ x = φ (s (r x)) := by
    apply hB.eq_of_observations
    intro S _ _ π
    exact hsmall S (π.comp φ) x
  refine ⟨φ.comp s, ?_, ?_⟩
  · ext x
    exact (he x).symm
  · intro ψ hψ
    ext d
    have h := RingHom.congr_fun hψ (s d)
    change ψ (r (s d)) = φ (s d) at h
    change ψ d = φ (s d)
    simpa only [hrs] using h

/-- A polynomial is detected by setting all variables outside a suitable finite set to zero. -/
theorem mvPolynomial (E : Type v) [CommRing E] [Small.{u} E] (σ : Type w) :
    ResiduallySmall.{u, max v w, max v w} (MvPolynomial σ E) := by
  classical
  intro p hp
  obtain ⟨s, q, hq⟩ := MvPolynomial.exists_finset_rename p
  let φ : MvPolynomial σ E →+* MvPolynomial s E := MvPolynomial.eval₂Hom MvPolynomial.C
    (fun x => if h : x ∈ s then MvPolynomial.X ⟨x, h⟩ else 0)
  have hφ : φ p = q := by
    rw [hq]
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.rename _ q) = q
    rw [MvPolynomial.eval₂Hom_rename]
    have he : (fun x => if h : x ∈ s then MvPolynomial.X ⟨x, h⟩ else 0) ∘
        (Subtype.val : s → σ) = (MvPolynomial.X : s → MvPolynomial s E) := by
      funext x
      simp only [Function.comp_apply, dif_pos x.property]
    rw [he]
    exact MvPolynomial.eval₂_eta q
  refine ⟨MvPolynomial s E, inferInstance, inferInstance, φ, ?_⟩
  intro hz
  have hq0 : q = 0 := hφ.symm.trans hz
  exact hp (by rw [hq, hq0, map_zero])

end ResiduallySmall
end
end Surreal
