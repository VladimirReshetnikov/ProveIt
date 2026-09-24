import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial solution sets under a ring retraction

Generic algebra for `odg:thm:transfer` and `odg:eq:existencetransfer`.
An arbitrary family of polynomials over the smaller ring has a solution
in the larger ring exactly when it has one in the smaller ring.
-/

namespace Surreal.PolynomialSolutionRetraction

variable {R S ι σ : Type*} [CommRing R] [CommRing S]

/-- Tuples solving a family of polynomials after the indicated coefficient map. -/
def Solutions (p : ι → MvPolynomial σ R) (i : R →+* S) :=
  {x : σ → S // ∀ j, (p j).eval₂ i x = 0}

/-- Retract every coordinate of a solution to the coefficient ring. -/
def retract (p : ι → MvPolynomial σ R) (i : R →+* S) (f : S →+* R)
    (hi : Function.LeftInverse f i) : Solutions p i → Solutions p (RingHom.id R) := fun x =>
  ⟨fun k => f (x.val k), fun j => by
    have hcomp : f.comp i = RingHom.id R := RingHom.ext hi
    have h := congrArg f (x.property j)
    rw [MvPolynomial.hom_eval₂, hcomp, map_zero] at h
    exact h⟩

/-- Include a solution over the coefficient ring into the larger ring. -/
def sectionMap (p : ι → MvPolynomial σ R) (i : R →+* S) :
    Solutions p (RingHom.id R) → Solutions p i := fun x =>
  ⟨fun k => i (x.val k), fun j => by
    have h := congrArg i (x.property j)
    rw [MvPolynomial.hom_eval₂, RingHom.comp_id, map_zero] at h
    exact h⟩

/-- Constant extraction after inclusion is the identity on the entire solution set. -/
theorem leftInverse (p : ι → MvPolynomial σ R) (i : R →+* S) (f : S →+* R)
    (hi : Function.LeftInverse f i) :
    Function.LeftInverse (retract p i f hi) (sectionMap p i) := by
  intro x
  exact Subtype.ext (funext fun k => hi (x.val k))

/-- The solution-set retraction is onto. -/
theorem retract_surjective (p : ι → MvPolynomial σ R) (i : R →+* S) (f : S →+* R)
    (hi : Function.LeftInverse f i) : Function.Surjective (retract p i f hi) :=
  (leftInverse p i f hi).surjective

/-- Existence of solutions is unchanged by a split ring extension. -/
theorem exists_solution_iff (p : ι → MvPolynomial σ R) (i : R →+* S) (f : S →+* R)
    (hi : Function.LeftInverse f i) :
    (∃ x : σ → S, ∀ j, (p j).eval₂ i x = 0) ↔
      ∃ x : σ → R, ∀ j, (p j).eval₂ (RingHom.id R) x = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(retract p i f hi ⟨x, hx⟩).val, (retract p i f hi ⟨x, hx⟩).property⟩
  · rintro ⟨x, hx⟩
    exact ⟨(sectionMap p i ⟨x, hx⟩).val, (sectionMap p i ⟨x, hx⟩).property⟩

end Surreal.PolynomialSolutionRetraction
