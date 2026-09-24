import Surreal.Algebra.PositiveExistentialRetraction
import Mathlib.ModelTheory.Complexity
import Mathlib.Algebra.Polynomial.Roots

/-!
# Unary quantifier-free ring formulas define finite or cofinite sets

The logical and polynomial prerequisite of `odg:def:prop:notqf`.
Parameters may be arbitrary elements of an integral domain. Ring terms
are evaluated in the native polynomial ring, and polynomial evaluation
commutes with term realization via its ring homomorphism.
-/

namespace Surreal.QuantifierFree
open FirstOrder FirstOrder.Language

variable {R : Type*} [CommRing R] [IsDomain R] [FirstOrder.Ring.CompatibleRing R]

noncomputable local instance polynomialLogicalStructure : FirstOrder.Ring.CompatibleRing (Polynomial R) :=
  FirstOrder.Ring.compatibleRingOfRing (Polynomial R)

omit [FirstOrder.Ring.CompatibleRing R] in
/-- An atomic polynomial zero set is finite, unless the polynomial vanishes identically. -/
theorem polynomial_finite_or_cofinite (p : (Polynomial R)) :
    Set.Finite {x : R | p.eval x = 0} ∨ Set.Finite {x : R | ¬ p.eval x = 0} := by
  by_cases hp : p = 0
  · right
    simp [hp]
  · exact Or.inl (Polynomial.finite_setOf_isRoot hp)

omit [CommRing R] [IsDomain R] [FirstOrder.Ring.CompatibleRing R] in
/-- Finite/cofinite predicates are closed under implication, hence under every Boolean operation. -/
theorem finite_or_cofinite_imp {P Q : R → Prop}
    (hP : Set.Finite {x | P x} ∨ Set.Finite {x | ¬ P x})
    (hQ : Set.Finite {x | Q x} ∨ Set.Finite {x | ¬ Q x}) :
    Set.Finite {x | P x → Q x} ∨ Set.Finite {x | ¬ (P x → Q x)} := by
  classical
  rcases hP with hp | hp
  · exact Or.inr (hp.subset (fun _ hx => (Classical.not_imp.mp hx).1))
  rcases hQ with hq | hq
  · apply Or.inl
    apply (hp.union hq).subset
    intro x hx
    by_cases hpx : P x
    · exact Or.inr (hx hpx)
    · exact Or.inl hpx
  · exact Or.inr (hq.subset (fun _ hx => (Classical.not_imp.mp hx).2))

omit [IsDomain R] in
/-- Ring-term realization commutes with evaluation of its polynomial-valued variables. -/
theorem term_realize_eval {α : Type*} (t : Language.ring.Term α) (v : α → (Polynomial R)) (x : R) :
    t.realize (fun a => (v a).eval x) = (t.realize v).eval x := by
  exact HomClass.realize_term (ringLanguageHom (Polynomial.evalRingHom x))

/-- Quantifier-free realization under arbitrary univariate polynomial assignments is finite/cofinite. -/
theorem finite_or_cofinite_realize {α : Type*} {n : ℕ}
    {φ : Language.ring.BoundedFormula α n} (hφ : φ.IsQF)
    (v : α → (Polynomial R)) (xs : Fin n → (Polynomial R)) :
    Set.Finite {x : R | φ.Realize (fun a => (v a).eval x) (fun j => (xs j).eval x)} ∨
      Set.Finite {x : R | ¬ φ.Realize (fun a => (v a).eval x) (fun j => (xs j).eval x)} := by
  induction hφ with
  | falsum => left; simp [BoundedFormula.Realize]
  | of_isAtomic h =>
    cases h with
    | equal t s =>
      have h := polynomial_finite_or_cofinite (t.realize (Sum.elim v xs) - s.realize (Sum.elim v xs))
      have he (x : R) : Sum.elim (fun a => (v a).eval x) (fun j => (xs j).eval x) =
          (fun a => (Sum.elim v xs a).eval x) := by funext a; cases a <;> rfl
      simpa only [Term.bdEqual, BoundedFormula.Realize, he, term_realize_eval,
        Polynomial.eval_sub, sub_eq_zero] using h
    | rel r ts => cases r
  | imp _ _ ihφ ihψ => exact finite_or_cofinite_imp ihφ ihψ

/-- Native unary quantifier-free definability with an arbitrary parameter family. -/
def Definable₁ {P : Type*} (p : P → R) (S : Set R) : Prop :=
  ∃ φ : Language.ring.Formula (P ⊕ Fin 1), φ.IsQF ∧
    ∀ x : R, φ.Realize (Sum.elim p (fun _ => x)) ↔ x ∈ S

/-- Every unary quantifier-free definition, with any ring parameters, is finite or cofinite. -/
theorem Definable₁.finite_or_cofinite {P : Type*} {p : P → R} {S : Set R}
    (hS : Definable₁ p S) : S.Finite ∨ Sᶜ.Finite := by
  obtain ⟨φ, hφ, h⟩ := hS
  let v : P ⊕ Fin 1 → (Polynomial R) := Sum.elim (fun a => Polynomial.C (p a)) (fun _ => Polynomial.X)
  have hv (x : R) : (fun a => (v a).eval x) = Sum.elim p (fun _ => x) := by
    funext a
    cases a <;> simp [v]
  have hx (x : R) : (fun j => ((default : Fin 0 → (Polynomial R)) j).eval x) = (default : Fin 0 → R) :=
    Subsingleton.elim _ _
  have hf := finite_or_cofinite_realize hφ v default
  simp only [Formula.Realize] at h
  simp only [hv, hx, h] at hf
  exact hf

/-- An infinite set with infinite complement has no unary quantifier-free definition. -/
theorem not_definable₁ {P : Type*} (p : P → R) {S : Set R}
    (hS : S.Infinite) (hSc : Sᶜ.Infinite) : ¬ Definable₁ p S := by
  intro h
  rcases h.finite_or_cofinite with hf | hf
  · exact hS hf
  · exact hSc hf

end Surreal.QuantifierFree
