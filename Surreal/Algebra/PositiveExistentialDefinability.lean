import Surreal.Algebra.PositiveExistentialRetraction

/-!
# Positive-existential definability and fixed-parameter endomorphisms

The general logical obstruction in `odg:def:thm:collapse`. Parameters are
indexed by a type and interpreted by a fixed family; each native formula
uses only finitely many. All syntax and semantics are Mathlib's own.
-/

namespace Surreal
open FirstOrder FirstOrder.Language

variable {L : Language} {M P σ : Type*} [L.Structure M]

/-- Definability by a positive-existential native formula with the given parameter family. -/
def PositiveExistentialDefinable (L : Language) {M P σ : Type*} [L.Structure M]
    (p : P → M) (D : Set (σ → M)) : Prop :=
  ∃ φ : L.Formula (P ⊕ σ), IsPositiveExistential φ ∧
    ∀ x : σ → M, φ.Realize (Sum.elim p x) ↔ x ∈ D

/-- Every endomorphism fixing the allowed parameters preserves the definable tuple set. -/
theorem PositiveExistentialDefinable.endomorphism_closed {p : P → M} {D : Set (σ → M)}
    (hD : PositiveExistentialDefinable L p D) (f : M →[L] M)
    (hp : ∀ a, f (p a) = p a) {x : σ → M} (hx : x ∈ D) : (f ∘ x) ∈ D := by
  obtain ⟨φ, hφ, h⟩ := hD
  have ht := hφ.realize_hom f (xs := default) ((h x).mpr hx)
  have hv : f ∘ Sum.elim p x = Sum.elim p (f ∘ x) := by
    funext a
    cases a with
    | inl a => exact hp a
    | inr a => rfl
  have he : f ∘ (default : Fin 0 → M) = default := Subsingleton.elim _ _
  rw [hv, he] at ht
  exact (h _).mp ht

/-- One point leaving a set under a fixed-parameter endomorphism obstructs its definition. -/
theorem not_positiveExistentialDefinable_of_endomorphism {p : P → M} {D : Set M}
    (f : M →[L] M) (hp : ∀ a, f (p a) = p a) {x : M}
    (hx : x ∈ D) (hfx : f x ∉ D) :
    ¬ PositiveExistentialDefinable L p {v : Fin 1 → M | v 0 ∈ D} := by
  intro hD
  exact hfx (hD.endomorphism_closed f hp (x := fun _ => x) hx)

/-- The parameter restriction is essential: a singleton is positively defined using that point. -/
theorem singleton_positiveExistentialDefinable (a : M) :
    PositiveExistentialDefinable L (fun _ : Unit => a) {v : Fin 1 → M | v 0 = a} := by
  refine ⟨(Term.var (Sum.inr 0)).equal (Term.var (Sum.inl ())), .equal _ _, ?_⟩
  intro x
  simp

section Ring
variable {R O : Type*} [CommRing R] [CommRing O] [FirstOrder.Ring.CompatibleRing R]

omit [FirstOrder.Ring.CompatibleRing R] in
/-- A nonzero kernel element cannot belong to the image of the section. -/
theorem retraction_kernel_not_mem_range (ct : R →+* O) (i : O →+* R)
    (hi : ∀ a, ct (i a) = a) {x : R} (hx : x ≠ 0) (hct : ct x = 0) :
    x ∉ Set.range i := by
  rintro ⟨a, ha⟩
  have ha0 : a = 0 := (hi a).symm.trans ((congrArg ct ha).trans hct)
  apply hx
  rw [← ha, ha0, map_zero]

/-- A split ring retraction obstructs every positive-existential definition containing a
kernel point and excluding zero, with all coefficient parameters allowed. -/
theorem not_positiveExistentialDefinable_of_retraction (ct : R →+* O) (i : O →+* R)
    (hi : ∀ a, ct (i a) = a) {D : Set R} {x : R}
    (hx : x ∈ D) (hct : ct x = 0) (hzero : (0 : R) ∉ D) :
    ¬ PositiveExistentialDefinable Language.ring i {v : Fin 1 → R | v 0 ∈ D} := by
  apply not_positiveExistentialDefinable_of_endomorphism (ringLanguageHom (i.comp ct))
    (fun a => congrArg i (hi a)) hx
  change i (ct x) ∉ D
  simpa only [hct, map_zero] using hzero

end Ring
end Surreal
