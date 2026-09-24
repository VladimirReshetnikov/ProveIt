import Surreal.Algebra.QuantifierFreeFiniteCofinite
import Surreal.Algebra.RetractionInfiniteSets
import Mathlib.ModelTheory.Satisfiability

/-!
# Quantifier-free obstructions for a split retraction

The generic form of `odg:def:prop:notqf`. The coefficient image and the
nontrivial kernel are infinite and coinfinite, so even arbitrary parameters
do not permit quantifier-free definitions. A formula defining either set
has no quantifier-free equivalent modulo the complete theory.
-/

namespace Surreal.QuantifierFree
open FirstOrder FirstOrder.Language

variable {R O : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing O] [CharZero O] [FirstOrder.Ring.CompatibleRing R]

/-- A nontrivial constant-term kernel has no quantifier-free definition with any parameter family. -/
theorem kernel_not_definable₁ (ct : R →+* O) {w : R} (hw : w ≠ 0) (hct : ct w = 0)
    {P : Type*} (p : P → R) : ¬ Definable₁ p {x : R | ct x = 0} :=
  not_definable₁ p (RetractionInfiniteSets.kernel_infinite ct hw hct)
    (RetractionInfiniteSets.kernel_complement_infinite ct)

/-- The ordinary coefficient image likewise has no quantifier-free definition with any parameters. -/
theorem constants_not_definable₁ (ct : R →+* O) (i : O →+* R) (hi : ∀ a, ct (i a) = a)
    {w : R} (hw : w ≠ 0) (hct : ct w = 0) {P : Type*} (p : P → R) :
    ¬ Definable₁ p (Set.range i) :=
  not_definable₁ p (RetractionInfiniteSets.constants_infinite ct i hi)
    (RetractionInfiniteSets.constants_complement_infinite ct i hi hw hct)

omit [IsDomain R] [CharZero R] in
/-- A parameter-free unary quantifier-free formula is in particular a definition with empty parameters. -/
theorem definable₁_of_formula {S : Set R} {φ : Language.ring.Formula (Fin 1)} (hφ : φ.IsQF)
    (hS : ∀ x : R, φ.Realize (fun _ => x) ↔ x ∈ S) :
    Definable₁ (Empty.elim : Empty → R) S := by
  refine ⟨φ.relabel Sum.inr, hφ.relabel (Sum.inl ∘ Sum.inr), ?_⟩
  intro x
  simpa only [Formula.realize_relabel, Sum.elim_comp_inr] using hS x

/-- An infinite coinfinite definable set witnesses failure of quantifier elimination in the
complete theory, expressed using native semantic consequence and native quantifier-free syntax. -/
theorem no_quantifierFree_equivalent_in_completeTheory {S : Set R}
    (hS : S.Infinite) (hSc : Sᶜ.Infinite) (δ : Language.ring.Formula (Fin 1))
    (hδ : ∀ x : R, δ.Realize (fun _ => x) ↔ x ∈ S) :
    ¬ ∃ ψ : Language.ring.Formula (Fin 1), ψ.IsQF ∧
      Language.ring.completeTheory R ⊨ᵇ δ.iff ψ := by
  rintro ⟨ψ, hψ, he⟩
  apply not_definable₁ (Empty.elim : Empty → R) hS hSc
  apply definable₁_of_formula hψ
  intro x
  have h := Formula.realize_iff.mp (he.realize_formula R (v := fun _ => x))
  exact h.symm.trans (hδ x)

end Surreal.QuantifierFree
