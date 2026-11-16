module
public import PACore
public import Mathlib.Data.Finset.Image
@[expose] public section
/-! Explicit finitary classical first-order sequent proof objects. The theory
parameter is not yet instantiated to PA: no arbitrary/opaque PA predicate is
being advertised as the final Challenge. -/
namespace PalomarPA
/-- Stable proof-calculus equality, independent of generated recursive compiler helpers. -/
noncomputable def calculusFormulaEq : DecidableEq (Formula Nat 0) := Classical.typeDecidableEq _
attribute [local instance] calculusFormulaEq
noncomputable section
abbrev Sequent := Finset (Formula Nat 0)
inductive Derivation (T : Sentence → Prop) : Sequent → Type where
  | closed (Γ) (p : Formula Nat 0) : p ∈ Γ → p.neg ∈ Γ → Derivation T Γ
  | axiom {Γ} (p : Sentence) : T p → p.embed ∈ Γ → Derivation T Γ
  | top {Γ} : Formula.top ∈ Γ → Derivation T Γ
  | and {Γ p q} : Formula.and p q ∈ Γ →
      Derivation T (insert p Γ) → Derivation T (insert q Γ) → Derivation T Γ
  | or {Γ p q} : Formula.or p q ∈ Γ →
      Derivation T (insert p (insert q Γ)) → Derivation T Γ
  | all {Γ} {p : Formula Nat 1} : Formula.all p ∈ Γ →
      Derivation T (insert p.free (Γ.image Formula.shift)) → Derivation T Γ
  | ex {Γ} {p : Formula Nat 1} : Formula.ex p ∈ Γ → (t : Term Nat 0) →
      Derivation T (insert (p.instantiate t) Γ) → Derivation T Γ
  | weaken {Δ Γ} : Derivation T Δ → Δ ⊆ Γ → Derivation T Γ
  | shift {Γ} : Derivation T Γ → Derivation T (Γ.image Formula.shift)
  | cut {Γ p} : Derivation T (insert p Γ) → Derivation T (insert p.neg Γ) → Derivation T Γ

def Provable (T : Sentence → Prop) (p : Sentence) : Prop :=
  Nonempty (Derivation T {p.embed})
end
end PalomarPA
