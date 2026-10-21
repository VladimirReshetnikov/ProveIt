/- Standalone Lean proposal, not compiled in this environment.
   No syntactic encoding, injectivity, or semantic-model assumptions. -/
namespace AxiomTransport
universe u v

inductive Closure {A : Type u} {I : Type v} (imp : A → A → A)
    (all : I → A → A) (truth : A) (Ax : A → Prop) : A → Prop
  | ax {a} : Ax a → Closure imp all truth Ax a
  | truth_intro : Closure imp all truth Ax truth
  | mp {a b} : Closure imp all truth Ax a →
      Closure imp all truth Ax (imp a b) → Closure imp all truth Ax b
  | gen (i) {a} : Closure imp all truth Ax a → Closure imp all truth Ax (all i a)

theorem transport {A : Type u} {I : Type v} {imp : A → A → A}
    {all : I → A → A} {truth : A} {Ax Bx : A → Prop}
    (admissible : ∀ a, Ax a → Closure imp all truth Bx a) :
    ∀ {a}, Closure imp all truth Ax a → Closure imp all truth Bx a := by
  intro a h
  induction h with
  | ax h => exact admissible _ h
  | truth_intro => exact .truth_intro
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen i _ ih => exact .gen i ih

theorem same_theorems {A : Type u} {I : Type v} {imp : A → A → A}
    {all : I → A → A} {truth : A} {Ax Bx : A → Prop}
    (forward : ∀ a, Ax a → Closure imp all truth Bx a)
    (backward : ∀ a, Bx a → Closure imp all truth Ax a) (a : A) :
    Closure imp all truth Ax a ↔ Closure imp all truth Bx a :=
  ⟨transport forward, transport backward⟩

end AxiomTransport
