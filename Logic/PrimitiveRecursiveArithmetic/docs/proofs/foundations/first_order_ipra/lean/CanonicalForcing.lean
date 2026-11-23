import Std

/-! Syntactic Kripke semantics for the propositional negative fragment.

Worlds are finite contexts ordered by inclusion. An inconsistent world forces
falsity; this definition allows such worlds without a consistency test. The
forcing/derivability equivalence and canonical completeness are constructive.
This file uses Lean propositions for the infinitary clauses. -/
namespace FirstOrderIPRA.CanonicalForcing

inductive Formula where
  | atom (p : Nat)
  | bottom
  | conj (a b : Formula)
  | impl (a b : Formula)
  deriving DecidableEq, Repr

abbrev World := List Formula

inductive Derives : World → Formula → Prop where
  | hyp {g a} (used : a ∈ g) : Derives g a
  | explode {g a} : Derives g .bottom → Derives g a
  | pair {g a b} : Derives g a → Derives g b → Derives g (.conj a b)
  | left {g a b} : Derives g (.conj a b) → Derives g a
  | right {g a b} : Derives g (.conj a b) → Derives g b
  | abstract {g a b} : Derives (a :: g) b → Derives g (.impl a b)
  | apply {g a b} : Derives g (.impl a b) → Derives g a → Derives g b

theorem weaken {g : World} {a} (h : Derives g a) :
    ∀ {d : World}, g ⊆ d → Derives d a := by
  induction h with
  | hyp h => exact fun ext => .hyp (ext h)
  | explode _ ih => exact fun ext => .explode (ih ext)
  | pair _ _ ihL ihR => exact fun ext => .pair (ihL ext) (ihR ext)
  | left _ ih => exact fun ext => .left (ih ext)
  | right _ ih => exact fun ext => .right (ih ext)
  | abstract _ ih =>
    intro d ext
    apply Derives.abstract
    exact ih (List.cons_subset_cons _ ext)
  | apply _ _ ihL ihR => exact fun ext => .apply (ihL ext) (ihR ext)

private theorem extendContext {g : World} (a : Formula) : g ⊆ a :: g :=
  fun _ h => List.mem_cons_of_mem _ h

theorem replacePremises {g : World} {a} (h : Derives g a) :
    ∀ {d : World}, (∀ b ∈ g, Derives d b) → Derives d a := by
  induction h with
  | hyp h => exact fun replace => replace _ h
  | explode _ ih => exact fun replace => .explode (ih replace)
  | pair _ _ ihL ihR => exact fun replace => .pair (ihL replace) (ihR replace)
  | left _ ih => exact fun replace => .left (ih replace)
  | right _ ih => exact fun replace => .right (ih replace)
  | abstract _ ih =>
    intro d replace
    apply Derives.abstract
    apply ih
    intro b hb
    rcases List.mem_cons.mp hb with head | tail
    · exact .hyp (List.mem_cons.mpr (Or.inl head))
    · exact weaken (replace _ tail) (extendContext _)
  | apply _ _ ihL ihR => exact fun replace => .apply (ihL replace) (ihR replace)

def Forces (g : World) : Formula → Prop
  | .atom p => Derives g (.atom p)
  | .bottom => Derives g .bottom
  | .conj a b => Forces g a ∧ Forces g b
  | .impl a b => ∀ d : World, g ⊆ d → Forces d a → Forces d b

theorem truth (a : Formula) : ∀ g, Forces g a ↔ Derives g a := by
  induction a with
  | atom p => exact fun _ => Iff.rfl
  | bottom => exact fun _ => Iff.rfl
  | conj a b ia ib =>
    intro g
    constructor
    · intro h
      exact .pair ((ia g).mp h.1) ((ib g).mp h.2)
    · intro h
      exact ⟨(ia g).mpr (.left h), (ib g).mpr (.right h)⟩
  | impl a b ia ib =>
    intro g
    constructor
    · intro h
      apply Derives.abstract
      apply (ib (a :: g)).mp
      exact h (a :: g) (extendContext _) ((ia _).mpr (.hyp (by simp)))
    · intro deriv d ext forced
      apply (ib d).mpr
      exact .apply (weaken deriv ext) ((ia d).mp forced)

theorem persistent {g d : World} {a} (ext : g ⊆ d) (h : Forces g a) : Forces d a :=
  (truth a d).mpr (weaken ((truth a g).mp h) ext)

theorem explodingWorld {g : World} (h : Forces g .bottom) (a : Formula) : Forces g a :=
  (truth a g).mpr (.explode h)

def Entails (premises : World) (a : Formula) : Prop :=
  ∀ d : World, (∀ b ∈ premises, Forces d b) → Forces d a

theorem canonical_completeness (g : World) (a : Formula) :
    Entails g a ↔ Derives g a := by
  constructor
  · intro valid
    apply (truth a g).mp
    exact valid g (fun b hb => (truth b g).mpr (.hyp hb))
  · intro deriv d h
    exact (truth a d).mpr (replacePremises deriv (fun b hb => (truth b d).mp (h b hb)))

end FirstOrderIPRA.CanonicalForcing
