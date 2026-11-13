import Init

/-!+# A semantic obstruction to successor-only transport

This file checks the semantic rule calculations for the counterreading in
`independent_theory.md`. It does not formalize the syntax or derivation trees
of the repository's native calculus, nor a bi-interpretation theorem.

The numerical carrier is the standard natural numbers. The iterator always
returns zero, and the displayed atomic equality is the relation `a = 0`,
independent of its right argument. Successor is the usual successor.

The arbitrary proposition `C` stands for the truth of an unchanged side
context. Quantification over a fresh index or witness is explicit in the
semantic rule premises. No classical axiom is used.
-/

namespace SuccessorSource

def Atomic (a _b : Nat) : Prop := a = 0

def iterator (_n _a : Nat) (_h : Nat → Nat) : Nat := 0

def Closure (B : Nat → Prop) : Prop := B 0 → ∀ n, B n

def Paired (B : Nat → Nat → Prop) : Prop := ∃ x, Closure (B x)

theorem hypothesis {Γ : List Prop} {A : Prop}
    (member : A ∈ Γ) (truth : ∀ B, B ∈ Γ → B) : A :=
  truth A member

theorem computationZero (a : Nat) (h : Nat → Nat) :
    Atomic (iterator 0 a h) a := rfl

theorem computationSucc (n a : Nat) (h : Nat → Nat) :
    Atomic (iterator (Nat.succ n) a h) (h (iterator n a h)) := rfl

theorem successorMajorFalse (r t : Nat) : ¬ Atomic (Nat.succ r) t :=
  fun h => Nat.noConfusion h

theorem ordinaryTransport {C : Prop} (r t : Nat) (F : Nat → Prop)
    (major : C → Atomic (Nat.succ r) t)
    (_minor : C → F (Nat.succ r)) : C → F t := by
  intro hc
  exact False.elim (successorMajorFalse r t (major hc))

theorem crossedTransport {C : Prop} (r t u : Nat) (h : Nat → Nat)
    (major : C → Atomic (Nat.succ r) t)
    (_minor : C → Atomic (h (Nat.succ r)) u) : C → Atomic u (h t) := by
  intro hc
  exact False.elim (successorMajorFalse r t (major hc))

theorem closureElimination {C : Prop} (B : Nat → Prop) (t : Nat)
    (major : C → Closure B) (base : C → B 0) : C → B t := by
  intro hc
  exact major hc (base hc) t

theorem pairedElimination {C A : Prop} (B : Nat → Nat → Prop)
    (major : C → Paired B)
    (branch : ∀ b, C → Closure (B b) → A) : C → A := by
  intro hc
  obtain ⟨b, hb⟩ := major hc
  exact branch b hc hb

theorem casesIntroduction {C : Prop} (B : Nat → Nat → Prop) (w : Nat)
    (step : ∀ z, C → B w 0 → B w (Nat.succ z)) : C → Paired B := by
  intro hc
  refine ⟨w, ?_⟩
  intro hzero n
  cases n with
  | zero => exact hzero
  | succ z => exact step z hc hzero

theorem progressIntroduction {C : Prop} (E : Nat → Prop)
    (step : ∀ z, C → E z → E (Nat.succ z)) : C → Closure E := by
  intro hc hzero n
  induction n with
  | zero => exact hzero
  | succ n ih => exact step n hc ih

theorem witnessedProgress {C : Prop} (E : Nat → Nat → Prop) (w : Nat)
    (step : ∀ z, C → E w z → E w (Nat.succ z)) : C → Paired E := by
  intro hc
  exact ⟨w, progressIntroduction (E w) step hc⟩

theorem reflexivityAtOneIsFalse : ¬ Atomic 1 1 :=
  successorMajorFalse 0 1

/-- An unrestricted transport instance is invalid in this reading.
The two premises are the same zero-computation instance. -/
theorem unrestrictedTransportCounterexample :
    let s := iterator 0 1 (fun _ => 0)
    let F := fun v => Atomic v 1
    Atomic s 1 ∧ F s ∧ ¬ F 1 := by
  exact ⟨rfl, rfl, reflexivityAtOneIsFalse⟩

end SuccessorSource

#print axioms SuccessorSource.computationZero
#print axioms SuccessorSource.computationSucc
#print axioms SuccessorSource.ordinaryTransport
#print axioms SuccessorSource.crossedTransport
#print axioms SuccessorSource.closureElimination
#print axioms SuccessorSource.pairedElimination
#print axioms SuccessorSource.casesIntroduction
#print axioms SuccessorSource.progressIntroduction
#print axioms SuccessorSource.witnessedProgress
#print axioms SuccessorSource.reflexivityAtOneIsFalse
#print axioms SuccessorSource.unrestrictedTransportCounterexample
