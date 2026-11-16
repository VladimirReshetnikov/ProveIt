import Std

/-!
# Finite-use relational certificates: semantic blueprint

This file records the executable host-level definitions underlying the report.
It is not an object-iPRA proof: arbitrary Lean functions in `EvidenceMachine`
are not asserted to be primitive recursive.  The propositions ending in
`Goal` are the exact semantic lemmas to prove before reification.

This file was not compiler-checked in the artifact environment.
-/

namespace IPRAFiniteUse

/-- Boolean bounded existential over `[0, bound)`. -/
def anyBelow (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => anyBelow p n || p n

/-- Boolean bounded universal over `[0, bound)`. -/
def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

/-- Least successful index, or the bound as a sentinel. -/
def firstTrue (p : Nat → Bool) (bound : Nat) : Nat :=
  (List.range bound).find? (fun i => p i) |>.getD bound

structure EvidenceMachine (State : Type) where
  answerBound : Nat → State → Nat
  halt        : Nat → State → Bool
  local       : Nat → State → Nat → Bool
  next        : Nat → State → Nat → State
  post        : Nat → State → Bool

/-- Backward viability for at most `resource` answer steps. -/
def viable {State : Type} (M : EvidenceMachine State) : Nat → State → Bool
  | 0, s => M.halt 0 s && M.post 0 s
  | r + 1, s =>
      if M.halt (r + 1) s then M.post (r + 1) s
      else anyBelow
        (fun a => M.local (r + 1) s a && viable M r (M.next (r + 1) s a))
        (M.answerBound (r + 1) s)

/-- Inductive semantic meaning of a successful finite transcript. -/
inductive Successful {State : Type} (M : EvidenceMachine State) : Nat → State → Prop
  | terminal {r s} : M.halt r s = true → M.post r s = true → Successful M r s
  | answer {r s a} :
      M.halt (r + 1) s = false →
      a < M.answerBound (r + 1) s →
      M.local (r + 1) s a = true →
      Successful M r (M.next (r + 1) s a) →
      Successful M (r + 1) s

/-- Main semantic correctness target. -/
def ViabilityCorrectGoal {State : Type} (M : EvidenceMachine State) : Prop :=
  ∀ r s, viable M r s = true ↔ Successful M r s

/-- The least viable answer when the machine is nonterminal. -/
def choose {State : Type} (M : EvidenceMachine State) (r : Nat) (s : State) : Nat :=
  match r with
  | 0 => 0
  | r' + 1 =>
      firstTrue
        (fun a => M.local (r' + 1) s a && viable M r' (M.next (r' + 1) s a))
        (M.answerBound (r' + 1) s)

/-- Soundness target for the least viable answer. -/
def ChooseSoundGoal {State : Type} (M : EvidenceMachine State) : Prop :=
  ∀ r s,
    viable M (r + 1) s = true →
    M.halt (r + 1) s = false →
    let a := choose M (r + 1) s
    a < M.answerBound (r + 1) s ∧
      M.local (r + 1) s a = true ∧
      viable M r (M.next (r + 1) s a) = true

structure TerminalObservation (State Output : Type) where
  output : State → Output
  equiv  : Output → Output → Prop

/-- Exact branch-invariance target.  Reachability is intentionally an input
predicate here; the object implementation will use a bounded Boolean fold. -/
def ConfluenceGoal {State Output : Type}
    (M : EvidenceMachine State) (O : TerminalObservation State Output)
    (Reach : Nat → State → State → Prop) : Prop :=
  ∀ r s t₁ t₂,
    Reach r s t₁ → Reach r s t₂ →
    M.halt 0 t₁ = true → M.post 0 t₁ = true →
    M.halt 0 t₂ = true → M.post 0 t₂ = true →
    O.equiv (O.output t₁) (O.output t₂)

/-- Quantitative branch stability target. -/
def DiameterGoal {State Output : Type}
    (M : EvidenceMachine State) (output : State → Output)
    (dist : Output → Output → Nat) (delta : Nat)
    (Reach : Nat → State → State → Prop) : Prop :=
  ∀ r s t₁ t₂,
    Reach r s t₁ → Reach r s t₂ →
    M.halt 0 t₁ = true → M.post 0 t₁ = true →
    M.halt 0 t₂ = true → M.post 0 t₂ = true →
    dist (output t₁) (output t₂) ≤ delta

/-- A finite error-DAG node.  All predecessors must have smaller indices. -/
structure ErrorNode where
  local : Nat
  predecessors : List (Nat × Nat)

/-- Specification target for a topological finite-error fold. -/
def ErrorDAGGoal (nodes : List ErrorNode) (budget : Nat → Nat) : Prop :=
  ∀ i, i < nodes.length →
    budget i = (nodes[i]'(by assumption)).local +
      ((nodes[i]'(by assumption)).predecessors.map
        (fun e => e.2 * budget e.1)).sum

end IPRAFiniteUse
