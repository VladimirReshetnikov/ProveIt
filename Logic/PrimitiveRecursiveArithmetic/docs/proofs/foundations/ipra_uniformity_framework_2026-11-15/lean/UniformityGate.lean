/-!
Native Lean 4 seed: all claims below concern finite lists and Boolean data.
No assertion of object-level `Prf PRAAx` is made here.
No imports are needed beyond Lean's prelude.
-/
namespace UniformityGate

def hits (w : Nat → Bool) (xs : List Nat) : List Nat := xs.filter (fun x => w x)

theorem mem_hits_iff (w : Nat → Bool) (xs : List Nat) (x : Nat) :
    x ∈ hits w xs ↔ x ∈ xs ∧ w x = true := by
  simp [hits]

theorem hits_sound (w : Nat → Bool) (xs : List Nat) (x : Nat)
    (h : x ∈ hits w xs) : w x = true :=
  (mem_hits_iff w xs x).mp h |>.2

theorem hits_complete (w : Nat → Bool) (xs : List Nat) (x : Nat)
    (hin : x ∈ xs) (hw : w x = true) : x ∈ hits w xs :=
  (mem_hits_iff w xs x).mpr ⟨hin, hw⟩

/- A finite frontier tree with a syntactic rank; `check` is a Boolean
   proof certificate, not a proposition asserted without a certificate. -/
inductive Tree where
  | leaf (value : Bool)
  | node (children : List Tree)
  deriving Repr

def Tree.eval : Tree → Bool
  | .leaf b => b
  | .node cs => cs.all Tree.eval

theorem eval_leaf (b : Bool) : (Tree.leaf b).eval = b := rfl

/- Object iPRA target (not asserted here): a primitive-recursive fold on
   bounded coded frontiers, together with the QF-induction proof rule. -/
end UniformityGate
