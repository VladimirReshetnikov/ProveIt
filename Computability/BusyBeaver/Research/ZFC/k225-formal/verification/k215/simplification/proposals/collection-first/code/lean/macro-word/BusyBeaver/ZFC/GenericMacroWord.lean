import BusyBeaver.ZFC.RMDag

/-!
A program-independent checked word of normal-returning register macros.

Prototype for sharing the word machinery currently repeated by L2AxiomsPerm
and L2AxiomsDom. This file does not replace either production theorem.
The source node numbers belong only to `check`; effects depend only on atoms.
-/
namespace SetTheory.BusyBeaver.ZFC.GenericMacroWord
open RMDag

variable {Atom State : Type}

def check (p : Prog) (edge : Atom → Edge) (stop : Nat) :
    Nat → List (Atom × Nat) → Bool
  | n, [] => decide (n = stop)
  | n, (a, next) :: rest =>
      decide (p.nodes n = (edge a, .node next)) && check p edge stop next rest

def eval (effect : Atom → State → State) (finish : State → State) :
    List (Atom × Nat) → State → State
  | [], s => finish s
  | (a, _) :: rest, s => eval effect finish rest (effect a s)

/-- Labels are evidence about placement; their values do not affect semantics. -/
theorem eval_labels (effect : Atom → State → State) (finish : State → State)
    (xs ys : List (Atom × Nat)) (h : xs.map Prod.fst = ys.map Prod.fst) (s : State) :
    eval effect finish xs s = eval effect finish ys s := by
  induction xs generalizing ys s with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          simp only [eval, h.1]
          exact ih ys h.2 _

theorem eval_append (effect : Atom → State → State) (finish : State → State)
    (xs ys : List (Atom × Nat)) (s : State) :
    eval effect finish (xs ++ ys) s = eval effect (eval effect finish ys) xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- An adjacent independent pair can be reordered under every prefix and suffix. -/
theorem eval_swap (effect : Atom → State → State) (finish : State → State)
    (a b : Atom) (hcomm : ∀ s, effect b (effect a s) = effect a (effect b s))
    (xs ys : List (Atom × Nat)) (i j : Nat) (s : State) :
    eval effect finish (xs ++ (a, i) :: (b, j) :: ys) s =
      eval effect finish (xs ++ (b, i) :: (a, j) :: ys) s := by
  induction xs generalizing s with
  | nil => simp only [List.nil_append, eval, hcomm]
  | cons x xs ih => exact ih _

/-- One invariant proof applies to every program using the same effects. -/
theorem eval_preserves (effect : Atom → State → State) (finish : State → State)
    (Inv : State → Prop)
    (ha : ∀ a s, Inv s → Inv (effect a s))
    (hf : ∀ s, Inv s → Inv (finish s))
    (word : List (Atom × Nat)) (s : State) (hs : Inv s) :
    Inv (eval effect finish word s) := by
  induction word generalizing s with
  | nil => exact hf s hs
  | cons x xs ih => exact ih _ (ha x.1 s hs)

/-- The only induction connecting a checked macro word to the DAG semantics. -/
theorem run (p : Prog) (enc : State → Regs) (Inv : State → Prop)
    (edge : Atom → Edge) (effect : Atom → State → State)
    (stop : Nat) (finish : State → State)
    (macro_run : ∀ a s, Inv s → Run p (edge a) (enc s) .normal (enc (effect a s)))
    (macro_inv : ∀ a s, Inv s → Inv (effect a s))
    (finish_run : ∀ s, Inv s → Run p (.node stop) (enc s) .normal (enc (finish s)))
    (word : List (Atom × Nat)) {n : Nat} (checked : check p edge stop n word = true)
    (s : State) (hs : Inv s) :
    Run p (.node n) (enc s) .normal (enc (eval effect finish word s)) := by
  induction word generalizing n s with
  | nil =>
      simp only [check, decide_eq_true_eq] at checked
      subst n
      exact finish_run s hs
  | cons x xs ih =>
      rcases x with ⟨a, next⟩
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact RMDag.seq checked.1 (macro_run a s hs)
        (ih checked.2 _ (macro_inv a s hs))

#print axioms eval_labels
#print axioms eval_swap
#print axioms eval_preserves
#print axioms run
end SetTheory.BusyBeaver.ZFC.GenericMacroWord
