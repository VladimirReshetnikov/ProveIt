/-!
# Formal languages: small semantic companion

STATUS: uncompiled Lean 4 source, not a checked result. Intended for Lean
4.32.0 with Std, matching the inspected ProveIt toolchain. No sorry or
axiom is used in this file, but absence of placeholders is not a build result.

Theorems here are semantic Lean theorems. They do not construct Prf PRAAx
derivations. Finite-state restrictions, numeric encodings, PR expressions,
and object-theory proofs are separate obligations in the outline files.
-/
import Std

namespace FormalLanguages.Semantic

abbrev Word (α : Type) := List α

structure DFA (α σ : Type) where
  start : σ
  step : σ → α → σ
  final : σ → Bool

def runFrom {α σ : Type} (M : DFA α σ) (s : σ) : Word α → σ
  | [] => s
  | a :: w => runFrom M (M.step s a) w

def accepts {α σ : Type} (M : DFA α σ) (w : Word α) : Bool :=
  M.final (runFrom M M.start w)

theorem runFrom_nil {α σ : Type} (M : DFA α σ) (s : σ) :
    runFrom M s [] = s := rfl

theorem runFrom_cons {α σ : Type} (M : DFA α σ) (s : σ)
    (a : α) (w : Word α) :
    runFrom M s (a :: w) = runFrom M (M.step s a) w := rfl

theorem runFrom_append {α σ : Type} (M : DFA α σ) (u v : Word α) (s : σ) :
    runFrom M s (u ++ v) = runFrom M (runFrom M s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih =>
    simpa only [List.cons_append, runFrom] using ih (M.step s a)

def complement {α σ : Type} (M : DFA α σ) : DFA α σ :=
  { M with final := fun s => !(M.final s) }

theorem runFrom_complement {α σ : Type} (M : DFA α σ) (w : Word α) (s : σ) :
    runFrom (complement M) s w = runFrom M s w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simpa only [runFrom, complement] using ih (M.step s a)

theorem accepts_complement {α σ : Type} (M : DFA α σ) (w : Word α) :
    accepts (complement M) w = !(accepts M w) := by
  simp only [accepts, complement, runFrom_complement]

def product {α σ τ : Type} (M : DFA α σ) (N : DFA α τ)
    (combine : Bool → Bool → Bool) : DFA α (σ × τ) where
  start := (M.start, N.start)
  step := fun st a => (M.step st.1 a, N.step st.2 a)
  final := fun st => combine (M.final st.1) (N.final st.2)

theorem runFrom_product {α σ τ : Type} (M : DFA α σ) (N : DFA α τ)
    (combine : Bool → Bool → Bool) (w : Word α) (s : σ) (t : τ) :
    runFrom (product M N combine) (s, t) w =
      (runFrom M s w, runFrom N t w) := by
  induction w generalizing s t with
  | nil => rfl
  | cons a w ih =>
    simpa only [runFrom, product] using ih (M.step s a) (N.step t a)

theorem accepts_product {α σ τ : Type} (M : DFA α σ) (N : DFA α τ)
    (combine : Bool → Bool → Bool) (w : Word α) :
    accepts (product M N combine) w = combine (accepts M w) (accepts N w) := by
  simp only [accepts, product, runFrom_product]

def mapWord {α β : Type} (h : α → Word β) : Word α → Word β
  | [] => []
  | a :: w => h a ++ mapWord h w

theorem mapWord_nil {α β : Type} (h : α → Word β) : mapWord h [] = [] := rfl

theorem mapWord_append {α β : Type} (h : α → Word β) (u v : Word α) :
    mapWord h (u ++ v) = mapWord h u ++ mapWord h v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, mapWord, ih, List.append_assoc]

-- Finite automata use alpha = Fin alphabetSize and sigma = Fin stateCount.
-- Their function fields must then be encoded by finite row-major tables.
-- No claim is made that an arbitrary function field is primitive recursive.

end FormalLanguages.Semantic
