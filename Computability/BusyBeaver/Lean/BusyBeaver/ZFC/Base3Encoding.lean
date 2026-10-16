import Lean.Elab.Tactic.Omega

/-!
Freshness for the finite named-variable part of the experimental base-3 codec.
This file uses Lean's distributed arithmetic tactic, without Mathlib.

The runtime also admits code0 as a cyclic truth alias.  There is deliberately
no Truth constructor here: `Imp(0,0)=0` would make a naive extension collide.
These results do not decode arbitrary naturals, prove codec injectivity, or
calibrate the 252-state candidate with any consistency statement.
-/

namespace SetTheory.BusyBeaver.ZFC.Base3Encoding

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

/-- The dual Cantor pairing used by the unchanged proof/stack representation. -/
def pair (a b : Nat) : Nat := triangle (a + b) + b

theorem le_triangle (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [triangle]; omega

theorem sum_le_pair (a b : Nat) : a + b ≤ pair a b := by
  have h := le_triangle (a + b)
  unfold pair
  omega

inductive Formula where
  | mem : Nat → Nat → Formula
  | imp : Formula → Formula → Formula
  | all : Nat → Formula → Formula
  deriving DecidableEq, Repr

def code : Formula → Nat
  | .mem i j => 3 * pair i j + 1
  | .imp p q => 3 * pair (code p) (code q)
  | .all i p => 3 * pair i (code p) + 2

/-- Includes labels on binders as well as on atomic membership formulas. -/
def labels : Formula → List Nat
  | .mem i j => [i, j]
  | .imp p q => labels p ++ labels q
  | .all i p => i :: labels p

theorem code_pos (p : Formula) : 0 < code p := by
  induction p with
  | mem i j => simp only [code]; omega
  | imp p q hp hq =>
      have h := sum_le_pair (code p) (code q)
      simp only [code]
      omega
  | all i p hp => simp only [code]; omega

theorem left_code_lt_imp (p q : Formula) : code p < code (.imp p q) := by
  have hp := code_pos p
  have hq := code_pos q
  have h := sum_le_pair (code p) (code q)
  simp only [code]
  omega

theorem right_code_lt_imp (p q : Formula) : code q < code (.imp p q) := by
  have hp := code_pos p
  have hq := code_pos q
  have h := sum_le_pair (code p) (code q)
  simp only [code]
  omega

theorem body_code_lt_all (i : Nat) (p : Formula) : code p < code (.all i p) := by
  have h := sum_le_pair i (code p)
  simp only [code]
  omega

theorem label_lt_code (p : Formula) (i : Nat) (h : i ∈ labels p) : i < code p := by
  induction p with
  | mem a b =>
      have hp := sum_le_pair a b
      simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [code]
      rcases h with h | h <;> omega
  | imp p q hp hq =>
      have hleft := left_code_lt_imp p q
      have hright := right_code_lt_imp p q
      simp only [labels, List.mem_append] at h
      rcases h with h | h
      · have hi := hp h; omega
      · have hi := hq h; omega
  | all a p hp =>
      have hpair := sum_le_pair a (code p)
      have hbody := body_code_lt_all a p
      simp only [labels, List.mem_cons] at h
      rcases h with h | h
      · simp only [code]; omega
      · have hi := hp h; omega

/-- The numerical formula code itself is safe as a fresh binder label. -/
theorem code_not_mem_labels (p : Formula) : code p ∉ labels p := by
  intro h
  have hi := label_lt_code p (code p) h
  omega

theorem label_ne_code (p : Formula) (i : Nat) (h : i ∈ labels p) : i ≠ code p := by
  have hi := label_lt_code p i h
  omega

theorem mem_tag (i j : Nat) : code (.mem i j) % 3 = 1 := by
  simp only [code]
  omega

theorem imp_tag (p q : Formula) : code (.imp p q) % 3 = 0 := by
  simp only [code]
  omega

theorem all_tag (i : Nat) (p : Formula) : code (.all i p) % 3 = 2 := by
  simp only [code]
  omega

#print axioms label_lt_code
#print axioms code_not_mem_labels

end SetTheory.BusyBeaver.ZFC.Base3Encoding
