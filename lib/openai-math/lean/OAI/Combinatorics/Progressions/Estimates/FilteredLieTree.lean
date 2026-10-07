import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence

namespace OAI

section

namespace Erdos3

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

inductive FilteredLieTree (F : NilpotentLieFiltration L s) : ℕ → ℕ → Type u where
  | leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) : FilteredLieTree F d 1
  | bracket {d e r t : ℕ} (a : FilteredLieTree F d r) (b : FilteredLieTree F e t) :
      FilteredLieTree F (d + e) (r + t)

namespace FilteredLieTree

variable {F : NilpotentLieFiltration L s}

def eval : {d r : ℕ} → FilteredLieTree F d r → L
  | _, _, .leaf _ x _ => x
  | _, _, .bracket a b => ⁅eval a, eval b⁆

@[simp] theorem eval_leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) :
    eval (leaf hd x hx) = x := rfl

@[simp] theorem eval_bracket {d e r t : ℕ} (a : FilteredLieTree F d r)
    (b : FilteredLieTree F e t) : eval (bracket a b) = ⁅eval a, eval b⁆ := rfl

theorem rank_pos {d r : ℕ} (a : FilteredLieTree F d r) : 0 < r := by
  induction a with
  | leaf hd x hx => omega
  | bracket a b ha hb => omega

theorem rank_le_degree {d r : ℕ} (a : FilteredLieTree F d r) : r ≤ d := by
  induction a with
  | leaf hd x hx => omega
  | bracket a b ha hb => omega

theorem degree_pos {d r : ℕ} (a : FilteredLieTree F d r) : 0 < d :=
  a.rank_pos.trans_le a.rank_le_degree

theorem eval_mem {d r : ℕ} (a : FilteredLieTree F d r) : a.eval ∈ F.layer d := by
  induction a with
  | leaf hd x hx => exact hx
  | bracket a b ha hb => exact F.lie_mem ha hb

theorem eval_eq_zero_of_degree_gt {d r : ℕ} (a : FilteredLieTree F d r) (hd : s < d) :
    a.eval = 0 := by
  have h := F.antitone (show s + 1 ≤ d by omega) a.eval_mem
  simpa only [F.terminal, Submodule.mem_bot] using h

end FilteredLieTree

end Erdos3

end

end OAI
