import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem prod_range_le_uniform_pow (K : ℕ → ℕ) (K0 n : ℕ)
    (hK : ∀ j < n, K j ≤ K0) :
    (∏ j ∈ Finset.range n, K j) ≤ K0 ^ n := by
  calc
    _ ≤ ∏ _j ∈ Finset.range n, K0 :=
      Finset.prod_le_prod (fun j hj => hK j (Finset.mem_range.mp hj))
    _ = K0 ^ n := by simp

theorem sum_graded_sizes_le (depth K0 : ℕ) (sizes : Fin (depth + 1) → ℕ)
    (hsizes : ∀ j, sizes j ≤ K0 ^ j.val) :
    (∑ j, sizes j) ≤ (depth + 1) * (max 1 K0) ^ depth := by
  calc
    _ ≤ ∑ _j : Fin (depth + 1), (max 1 K0) ^ depth := by
      apply Finset.sum_le_sum
      intro j _
      exact (hsizes j).trans
        ((pow_le_pow_left' (le_max_right 1 K0) j.val).trans
          (pow_le_pow_right' (le_max_left 1 K0) (Nat.le_of_lt_succ j.isLt)))
    _ = (depth + 1) * (max 1 K0) ^ depth := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def finiteGradedBranchLevel {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) :
    ∀ n, Finset (State n)
  | 0 => {initial}
  | n + 1 => (finiteGradedBranchLevel initial children n).biUnion (children n)

@[simp] theorem finiteGradedBranchLevel_mem_zero {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) (x : State 0) :
    x ∈ finiteGradedBranchLevel initial children 0 ↔ x = initial := by
  exact Finset.mem_singleton

theorem finiteGradedBranchLevel_mem_succ {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (n : ℕ) (x : State (n + 1)) :
    x ∈ finiteGradedBranchLevel initial children (n + 1) ↔
      ∃ y ∈ finiteGradedBranchLevel initial children n, x ∈ children n y :=
  Finset.mem_biUnion

theorem finiteGradedBranchLevel_child_mem {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    {n : ℕ} {y : State n} {x : State (n + 1)}
    (hy : y ∈ finiteGradedBranchLevel initial children n) (hx : x ∈ children n y) :
    x ∈ finiteGradedBranchLevel initial children (n + 1) :=
  (finiteGradedBranchLevel_mem_succ initial children n x).mpr ⟨y, hy, hx⟩

theorem finiteGradedBranchLevel_card_le_product {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (K : ℕ → ℕ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      (children n x).card ≤ K n) :
    ∀ n, n ≤ depth → (finiteGradedBranchLevel initial children n).card ≤
      ∏ j ∈ Finset.range n, K j := by
  intro n
  induction n with
  | zero =>
    intro _
    change ({initial} : Finset (State 0)).card ≤ ∏ j ∈ Finset.range 0, K j
    simp
  | succ n ih =>
    intro hn
    have hnd : n < depth := Nat.lt_of_succ_le hn
    change ((finiteGradedBranchLevel initial children n).biUnion (children n)).card ≤ _
    calc
      _ ≤ ∑ x ∈ finiteGradedBranchLevel initial children n, (children n x).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ finiteGradedBranchLevel initial children n, K n :=
        Finset.sum_le_sum (fun x hx => hcard n hnd x hx)
      _ = (finiteGradedBranchLevel initial children n).card * K n := by simp
      _ ≤ (∏ j ∈ Finset.range n, K j) * K n :=
        Nat.mul_le_mul_right _ (ih (Nat.le_of_lt hnd))
      _ = ∏ j ∈ Finset.range (n + 1), K j := (Finset.prod_range_succ K n).symm

theorem finiteGradedBranchLevel_all_valid {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (valid : ∀ n, State n → Prop) (hinit : valid 0 initial)
    (hstep : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      valid n x → ∀ y ∈ children n x, valid (n + 1) y) :
    ∀ n, n ≤ depth → ∀ x ∈ finiteGradedBranchLevel initial children n, valid n x := by
  intro n
  induction n with
  | zero =>
    intro _ x hx
    have he := (finiteGradedBranchLevel_mem_zero initial children x).mp hx
    simpa only [he] using hinit
  | succ n ih =>
    intro hn x hx
    obtain ⟨y, hy, hxy⟩ := (finiteGradedBranchLevel_mem_succ initial children n x).mp hx
    exact hstep n (Nat.lt_of_succ_le hn) y hy (ih (Nat.le_of_succ_le hn) y hy) x hxy

theorem finiteGradedBranchLevel_nonempty {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ)
    (hchild : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      (children n x).Nonempty) :
    (finiteGradedBranchLevel initial children depth).Nonempty := by
  have hall : ∀ n, n ≤ depth → (finiteGradedBranchLevel initial children n).Nonempty := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨initial, (finiteGradedBranchLevel_mem_zero initial children initial).mpr rfl⟩
    | succ n ih =>
      intro hn
      obtain ⟨x, hx⟩ := ih (Nat.le_of_succ_le hn)
      obtain ⟨y, hy⟩ := hchild n (Nat.lt_of_succ_le hn) x hx
      exact ⟨y, finiteGradedBranchLevel_child_mem initial children hx hy⟩
  exact hall depth le_rfl

theorem finiteGradedBranchLevel_exists_valid {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (valid : ∀ n, State n → Prop) (hinit : valid 0 initial)
    (hchild : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      valid n x → ∃ y ∈ children n x, valid (n + 1) y) :
    ∃ x ∈ finiteGradedBranchLevel initial children depth, valid depth x := by
  have hall : ∀ n, n ≤ depth → ∃ x ∈ finiteGradedBranchLevel initial children n, valid n x := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨initial, (finiteGradedBranchLevel_mem_zero initial children initial).mpr rfl, hinit⟩
    | succ n ih =>
      intro hn
      obtain ⟨x, hx, hv⟩ := ih (Nat.le_of_succ_le hn)
      obtain ⟨y, hy, hyv⟩ := hchild n (Nat.lt_of_succ_le hn) x hx hv
      exact ⟨y, finiteGradedBranchLevel_child_mem initial children hx hy, hyv⟩
  exact hall depth le_rfl

theorem finiteGradedBranchLevel_card_le_pow {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth K : ℕ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      (children n x).card ≤ K)
    (n : ℕ) (hn : n ≤ depth) :
    (finiteGradedBranchLevel initial children n).card ≤ K ^ n := by
  exact (finiteGradedBranchLevel_card_le_product initial children depth (fun _ => K)
    hcard n hn).trans (prod_range_le_uniform_pow (fun _ => K) K n (fun _ _ => le_rfl))

noncomputable def finiteGradedBranchVertices {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) (depth : ℕ) :
    Finset (Σ n : Fin (depth + 1), State n.val) :=
  Finset.univ.sigma (fun n => finiteGradedBranchLevel initial children n.val)

@[simp] theorem finiteGradedBranchVertices_mem_iff {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (v : Σ n : Fin (depth + 1), State n.val) :
    v ∈ finiteGradedBranchVertices initial children depth ↔
      v.2 ∈ finiteGradedBranchLevel initial children v.1.val := by
  change v ∈ Finset.univ.sigma (fun n : Fin (depth + 1) =>
    finiteGradedBranchLevel initial children n.val) ↔ _
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]

theorem finiteGradedBranchVertices_card_le {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth K : ℕ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      (children n x).card ≤ K) :
    (finiteGradedBranchVertices initial children depth).card ≤
      (depth + 1) * (max 1 K) ^ depth := by
  rw [finiteGradedBranchVertices, Finset.card_sigma]
  apply sum_graded_sizes_le depth K
  intro n
  exact finiteGradedBranchLevel_card_le_pow initial children depth K hcard n.val
    (Nat.le_of_lt_succ n.isLt)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem finiteGradedBranchLevel_card_le_exp_sum {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (logCap : ℕ → ℝ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      ((children n x).card : ℝ) ≤ Real.exp (logCap n)) :
    ∀ n, n ≤ depth → ((finiteGradedBranchLevel initial children n).card : ℝ) ≤
      Real.exp (∑ j ∈ Finset.range n, logCap j) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [finiteGradedBranchLevel]
  | succ n ih =>
    intro hn
    have hnd : n < depth := Nat.lt_of_succ_le hn
    change (((finiteGradedBranchLevel initial children n).biUnion (children n)).card : ℝ) ≤ _
    calc
      _ ≤ ((∑ x ∈ finiteGradedBranchLevel initial children n, (children n x).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ x ∈ finiteGradedBranchLevel initial children n, ((children n x).card : ℝ) := by
        simp only [Nat.cast_sum]
      _ ≤ ∑ _x ∈ finiteGradedBranchLevel initial children n, Real.exp (logCap n) :=
        Finset.sum_le_sum (fun x hx => hcard n hnd x hx)
      _ = ((finiteGradedBranchLevel initial children n).card : ℝ) * Real.exp (logCap n) := by
        simp [nsmul_eq_mul]
      _ ≤ Real.exp (∑ j ∈ Finset.range n, logCap j) * Real.exp (logCap n) :=
        mul_le_mul_of_nonneg_right (ih (Nat.le_of_lt hnd)) (Real.exp_nonneg _)
      _ = Real.exp (∑ j ∈ Finset.range (n + 1), logCap j) := by
        rw [Finset.sum_range_succ, Real.exp_add]

theorem finiteGradedBranchVertices_card_le_sum_exp_prefixes {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (logCap : ℕ → ℝ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      ((children n x).card : ℝ) ≤ Real.exp (logCap n))
    (n : ℕ) (hn : n ≤ depth) :
    ((finiteGradedBranchVertices initial children n).card : ℝ) ≤
      ∑ j ∈ Finset.range (n + 1), Real.exp (∑ k ∈ Finset.range j, logCap k) := by
  rw [finiteGradedBranchVertices, Finset.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ j : Fin (n + 1), Real.exp (∑ k ∈ Finset.range j.val, logCap k) := by
      apply Finset.sum_le_sum
      intro j _
      exact finiteGradedBranchLevel_card_le_exp_sum initial children depth logCap hcard
        j.val ((Nat.le_of_lt_succ j.isLt).trans hn)
    _ = ∑ j ∈ Finset.range (n + 1), Real.exp (∑ k ∈ Finset.range j, logCap k) :=
      Fin.sum_univ_eq_sum_range
        (fun j => Real.exp (∑ k ∈ Finset.range j, logCap k)) (n + 1)

theorem finiteGradedBranchVertices_card_le_mul_exp_sum {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (logCap : ℕ → ℝ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      ((children n x).card : ℝ) ≤ Real.exp (logCap n))
    (hnonneg : ∀ j, j < depth → 0 ≤ logCap j)
    (n : ℕ) (hn : n ≤ depth) :
    ((finiteGradedBranchVertices initial children n).card : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * Real.exp (∑ j ∈ Finset.range n, logCap j) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), Real.exp (∑ k ∈ Finset.range j, logCap k) :=
      finiteGradedBranchVertices_card_le_sum_exp_prefixes initial children depth logCap hcard n hn
    _ ≤ ∑ _j ∈ Finset.range (n + 1), Real.exp (∑ k ∈ Finset.range n, logCap k) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.exp_le_exp.mpr
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      · intro k hk _
        exact hnonneg k ((Finset.mem_range.mp hk).trans_le hn)
    _ = ((n + 1 : ℕ) : ℝ) * Real.exp (∑ j ∈ Finset.range n, logCap j) := by
      simp [nsmul_eq_mul]

end Erdos3

end

end OAI
