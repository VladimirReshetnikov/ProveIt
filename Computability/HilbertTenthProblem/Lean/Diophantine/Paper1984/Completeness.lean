import Diophantine.Paper1984.Encoding

/-!
# Completeness: an accepting computation solves the system

If `P` accepts `x` in `s` steps we take `Q = 2^(x+s+l+2)` (the choice made
after (26)), `I = Σ_{t≤s} Q^t`, and the numbers `R_j`, `L_i` of (22)–(23) built
from the trace of the computation, and verify (24)–(39).
-/

namespace JM1984
namespace RM

open Finset

variable {r : ℕ}

/-! ### The trace of a run -/

/-- Register `j` at time `t` (`0` once the run is undefined). -/
def regAt (P : Program r) (x : ℕ) (j : Fin r) (t : ℕ) : ℕ :=
  match run P (init r x) t with
  | some c => c.regs j
  | none => 0

/-- `1` if line `i` is executed at time `t`, else `0`. -/
def linAt (P : Program r) (x : ℕ) (i t : ℕ) : ℕ :=
  match run P (init r x) t with
  | some c => if c.pc = i then 1 else 0
  | none => 0

/-- The value of operand `a` at time `t`. -/
def opdAt (P : Program r) (x : ℕ) (a : Operand r) (t : ℕ) : ℕ :=
  match run P (init r x) t with
  | some c => a.val c.regs
  | none => 0

variable {P : Program r} {x t : ℕ}

theorem regAt_of_eq {c : Config r} (h : run P (init r x) t = some c) (j : Fin r) :
    regAt P x j t = c.regs j := by simp [regAt, h]

theorem linAt_of_eq {c : Config r} (h : run P (init r x) t = some c) (i : ℕ) :
    linAt P x i t = if c.pc = i then 1 else 0 := by simp [linAt, h]

theorem opdAt_of_eq {c : Config r} (h : run P (init r x) t = some c) (a : Operand r) :
    opdAt P x a t = a.val c.regs := by simp [opdAt, h]

theorem regAt_of_none (h : run P (init r x) t = none) (j : Fin r) : regAt P x j t = 0 := by
  simp [regAt, h]

theorem linAt_of_none (h : run P (init r x) t = none) (i : ℕ) : linAt P x i t = 0 := by
  simp [linAt, h]

theorem opdAt_of_none (h : run P (init r x) t = none) (a : Operand r) : opdAt P x a t = 0 := by
  simp [opdAt, h]

theorem linAt_le_one (P : Program r) (x i t : ℕ) : linAt P x i t ≤ 1 := by
  unfold linAt
  split
  · split_ifs <;> omega
  · omega

theorem step_final (hP : WF P) : step P (final P) = none := by
  unfold step
  simp [final, hP.last_stop, Cmd.exec]

theorem run_none_of_gt (hP : WF P) {s : ℕ} (hs : run P (init r x) s = some (final P)) :
    ∀ t, s < t → run P (init r x) t = none := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge s t with h | h
    · rw [run_succ, ih h]; rfl
    · have : t = s := by omega
      subst this
      rw [run_succ_of_eq hs, step_final hP]

/-- The main construction. -/
theorem sys_of_accepts (hP : WF P) (h : Accepts P x) :
    ∃ s Q I R L, Sys P x s Q I R L ∧ Q = 2 ^ (x + s + P.length + 1) := by
  obtain ⟨s, hs⟩ := h
  have hlen : 0 < P.length := hP.pos
  -- the base `Q = 2^q`
  generalize hq : x + s + (P.length - 1) + 2 = q
  have hq2 : 2 ≤ q := by omega
  have hQ4 : 4 ≤ 2 ^ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
  have hQ0 : 0 < 2 ^ q := by omega
  have h24 : 2 * (x + s) < 2 ^ q := by
    calc 2 * (x + s) < 2 * 2 ^ (x + s) := by
          have := Nat.lt_two_pow_self (n := x + s); omega
      _ = 2 ^ (x + s + 1) := by ring
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h25 : P.length < 2 ^ q :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hhalf : x + s < 2 ^ (q - 1) := by
    have := two_mul_two_pow_div_two (q := q) (by omega)
    rw [two_pow_div_two (by omega)] at this
    omega
  -- facts about the run
  have hsome : ∀ t ≤ s, ∃ c, run P (init r x) t = some c := run_isSome_of_le hs
  have hnone : ∀ t, s < t → run P (init r x) t = none := run_none_of_gt hP hs
  have hstep : ∀ t < s, ∀ c, run P (init r x) t = some c →
      ∃ c', run P (init r x) (t + 1) = some c' ∧ step P c = some c' := by
    intro t ht c hc
    obtain ⟨c', hc'⟩ := hsome (t + 1) (by omega)
    exact ⟨c', hc', by rw [← hc', run_succ_of_eq hc]⟩
  have hpc_lt : ∀ t < s, ∀ c, run P (init r x) t = some c →
      c.pc < P.length ∧ P[c.pc]? ≠ some Cmd.stop := by
    intro t ht c hc
    obtain ⟨c', -, hstep'⟩ := hstep t ht c hc
    exact pc_lt_of_step hstep'
  have hpc_ne : ∀ t < s, ∀ c, run P (init r x) t = some c → c.pc ≠ P.length - 1 := by
    intro t ht c hc heq
    have := (hpc_lt t ht c hc).2
    rw [heq] at this
    exact this hP.last_stop
  have hfin_pc : (final P).pc = P.length - 1 := rfl
  have hfin_regs : ∀ j, (final P).regs j = 0 := fun _ => rfl
  have hreg_le : ∀ t c, run P (init r x) t = some c → ∀ j, c.regs j ≤ x + t :=
    fun t c hc j => regs_run_le hP hc j
  have hpc_le : ∀ t ≤ s, ∀ c, run P (init r x) t = some c → c.pc < P.length := by
    intro t ht c hc
    rcases Nat.lt_or_ge t s with h | h
    · exact (hpc_lt t h c hc).1
    · have : t = s := by omega
      subst this
      rw [hs] at hc
      cases hc
      simp [final]; omega
  -- one line at each time
  have huniq : ∀ t ≤ s, ∑ i ∈ range P.length, linAt P x i t = 1 := by
    intro t ht
    obtain ⟨c, hc⟩ := hsome t ht
    simp only [linAt_of_eq hc]
    rw [sum_ite_eq]
    simp [mem_range, hpc_le t ht c hc]
  have hlin_zero : ∀ i t, s < t → linAt P x i t = 0 := fun i t ht => linAt_of_none (hnone t ht) i
  have hreg_zero : ∀ j t, s < t → regAt P x j t = 0 := fun j t ht => regAt_of_none (hnone t ht) j
  -- "line i is executed at time t" for a non-STOP line forces t < s and gives the next config
  have hexec : ∀ i t, P[i]? ≠ some Cmd.stop → linAt P x i t = 1 →
      ∃ c c', run P (init r x) t = some c ∧ c.pc = i ∧ t < s ∧
        run P (init r x) (t + 1) = some c' ∧ step P c = some c' := by
    intro i t hi hl
    have hts : t ≤ s := by
      by_contra hc
      rw [hlin_zero i t (by omega)] at hl
      omega
    obtain ⟨c, hc⟩ := hsome t hts
    rw [linAt_of_eq hc] at hl
    have hpc : c.pc = i := by by_contra hne; rw [if_neg hne] at hl; omega
    have hlt : t < s := by
      rcases Nat.lt_or_ge t s with h | h
      · exact h
      · exfalso
        have : t = s := by omega
        subst this
        rw [hs] at hc
        cases hc
        exact hi (hpc ▸ hP.last_stop)
    obtain ⟨c', hc', hst⟩ := hstep t hlt c hc
    exact ⟨c, c', hc, hpc, hlt, hc', hst⟩
  -- the unknowns
  refine ⟨s, 2 ^ q, blocks (2 ^ q) (s + 1) (fun _ => 1),
    fun j => blocks (2 ^ q) (s + 1) (regAt P x j),
    fun i => blocks (2 ^ q) (s + 1) (linAt P x i), ?_, by rw [← hq]; congr 1; omega⟩
  -- extending block numbers of the trace to `s + 2` blocks
  have hextL : ∀ i, blocks (2 ^ q) (s + 1) (linAt P x i) = blocks (2 ^ q) (s + 2) (linAt P x i) :=
    fun i => (blocks_of_zero_of_ge (by omega) (fun t ht => hlin_zero i t (by omega))).symm
  have hextR : ∀ j, blocks (2 ^ q) (s + 1) (regAt P x j) = blocks (2 ^ q) (s + 2) (regAt P x j) :=
    fun j => (blocks_of_zero_of_ge (by omega) (fun t ht => hreg_zero j t (by omega))).symm
  have hlin_lt : ∀ i t, linAt P x i t < 2 ^ q := fun i t => by have := linAt_le_one P x i t; omega
  -- the fall-through / GO TO condition, for any line `i ≠ l` whose successor is always line `n`
  have hjump : ∀ i n, P[i]? ≠ some Cmd.stop →
      (∀ t c c', run P (init r x) t = some c → c.pc = i → step P c = some c' → c'.pc = n) →
      2 ^ q * blocks (2 ^ q) (s + 1) (linAt P x i) ≼ blocks (2 ^ q) (s + 1) (linAt P x n) := by
    intro i n hi hn
    rw [blocks_shift, hextL n, mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hlin_lt _ _))
      (fun t _ => hlin_lt _ _), forall_lt_succ']
    simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    refine ⟨zero_mask _, fun t _ => ?_⟩
    rw [mask_of_le_one_iff (linAt_le_one _ _ _ _)]
    intro hl
    obtain ⟨c, c', hc, hpc, -, hc', hst⟩ := hexec i t hi hl
    rw [linAt_of_eq hc', if_pos (hn t c c' hc hpc hst)]
  have hts_of : ∀ t c, run P (init r x) t = some c → t ≤ s := by
    intro t c hc
    by_contra h
    rw [hnone t (by omega)] at hc
    cases hc
  -- encoded operands are the block numbers of the operand histories
  have henc : ∀ a : Operand r, Operand.enc (blocks (2 ^ q) (s + 1) fun _ => 1)
      (fun j => blocks (2 ^ q) (s + 1) (regAt P x j)) a = blocks (2 ^ q) (s + 1) (opdAt P x a) := by
    intro a
    cases a with
    | reg j =>
      simp only [Operand.enc]
      apply blocks_congr
      intro t _
      cases hc : run P (init r x) t with
      | none => rw [regAt_of_none hc, opdAt_of_none hc]
      | some c => rw [regAt_of_eq hc, opdAt_of_eq hc]; rfl
    | zero =>
      simp only [Operand.enc]
      rw [← blocks_const_zero (2 ^ q) (s + 1)]
      apply blocks_congr
      intro t _
      cases hc : run P (init r x) t with
      | none => rw [opdAt_of_none hc]
      | some c => rw [opdAt_of_eq hc]; rfl
    | one =>
      simp only [Operand.enc]
      apply blocks_congr
      intro t ht
      obtain ⟨c, hc⟩ := hsome t (by omega)
      rw [opdAt_of_eq hc]; rfl
  have hopd_lt : ∀ a t, 2 * opdAt P x a t < 2 ^ q := by
    intro a t
    cases hc : run P (init r x) t with
    | none => rw [opdAt_of_none hc]; omega
    | some c =>
      rw [opdAt_of_eq hc]
      have hts := hts_of t c hc
      cases a with
      | reg j =>
        simp only [Operand.val]
        have := hreg_le t c hc j
        omega
      | zero => simp only [Operand.val]; omega
      | one => simp only [Operand.val]; omega
  have hopd_le' : ∀ a t, 1 ≤ t → t < s → 2 * opdAt P x a t + 3 ≤ 2 ^ q := by
    intro a t h1 h2
    obtain ⟨c, hc⟩ := hsome t (by omega)
    rw [opdAt_of_eq hc]
    cases a with
    | reg j => simp only [Operand.val]; have := hreg_le t c hc j; omega
    | zero => simp only [Operand.val]; omega
    | one =>
      simp only [Operand.val]
      have : 2 ^ 4 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  -- the first condition of (36)/(37): `Q L_i ≼ L_k + L_{i+1}`
  have hcond1 : ∀ i k, P[i]? ≠ some Cmd.stop → k ≠ i + 1 →
      (∀ t c c', run P (init r x) t = some c → c.pc = i → step P c = some c' →
        c'.pc = k ∨ c'.pc = i + 1) →
      2 ^ q * blocks (2 ^ q) (s + 1) (linAt P x i) ≼
        blocks (2 ^ q) (s + 1) (linAt P x k) + blocks (2 ^ q) (s + 1) (linAt P x (i + 1)) := by
    intro i k hi hk hn
    rw [blocks_shift, hextL k, hextL (i + 1), ← blocks_add,
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hlin_lt _ _))
        (fun t _ => by
          have := linAt_le_one P x k t; have := linAt_le_one P x (i + 1) t; omega),
      forall_lt_succ']
    simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    refine ⟨zero_mask _, fun t _ => ?_⟩
    rw [mask_of_le_one_iff (linAt_le_one _ _ _ _)]
    intro hl
    obtain ⟨c, c', hc, hpc, -, hc', hst⟩ := hexec i t hi hl
    rw [linAt_of_eq hc', linAt_of_eq hc']
    rcases hn t c c' hc hpc hst with h | h
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h]
  -- (29)
  have h29 : ∀ j, blocks (2 ^ q) (s + 1) (regAt P x j) ≼
      (2 ^ q / 2 - 1) * blocks (2 ^ q) (s + 1) (fun _ => 1) := by
    intro j
    have hreg_lt : ∀ t, regAt P x j t < 2 ^ q := by
      intro t
      cases hc : run P (init r x) t with
      | none => rw [regAt_of_none hc]; omega
      | some c =>
        rw [regAt_of_eq hc]
        have := hreg_le t c hc j
        have := hts_of t c hc
        omega
    rw [← blocks_smul]
    refine (mask_blocks_iff (fun t _ => hreg_lt t) (fun t _ => ?_)).2 ?_
    · simp only [mul_one]
      have := two_pow_div_two (q := q) (by omega)
      omega
    · intro t _
      simp only [mul_one]
      rw [two_pow_div_two (by omega), mask_two_pow_sub_one_iff]
      cases hc : run P (init r x) t with
      | none => rw [regAt_of_none hc]; positivity
      | some c =>
        rw [regAt_of_eq hc]
        have := hreg_le t c hc j
        have := hts_of t c hc
        omega
  -- (30)
  have h30 : blocks (2 ^ q) (s + 1) (fun _ => 1)
      = ∑ i ∈ range P.length, blocks (2 ^ q) (s + 1) (linAt P x i) := by
    rw [← blocks_sum]
    apply blocks_congr
    intro t ht
    exact (huniq t (by omega)).symm
  -- (31)
  have h31 : ∀ i < P.length, blocks (2 ^ q) (s + 1) (linAt P x i) ≼
      blocks (2 ^ q) (s + 1) (fun _ => 1) := by
    intro i _
    refine (mask_blocks_iff (fun t _ => hlin_lt i t) (fun t _ => by omega)).2 ?_
    intro t _
    rw [mask_of_le_one_iff (linAt_le_one _ _ _ _)]
    intro _
    rfl
  -- (32)
  have h32 : 1 ≼ blocks (2 ^ q) (s + 1) (linAt P x 0) := by
    have key : blocks (2 ^ q) (s + 1) (fun t => if t = 0 then 1 else 0) ≼
        blocks (2 ^ q) (s + 1) (linAt P x 0) := by
      refine (mask_blocks_iff (fun t _ => by split_ifs <;> omega) (fun t _ => hlin_lt _ _)).2 ?_
      intro t _
      split_ifs with h0
      · subst h0
        rw [linAt_of_eq (run_zero P (init r x))]
        simp only [init, if_pos rfl]
        exact Mask.refl 1
      · exact zero_mask _
    rwa [blocks_single (by omega), pow_zero] at key
  -- (33)
  have h33 : blocks (2 ^ q) (s + 1) (linAt P x (P.length - 1)) = (2 ^ q) ^ s := by
    rw [← blocks_single (Q := 2 ^ q) (n := s + 1) (k := s) (by omega)]
    apply blocks_congr
    intro t ht
    rcases Nat.lt_or_ge t s with h | h
    · obtain ⟨c, hc⟩ := hsome t (by omega)
      rw [linAt_of_eq hc, if_neg (hpc_ne t h c hc), if_neg (by omega)]
    · have : t = s := by omega
      subst this
      rw [linAt_of_eq hs, if_pos hfin_pc, if_pos rfl]
  -- the line conditions
  have hlines : ∀ (i : ℕ) (c : Cmd r), P[i]? = some c →
      lineCond (2 ^ q) (blocks (2 ^ q) (s + 1) fun _ => 1)
        (fun j => blocks (2 ^ q) (s + 1) (regAt P x j))
        (fun i => blocks (2 ^ q) (s + 1) (linAt P x i)) i c := by
    intro i c hc
    cases c with
    | goto k =>
      have hi : P[i]? ≠ some Cmd.stop := by rw [hc]; simp
      show 2 ^ q * blocks (2 ^ q) (s + 1) (linAt P x i) ≼ blocks (2 ^ q) (s + 1) (linAt P x k)
      apply hjump i k hi
      intro t c c' _ hpc hst
      unfold step at hst
      rw [hpc, hc] at hst
      simp only [Cmd.exec, Option.some.injEq] at hst
      rw [← hst]
    | arith δ =>
      have hi : P[i]? ≠ some Cmd.stop := by rw [hc]; simp
      show 2 ^ q * blocks (2 ^ q) (s + 1) (linAt P x i) ≼ blocks (2 ^ q) (s + 1) (linAt P x (i + 1))
      apply hjump i (i + 1) hi
      intro t c c' _ hpc hst
      unfold step at hst
      rw [hpc, hc] at hst
      simp only [Cmd.exec] at hst
      split_ifs at hst
      simp only [Option.some.injEq] at hst
      rw [← hst]
    | stop => trivial
    | ifLt a b k =>
      have hi : P[i]? ≠ some Cmd.stop := by rw [hc]; simp
      obtain ⟨hk, hki, hki1⟩ := hP.ifLt_ok i a b k hc
      refine ⟨hcond1 i k hi hki1 ?_, ?_⟩
      · intro t c c' _ hpc hst
        unfold step at hst
        rw [hpc, hc] at hst
        simp only [Cmd.exec, Option.some.injEq] at hst
        rw [← hst]
        simp only
        split_ifs <;> simp
      · show 2 ^ q * blocks (2 ^ q) (s + 1) (linAt P x i) ≼
          blocks (2 ^ q) (s + 1) (linAt P x k) + 2 ^ q * blocks (2 ^ q) (s + 1) (fun _ => 1)
            + 2 * Operand.enc _ _ a - 2 * Operand.enc _ _ b
        rw [henc a, henc b]
        refine (compare_cond rfl hq2 (linAt_le_one P x i) (linAt_le_one P x k) ?_ ?_
          (hopd_lt a) (hopd_lt b) ?_).2 ?_
        · intro t hl
          obtain ⟨c, c', hct, hpc, -, -, -⟩ := hexec i t hi hl
          rw [linAt_of_eq hct, if_neg (by omega)]
        · intro t hl
          obtain ⟨c, c', -, -, hts, -, -⟩ := hexec i t hi hl
          exact hts
        · intro t h1 h2
          have := linAt_le_one P x k t
          have := hopd_le' a t h1 h2
          omega
        · intro t hl
          obtain ⟨c, c', hct, hpc, -, hc', hst⟩ := hexec i t hi hl
          unfold step at hst
          rw [hpc, hc] at hst
          simp only [Cmd.exec, Option.some.injEq] at hst
          rw [linAt_of_eq hc', ← hst, opdAt_of_eq hct, opdAt_of_eq hct]
          simp only
          by_cases hab : a.val c.regs < b.val c.regs
          · simp [hab]
          · simp [hab, Ne.symm hki1]
    | ifLe a b k =>
      have hi : P[i]? ≠ some Cmd.stop := by rw [hc]; simp
      obtain ⟨hk, hki, hki1⟩ := hP.ifLe_ok i a b k hc
      refine ⟨hcond1 i k hi hki1 ?_, ?_⟩
      · intro t c c' _ hpc hst
        unfold step at hst
        rw [hpc, hc] at hst
        simp only [Cmd.exec, Option.some.injEq] at hst
        rw [← hst]
        simp only
        split_ifs <;> simp
      · show 2 ^ q * blocks (2 ^ q) (s + 1) (linAt P x i) ≼
          blocks (2 ^ q) (s + 1) (linAt P x (i + 1)) + 2 ^ q * blocks (2 ^ q) (s + 1) (fun _ => 1)
            + 2 * Operand.enc _ _ b - 2 * Operand.enc _ _ a
        rw [henc a, henc b]
        refine (compare_cond rfl hq2 (linAt_le_one P x i) (linAt_le_one P x (i + 1)) ?_ ?_
          (hopd_lt b) (hopd_lt a) ?_).2 ?_
        · intro t hl
          obtain ⟨c, c', hct, hpc, -, -, -⟩ := hexec i t hi hl
          rw [linAt_of_eq hct, if_neg (by omega)]
        · intro t hl
          obtain ⟨c, c', -, -, hts, -, -⟩ := hexec i t hi hl
          exact hts
        · intro t h1 h2
          have := linAt_le_one P x (i + 1) t
          have := hopd_le' b t h1 h2
          omega
        · intro t hl
          obtain ⟨c, c', hct, hpc, -, hc', hst⟩ := hexec i t hi hl
          unfold step at hst
          rw [hpc, hc] at hst
          simp only [Cmd.exec, Option.some.injEq] at hst
          rw [linAt_of_eq hc', ← hst, opdAt_of_eq hct, opdAt_of_eq hct]
          simp only
          by_cases hab : a.val c.regs ≤ b.val c.regs
          · simp [hab, hki1]
          · have := Nat.lt_of_not_le hab
            simp [hab, this]
  -- the register equations
  have hregs : ∀ j, regEq P x (2 ^ q) (fun j => blocks (2 ^ q) (s + 1) (regAt P x j))
      (fun i => blocks (2 ^ q) (s + 1) (linAt P x i)) j := by
    intro j
    unfold regEq
    simp only
    rw [sum_ite_mul_blocks, sum_ite_mul_blocks, blocks_shift, blocks_shift, blocks_shift, hextR j]
    have hx0 : (if j.val = 0 then x else 0)
        = blocks (2 ^ q) (s + 2) (fun t => if t = 0 then (if j.val = 0 then x else 0) else 0) := by
      rw [blocks_single_mul (by omega)]; simp
    rw [hx0, ← blocks_add, ← blocks_add, ← blocks_add]
    apply blocks_congr
    intro t ht
    cases t with
    | zero =>
      simp only [↓reduceIte, Nat.zero_add, Nat.add_zero]
      rw [regAt_of_eq (run_zero P (init r x))]
      rfl
    | succ t =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
      have hts : t ≤ s := by omega
      obtain ⟨c, hc⟩ := hsome t hts
      have hpcl := hpc_le t hts c hc
      have hlin : ∀ i, linAt P x i t = if i = c.pc then 1 else 0 := by
        intro i; rw [linAt_of_eq hc]; simp only [eq_comm]
      rw [sum_ite_indicator hpcl _ _ hlin, sum_ite_indicator hpcl _ _ hlin, regAt_of_eq hc]
      rcases Nat.lt_or_ge t s with hlt | hge
      · obtain ⟨c', hc', hst⟩ := hstep t hlt c hc
        rw [regAt_of_eq hc']
        unfold step at hst
        cases hp : P[c.pc]? with
        | none => rw [hp] at hst; simp at hst
        | some cmd =>
          rw [hp] at hst
          cases cmd with
          | goto k =>
            simp only [Cmd.exec, Option.some.injEq] at hst
            simp [delta, hp, ← hst]
          | ifLt a b k =>
            simp only [Cmd.exec, Option.some.injEq] at hst
            simp [delta, hp, ← hst]
          | ifLe a b k =>
            simp only [Cmd.exec, Option.some.injEq] at hst
            simp [delta, hp, ← hst]
          | arith δ =>
            simp only [Cmd.exec] at hst
            split_ifs at hst with hδ
            simp only [Option.some.injEq] at hst
            have hδj := hδ j
            have hb := hP.arith_ok _ _ hp j
            simp only [delta, hp, ← hst]
            split_ifs <;> omega
          | stop => simp [Cmd.exec] at hst
      · have hts' : t = s := by omega
        rw [hts', hs] at hc
        cases hc
        rw [hts', hreg_zero j (s + 1) (by omega)]
        simp [delta, final, hP.last_stop]
  exact {
    c24 := h24
    c25 := h25
    c26 := ⟨q, rfl⟩
    c27 := geom_blocks (by omega) (s + 1)
    c29 := h29
    c30 := h30
    c31 := h31
    c32 := h32
    c33 := h33
    lines := hlines
    regs := hregs }

end RM
end JM1984
