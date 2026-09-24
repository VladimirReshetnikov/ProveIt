import Diophantine.Paper1984.Encoding

/-!
# Soundness: a solution of the system is an accepting computation

From a solution `s, Q, I, R, L` of (24)–(39) we read off the base-`Q` blocks
`r_{j,t}` of `R_j` and `l_{i,t}` of `L_i`; (27) makes `I` the number with all
blocks `1`, (29)–(31) make the blocks proper, (30) says exactly one line is
"executed" at each time, (32)/(33) fix the first and last line, the line
conditions force the correct transfers, and the register equations force the
correct register contents.  By induction on `t` the configuration at time `t`
is the one described by the blocks, and at time `s` it is the accepting one.
-/

namespace JM1984
namespace RM

open Finset

variable {r : ℕ}

/-- The value of an operand at time `t`, read from the blocks. -/
def opdOf (s : ℕ) (rj : Fin r → ℕ → ℕ) (t : ℕ) : Operand r → ℕ
  | .reg j => rj j t
  | .zero => 0
  | .one => if t ≤ s then 1 else 0

/-- A solution of the system is the canonical encoding of the accepting computation: the run
reaches the accepting configuration at time `s`, `I` has all blocks `1`, and the base-`Q` digits
of `R_j` and `L_i` are the register contents and the line indicators of the run. -/
theorem sys_canonical {P : Program r} (hP : WF P) {x s Q I : ℕ} {R : Fin r → ℕ} {L : ℕ → ℕ}
    (H : Sys P x s Q I R L) :
    run P (init r x) s = some (final P) ∧ I = blocks Q (s + 1) (fun _ => 1) ∧
      (∀ j, R j < Q ^ (s + 1)) ∧ (∀ i < P.length, L i < Q ^ (s + 1)) ∧
      ∀ t ≤ s, ∀ c, run P (init r x) t = some c →
        (∀ j, digit Q (R j) t = c.regs j) ∧
        ∀ i < P.length, digit Q (L i) t = if c.pc = i then 1 else 0 := by
  obtain ⟨q, rfl⟩ := H.c26
  have hlen := hP.pos
  have h25 := H.c25
  have h24 := H.c24
  have hQ2 : 2 ≤ 2 ^ q := by omega
  have hq1 : 1 ≤ q := by
    by_contra h
    have : q = 0 := by omega
    subst this
    simp at hQ2
  have hQ0 : 0 < 2 ^ q := by omega
  have hhalf := two_pow_div_two hq1
  have hhalf2 := two_mul_two_pow_div_two hq1
  -- (27): `I` has all blocks equal to `1`
  have hI : I = blocks (2 ^ q) (s + 1) (fun _ => 1) := by
    have h1 := H.c27
    have h2 := geom_blocks (Q := 2 ^ q) (by omega) (s + 1)
    have : (2 ^ q - 1) * I = (2 ^ q - 1) * blocks (2 ^ q) (s + 1) (fun _ => 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  -- the blocks of `R_j`
  obtain ⟨rj, hrj_def⟩ : ∃ rj : Fin r → ℕ → ℕ, rj = fun j t => digit (2 ^ q) (R j) t := ⟨_, rfl⟩
  have hR_lt : ∀ j, R j < (2 ^ q) ^ (s + 1) := by
    intro j
    have := (H.c29 j).le
    rw [hI, ← blocks_smul] at this
    refine lt_of_le_of_lt this (blocks_lt ?_)
    intro t _
    simp only [mul_one]
    omega
  have hR : ∀ j, R j = blocks (2 ^ q) (s + 1) (rj j) := by
    intro j; rw [hrj_def]; exact (blocks_digit hQ0 (hR_lt j)).symm
  have hrj_zero : ∀ j t, s < t → rj j t = 0 := by
    intro j t ht; rw [hrj_def]; exact digit_eq_zero_of_lt hQ0 (hR_lt j) (by omega)
  have hrj_digit : ∀ j t, rj j t < 2 ^ q := by
    intro j t; rw [hrj_def]; exact digit_lt hQ0 _ _
  have hrj_lt : ∀ j t, 2 * rj j t < 2 ^ q := by
    intro j t
    rcases Nat.lt_or_ge t (s + 1) with ht | ht
    · have h := H.c29 j
      rw [hI, ← blocks_smul, hR j,
        mask_blocks_iff (fun t _ => hrj_digit j t) (fun t _ => by simp only [mul_one]; omega)] at h
      have := h t ht
      simp only [mul_one, hhalf, mask_two_pow_sub_one_iff] at this
      omega
    · rw [hrj_zero j t (by omega)]
      omega
  -- the blocks of `L_i`
  obtain ⟨li, hli_def⟩ : ∃ li : ℕ → ℕ → ℕ, li = fun i t => digit (2 ^ q) (L i) t := ⟨_, rfl⟩
  have hL_lt : ∀ i < P.length, L i < (2 ^ q) ^ (s + 1) := by
    intro i hi
    have := (H.c31 i hi).le
    rw [hI] at this
    exact lt_of_le_of_lt this (blocks_lt (fun t _ => by omega))
  have hL : ∀ i < P.length, L i = blocks (2 ^ q) (s + 1) (li i) := by
    intro i hi; rw [hli_def]; exact (blocks_digit hQ0 (hL_lt i hi)).symm
  have hli_zero : ∀ i < P.length, ∀ t, s < t → li i t = 0 := by
    intro i hi t ht; rw [hli_def]; exact digit_eq_zero_of_lt hQ0 (hL_lt i hi) (by omega)
  have hli_digit : ∀ i t, li i t < 2 ^ q := by
    intro i t; rw [hli_def]; exact digit_lt hQ0 _ _
  have hli_le : ∀ i < P.length, ∀ t, li i t ≤ 1 := by
    intro i hi t
    rcases Nat.lt_or_ge t (s + 1) with ht | ht
    · have h := H.c31 i hi
      rw [hI, hL i hi, mask_blocks_iff (fun t _ => hli_digit i t) (fun t _ => by omega)] at h
      exact (h t ht).le
    · rw [hli_zero i hi t (by omega)]
      omega
  -- (30): exactly one line at each time
  have hsum : ∀ t ≤ s, ∑ i ∈ range P.length, li i t = 1 := by
    intro t ht
    have h := H.c30
    rw [hI, sum_congr rfl (fun i hi => hL i (mem_range.1 hi)), ← blocks_sum] at h
    have hbound : ∀ t, ∑ i ∈ range P.length, li i t < 2 ^ q := by
      intro t
      calc ∑ i ∈ range P.length, li i t ≤ ∑ i ∈ range P.length, 1 :=
            sum_le_sum (fun i hi => hli_le i (mem_range.1 hi) t)
        _ = P.length := by simp
        _ < 2 ^ q := h25
    exact ((blocks_eq_iff hQ0 (fun t _ => by omega) (fun t _ => hbound t)).1 h t (by omega)).symm
  have hpc_ex : ∀ t ≤ s, ∃ i0, i0 < P.length ∧ li i0 t = 1 ∧ ∀ i < P.length, i ≠ i0 → li i t = 0 :=
    fun t ht => exists_unique_of_sum_eq_one (hsum t ht)
  choose! pc hpc using hpc_ex
  have hli_eq : ∀ t ≤ s, ∀ i < P.length, li i t = if i = pc t then 1 else 0 := by
    intro t ht i hi
    split_ifs with h
    · subst h; exact (hpc t ht).2.1
    · exact (hpc t ht).2.2 i hi h
  have hpc_of : ∀ t ≤ s, ∀ i < P.length, li i t = 1 → pc t = i := by
    intro t ht i hi h
    by_contra hne
    rw [(hpc t ht).2.2 i hi (Ne.symm hne)] at h
    omega
  -- (32): the machine starts at `L0`
  have hpc0 : pc 0 = 0 := by
    have h := H.c32
    have key : blocks (2 ^ q) (s + 1) (fun t => if t = 0 then 1 else 0) ≼ L 0 := by
      rwa [blocks_single (by omega), pow_zero]
    rw [hL 0 hlen, mask_blocks_iff (fun t _ => by split_ifs <;> omega)
      (fun t _ => hli_digit 0 t)] at key
    have := key 0 (by omega)
    simp only [if_pos rfl] at this
    have h2 := (mask_of_le_one_iff le_rfl).1 this rfl
    have h3 := hli_le 0 hlen 0
    exact hpc_of 0 (by omega) 0 hlen (by omega)
  -- (33): the machine is at the STOP line exactly at time `s`
  have hLl : ∀ t ≤ s, li (P.length - 1) t = if t = s then 1 else 0 := by
    intro t ht
    have h := H.c33
    rw [hL _ (by omega), ← blocks_single (Q := 2 ^ q) (n := s + 1) (k := s) (by omega)] at h
    exact (blocks_eq_iff hQ0 (fun t _ => hli_digit _ t) (fun t _ => by split_ifs <;> omega)).1
      h t (by omega)
  have hpcs : pc s = P.length - 1 := by
    have := hLl s le_rfl
    rw [if_pos rfl] at this
    exact hpc_of s le_rfl _ (by omega) this
  have hpc_ne : ∀ t < s, pc t ≠ P.length - 1 := by
    intro t ht hne
    have h1 := hLl t (by omega)
    rw [if_neg (by omega)] at h1
    have h2 := (hpc t (by omega)).2.1
    rw [hne] at h2
    omega
  have hcmd : ∀ t < s, ∃ c, P[pc t]? = some c ∧ c ≠ Cmd.stop := by
    intro t ht
    have hlt := (hpc t (by omega)).1
    refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
    intro hstop
    exact hpc_ne t ht (hP.stop_last _ (by rw [List.getElem?_eq_getElem hlt, hstop]))
  -- the register equations, block by block
  have hdec_gen : ∀ (p : ℤ → Prop) [DecidablePred p] (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if p (delta P i j) then li i t else 0)
        = if p (delta P (pc t) j) then 1 else 0 := by
    intro p _ j t ht
    rw [sum_congr rfl (fun i hi => by rw [hli_eq t ht i (mem_range.1 hi)])]
    exact sum_ite_indicator (hpc t ht).1 _ _ (fun i => rfl)
  have hdec_zero_gen : ∀ (p : ℤ → Prop) [DecidablePred p] (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if p (delta P i j) then li i t else 0) = 0 := by
    intro p _ j t ht
    apply sum_eq_zero
    intro i hi
    rw [hli_zero i (mem_range.1 hi) t ht]
    simp
  have hdecm : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if delta P i j = -1 then li i t else 0)
        = if delta P (pc t) j = -1 then 1 else 0 := hdec_gen (fun d => d = -1)
  have hdecp : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if delta P i j = 1 then li i t else 0)
        = if delta P (pc t) j = 1 then 1 else 0 := hdec_gen (fun d => d = 1)
  have hdecm0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if delta P i j = -1 then li i t else 0) = 0 :=
    hdec_zero_gen (fun d => d = -1)
  have hdecp0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if delta P i j = 1 then li i t else 0) = 0 :=
    hdec_zero_gen (fun d => d = 1)
  have hreg : ∀ j, ∀ t < s + 2,
      rj j t + (if t = 0 then 0 else ∑ i ∈ range P.length, if delta P i j = -1 then li i (t - 1) else 0)
        = (if t = 0 then 0 else rj j (t - 1))
          + (if t = 0 then 0 else ∑ i ∈ range P.length, if delta P i j = 1 then li i (t - 1) else 0)
          + (if t = 0 then (if j.val = 0 then x else 0) else 0) := by
    intro j
    have h := H.regs j
    unfold regEq at h
    have hS1 : ∑ i ∈ range P.length, (if delta P i j = -1 then 2 ^ q * L i else 0)
        = ∑ i ∈ range P.length, (if delta P i j = -1 then 2 ^ q * blocks (2 ^ q) (s + 1) (li i) else 0) :=
      sum_congr rfl (fun i hi => by rw [hL i (mem_range.1 hi)])
    have hS2 : ∑ i ∈ range P.length, (if delta P i j = 1 then 2 ^ q * L i else 0)
        = ∑ i ∈ range P.length, (if delta P i j = 1 then 2 ^ q * blocks (2 ^ q) (s + 1) (li i) else 0) :=
      sum_congr rfl (fun i hi => by rw [hL i (mem_range.1 hi)])
    rw [hS1, hS2, hR j, sum_ite_mul_blocks, sum_ite_mul_blocks, blocks_shift, blocks_shift,
      blocks_shift,
      (blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => hrj_zero j t (by omega))).symm] at h
    have hx0 : (if j.val = 0 then x else 0)
        = blocks (2 ^ q) (s + 2) (fun t => if t = 0 then (if j.val = 0 then x else 0) else 0) := by
      rw [blocks_single_mul (by omega)]; simp
    rw [hx0, ← blocks_add, ← blocks_add, ← blocks_add] at h
    refine (blocks_eq_iff hQ0 ?_ ?_).1 h
    · intro t ht
      cases t with
      | zero => simp only [↓reduceIte]; have := hrj_lt j 0; omega
      | succ t =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have := hrj_lt j (t + 1)
        rcases Nat.lt_or_ge s t with h' | h'
        · rw [hdecm0 j t h']; omega
        · rw [hdecm j t h']; split_ifs <;> omega
    · intro t ht
      cases t with
      | zero => simp only [↓reduceIte]; split_ifs <;> omega
      | succ t =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
        have := hrj_lt j t
        rcases Nat.lt_or_ge s t with h' | h'
        · rw [hdecp0 j t h']; omega
        · rw [hdecp j t h']; split_ifs <;> omega
  have hdig0 : ∀ j, rj j 0 = if j.val = 0 then x else 0 := by
    intro j
    have := hreg j 0 (by omega)
    simpa using this
  have hdig : ∀ j, ∀ t ≤ s,
      rj j (t + 1) + (if delta P (pc t) j = -1 then 1 else 0)
        = rj j t + (if delta P (pc t) j = 1 then 1 else 0) := by
    intro j t ht
    have := hreg j (t + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero] at this
    rwa [hdecm j t ht, hdecp j t ht] at this
  -- the register contents are bounded by `x + t`
  have hrj_le : ∀ j, ∀ t ≤ s, rj j t ≤ x + t := by
    intro j t
    induction t with
    | zero => intro _; rw [hdig0 j]; split_ifs <;> omega
    | succ t ih =>
      intro ht
      have h1 := hdig j t (by omega)
      have h2 := ih (by omega)
      split_ifs at h1 <;> omega
  -- the registers are zero at time `s`
  have hrj_s : ∀ j, rj j s = 0 := by
    intro j
    have h1 := hdig j s le_rfl
    have hd : delta P (pc s) j = 0 := by
      rw [hpcs]; simp [delta, hP.last_stop]
    rw [hrj_zero j (s + 1) (by omega), hd] at h1
    simp at h1
    omega
  -- reading the transfer conditions block by block
  have hjump : ∀ i n, i < P.length → n < P.length → 2 ^ q * L i ≼ L n →
      ∀ t < s, pc t = i → pc (t + 1) = n := by
    intro i n hi hn h t ht hpt
    rw [hL i hi, hL n hn, blocks_shift,
      ← blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => hli_zero n hn t (by omega)),
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hli_digit _ _))
        (fun t _ => hli_digit _ _)] at h
    have := h (t + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [mask_of_le_one_iff (hli_le i hi t)] at this
    have h1 := this (by rw [hli_eq t (by omega) i hi, if_pos hpt.symm])
    have h2 := hli_le n hn (t + 1)
    exact hpc_of (t + 1) (by omega) n hn (by omega)
  have hbranch : ∀ i k, i + 1 < P.length → k < P.length → k ≠ i + 1 →
      2 ^ q * L i ≼ L k + L (i + 1) →
      ∀ t < s, pc t = i → pc (t + 1) = k ∨ pc (t + 1) = i + 1 := by
    intro i k hi hk hki h t ht hpt
    rw [hL i (by omega), hL k hk, hL (i + 1) hi, blocks_shift,
      ← blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => hli_zero k hk t (by omega)),
      ← blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => hli_zero (i + 1) hi t (by omega)),
      ← blocks_add,
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hli_digit _ _))
        (fun t _ => by have := hli_le k hk t; have := hli_le (i + 1) hi t; omega)] at h
    have := h (t + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [mask_of_le_one_iff (hli_le i (by omega) t)] at this
    have h1 := this (by rw [hli_eq t (by omega) i (by omega), if_pos hpt.symm])
    rw [hli_eq (t + 1) (by omega) k hk, hli_eq (t + 1) (by omega) (i + 1) hi] at h1
    by_cases hk' : k = pc (t + 1)
    · left; exact hk'.symm
    · right
      rw [if_neg hk'] at h1
      by_contra hne
      rw [if_neg (Ne.symm hne)] at h1
      omega
  -- the encoded operands
  have henc : ∀ a : Operand r, a.enc I R = blocks (2 ^ q) (s + 1) (fun t => opdOf s rj t a) := by
    intro a
    cases a with
    | reg j => exact hR j
    | zero => simp only [Operand.enc]; rw [← blocks_const_zero (2 ^ q) (s + 1)]; rfl
    | one =>
      simp only [Operand.enc]
      rw [hI]
      apply blocks_congr
      intro t ht
      simp only [opdOf]
      rw [if_pos (by omega)]
  have hval : ∀ t ≤ s, ∀ o : Operand r, o.val (fun j => rj j t) = opdOf s rj t o := by
    intro t ht o
    cases o with
    | reg j => rfl
    | zero => rfl
    | one => simp only [Operand.val, opdOf]; rw [if_pos ht]
  -- the second condition of (36)/(37)
  have hcompare : ∀ i n (a b : Operand r), i < P.length → n < P.length → n ≠ i →
      3 ≤ P.length → P[i]? ≠ some Cmd.stop →
      2 ^ q * L i ≼ L n + 2 ^ q * I + 2 * a.enc I R - 2 * b.enc I R →
      ∀ t < s, pc t = i → (pc (t + 1) = n ↔ opdOf s rj t a < opdOf s rj t b) := by
    intro i n a b hi hn hni h3 hstop h t ht hpt
    have hq2 : 2 ≤ q := by
      by_contra hq
      push_neg at hq
      have : 2 ^ q ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hQ4 : 4 ≤ 2 ^ q := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
    have hu : ∀ (o : Operand r) t, 2 * opdOf s rj t o < 2 ^ q := by
      intro o t
      cases o with
      | reg j => exact hrj_lt j t
      | zero => simp only [opdOf]; omega
      | one => simp only [opdOf]; split_ifs <;> omega
    rw [hL i hi, hL n hn, henc a, henc b, hI] at h
    have key := (compare_cond rfl hq2 (hli_le i hi) (hli_le n hn) ?_ ?_ (hu a) (hu b) ?_).1 h t
      (by rw [hli_eq t (by omega) i hi, if_pos hpt.symm])
    · rw [hli_eq (t + 1) (by omega) n hn] at key
      constructor
      · intro hp
        exact key.1 (by rw [if_pos hp.symm])
      · intro hlt
        have := key.2 hlt
        by_contra hne
        rw [if_neg (Ne.symm hne)] at this
        omega
    · intro t' hl
      rcases Nat.lt_or_ge s t' with h' | h'
      · rw [hli_zero i hi t' h'] at hl; omega
      · have := hpc_of t' h' i hi hl
        rw [hli_eq t' h' n hn, if_neg (by omega)]
    · intro t' hl
      rcases Nat.lt_or_ge t' s with h' | h'
      · exact h'
      · exfalso
        rcases Nat.lt_or_ge s t' with h'' | h''
        · rw [hli_zero i hi t' h''] at hl; omega
        · have hts : t' = s := by omega
          subst hts
          have := hpc_of t' le_rfl i hi hl
          rw [hpcs] at this
          exact hstop (by rw [← this]; exact hP.last_stop)
    · intro t' h1 h2
      have hln := hli_le n hn t'
      have h8 : 8 ≤ 2 ^ q := by
        have h4 : 4 < 2 ^ q := by omega
        have hq3 : 2 < q := by
          by_contra hq
          push_neg at hq
          have : 2 ^ q ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hq
          omega
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq3
      cases a with
      | reg j =>
        have := hrj_le j t' (by omega)
        simp only [opdOf]
        omega
      | zero => simp only [opdOf]; omega
      | one => simp only [opdOf]; rw [if_pos (by omega)]; omega
  -- the main induction: the configuration at time `t` is the one described by the blocks
  have hrun : ∀ t ≤ s, run P (init r x) t = some ⟨pc t, fun j => rj j t⟩ := by
    intro t
    induction t with
    | zero =>
      intro _
      simp only [run_zero, init, Option.some.injEq, Config.mk.injEq]
      refine ⟨hpc0.symm, ?_⟩
      funext j
      exact (hdig0 j).symm
    | succ t ih =>
      intro ht
      have ht' : t < s := by omega
      rw [run_succ_of_eq (ih (by omega))]
      obtain ⟨c, hc, hcs⟩ := hcmd t ht'
      have hpcl := (hpc t (by omega)).1
      have hne := hpc_ne t ht'
      unfold step
      simp only
      rw [hc]
      have hd := fun j => hdig j t (by omega)
      cases c with
      | goto k =>
        have hk := hP.goto_lt _ _ hc
        have hn := hjump _ k hpcl hk (H.lines _ _ hc) t ht' rfl
        simp only [Cmd.exec, Option.some.injEq, Config.mk.injEq]
        refine ⟨hn.symm, ?_⟩
        funext j
        have := hd j
        simp [delta, hc] at this
        exact this.symm
      | arith δ =>
        have hb := hP.arith_ok _ _ hc
        have hn := hjump _ (pc t + 1) hpcl (by omega) (H.lines _ _ hc) t ht' rfl
        simp only [Cmd.exec]
        have hδ : ∀ j, 0 ≤ (rj j t : ℤ) + δ j := by
          intro j
          have h1 := hd j
          simp only [delta, hc] at h1
          have := hb j
          split_ifs at h1 <;> omega
        rw [if_pos hδ]
        simp only [Option.some.injEq, Config.mk.injEq]
        refine ⟨hn.symm, ?_⟩
        funext j
        have h1 := hd j
        simp only [delta, hc] at h1
        have := hb j
        split_ifs at h1 <;> omega
      | ifLt a b k =>
        obtain ⟨hk, hki, hki1⟩ := hP.ifLt_ok _ a b k hc
        have h3 : 3 ≤ P.length := length_ge_three_of_cond hk hki hki1 (by omega)
        obtain ⟨h1, h2⟩ := H.lines _ _ hc
        have hbr := hbranch _ k (by omega) hk hki1 h1 t ht' rfl
        have hcmp := hcompare _ k a b hpcl hk hki h3 (by rw [hc]; simp) h2 t ht' rfl
        simp only [Cmd.exec, Option.some.injEq, Config.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [hval t (by omega) a, hval t (by omega) b]
          split_ifs with hlt
          · exact (hcmp.2 hlt).symm
          · rcases hbr with h | h
            · exact absurd (hcmp.1 h) hlt
            · exact h.symm
        · funext j
          have := hd j
          simp [delta, hc] at this
          exact this.symm
      | ifLe a b k =>
        obtain ⟨hk, hki, hki1⟩ := hP.ifLe_ok _ a b k hc
        have h3 : 3 ≤ P.length := length_ge_three_of_cond hk hki hki1 (by omega)
        obtain ⟨h1, h2⟩ := H.lines _ _ hc
        have hbr := hbranch _ k (by omega) hk hki1 h1 t ht' rfl
        have hcmp := hcompare _ (pc t + 1) b a hpcl (by omega) (by omega) h3 (by rw [hc]; simp)
          h2 t ht' rfl
        simp only [Cmd.exec, Option.some.injEq, Config.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [hval t (by omega) a, hval t (by omega) b]
          split_ifs with hle
          · rcases hbr with h | h
            · exact h.symm
            · exact absurd (hcmp.1 h) (by omega)
          · exact (hcmp.2 (by omega)).symm
        · funext j
          have := hd j
          simp [delta, hc] at this
          exact this.symm
      | stop => exact absurd rfl hcs
  have hfinal : run P (init r x) s = some (final P) := by
    rw [hrun s le_rfl]
    simp only [final, Option.some.injEq, Config.mk.injEq]
    exact ⟨hpcs, funext hrj_s⟩
  refine ⟨hfinal, hI, hR_lt, hL_lt, fun t ht c hc => ?_⟩
  rw [hrun t ht] at hc
  cases hc
  refine ⟨fun j => by rw [hrj_def], fun i hi => ?_⟩
  have := hli_eq t ht i hi
  rw [hli_def] at this
  simp only at this
  rw [this]
  by_cases h : i = pc t
  · simp [h]
  · simp [h, Ne.symm h]

theorem accepts_of_sys {P : Program r} (hP : WF P) {x s Q I : ℕ} {R : Fin r → ℕ} {L : ℕ → ℕ}
    (H : Sys P x s Q I R L) : Accepts P x :=
  ⟨s, (sys_canonical hP H).1⟩

end RM
end JM1984
