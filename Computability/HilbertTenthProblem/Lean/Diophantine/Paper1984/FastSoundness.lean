import Diophantine.Paper1984.FastSystem
import Diophantine.Paper1984.Soundness

/-!
# Jones–Matijasevič 1984, §4: a solution of the extended system is an accepting computation

The reading of §3 is repeated for the system of §4.  The blocks of `R_j` and `L_i` are the
register contents and the line indicators, and (47)–(50) pin the blocks of the auxiliary
unknowns: `M_n` has blocks `r_{k,t} l_{n,t}` and `J_p` has blocks `⌊r_{j,t}/2⌋ l_{p,t}`, so the
register equations read blockwise as

  `r_{j,t+1} + [δ_{pc(t)}(j) = −1] + [pc(t) halves j]·⌊r_{j,t}/2⌋
     = r_{j,t} + [δ_{pc(t)}(j) = 1] + [pc(t) adds k into j]·r_{k,t}`,

which is exactly one step of a machine with the fast commands (41) and (42).  Since a step at
most doubles a register, `r_{j,t} < 2^t(x+1)`, and (46) leaves room for the carries used by the
comparison conditions.
-/

namespace JM1984
namespace RM

open Finset

variable {r : ℕ}

set_option maxHeartbeats 4000000 in
/-- A solution of the extended system describes the accepting computation: the machine reaches
the accepting configuration at time `s`. -/
theorem xrun_of_xsys {P : XProgram r} (hP : XWF P) {x s Q I : ℕ} {R : Fin r → ℕ}
    {L M J : ℕ → ℕ} (H : XSys P x s Q I R L M J) :
    xrun P (init r x) s = some (xfinal P) := by
  obtain ⟨q, rfl⟩ := H.c26
  have hlen := hP.pos
  have h25 := H.c25
  have h46 := H.c46
  have hpos : 1 ≤ 2 ^ s * (x + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hxs : x + 1 ≤ 2 ^ s * (x + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hq2 : 2 ≤ q := by
    by_contra hc
    push_neg at hc
    have : 2 ^ q ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hq1 : 1 ≤ q := by omega
  have hQ4 : 4 ≤ 2 ^ q := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
  have hQ0 : 0 < 2 ^ q := by omega
  have hhalf := two_pow_div_two hq1
  have hhalf2 := two_mul_two_pow_div_two hq1
  have hQeven : 2 ^ q % 2 = 0 := by omega
  have hmul_le : ∀ a b : ℕ, b ≤ 1 → a * b ≤ a := by
    intro a b hb
    calc a * b ≤ a * 1 := Nat.mul_le_mul_left _ hb
      _ = a := mul_one a
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
  have hcmd : ∀ t < s, ∃ c, P[pc t]? = some c ∧ c ≠ (XCmd.base Cmd.stop : XCmd r) := by
    intro t ht
    have hlt := (hpc t (by omega)).1
    refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
    intro hstop
    exact hpc_ne t ht (hP.stop_last _ (by rw [List.getElem?_eq_getElem hlt, hstop]))
  -- which lines add into, or halve, a register
  have hisAdd : ∀ (i : ℕ) (j : Fin r), isAdd P i j = true → ∃ b, P[i]? = some (.add j b) := by
    intro i j h
    unfold isAdd at h
    cases hp : P[i]? with
    | none => rw [hp] at h; simp at h
    | some c =>
      rw [hp] at h
      cases c with
      | base c' => simp at h
      | add a b =>
        simp only [decide_eq_true_eq] at h
        subst h
        exact ⟨b, rfl⟩
      | half a => simp at h
  have hisHalf : ∀ (i : ℕ) (j : Fin r), isHalf P i j = true → P[i]? = some (.half j) := by
    intro i j h
    unfold isHalf at h
    cases hp : P[i]? with
    | none => rw [hp] at h; simp at h
    | some c =>
      rw [hp] at h
      cases c with
      | base c' => simp at h
      | add a b => simp at h
      | half a =>
        simp only [decide_eq_true_eq] at h
        subst h
        rfl
  -- (47)–(50): the blocks of `M_i` and `J_i`
  obtain ⟨mv, hmv_def⟩ : ∃ mv : ℕ → ℕ → ℕ, mv = fun i t => digit (2 ^ q) (M i) t := ⟨_, rfl⟩
  obtain ⟨jv, hjv_def⟩ : ∃ jv : ℕ → ℕ → ℕ, jv = fun i t => digit (2 ^ q) (J i) t := ⟨_, rfl⟩
  have hmv_eq : ∀ (i : ℕ) (a b : Fin r), P[i]? = some (.add a b) → ∀ t,
      mv i t = rj b t * li i t := by
    intro i a b hi t
    have hil : i < P.length := (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨h1, h2, h3⟩ := H.addMask i a b hi
    rw [hR b] at h1
    rw [hL i hil] at h2
    rw [hR b, hI, hL i hil] at h3
    have hM := (mask47_iff (fun t _ => hrj_digit b t) (fun t _ => hli_le i hil t) (M i)).1
      ⟨h1, h2, h3⟩
    have hbound : ∀ t < s + 1, rj b t * li i t < 2 ^ q := by
      intro t _
      have := hmul_le (rj b t) (li i t) (hli_le i hil t)
      have := hrj_digit b t
      omega
    rcases Nat.lt_or_ge t (s + 1) with ht | ht
    · simp only [hmv_def, hM]
      exact digit_blocks hQ0 hbound t ht
    · simp only [hmv_def, hM]
      rw [hli_zero i hil t (by omega), mul_zero]
      exact digit_eq_zero_of_lt hQ0 (blocks_lt hbound) ht
  have hjv_eq : ∀ (i : ℕ) (a : Fin r), P[i]? = some (.half a) → ∀ t,
      jv i t = rj a t / 2 * li i t := by
    intro i a hi t
    have hil : i < P.length := (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨h1, h2, h3⟩ := H.halfMask i a hi
    rw [hR a] at h1
    rw [hL i hil] at h2
    rw [hR a, hI, hL i hil] at h3
    have hJ := (mask49_iff hq1 (fun t _ => hrj_digit a t) (fun t _ => hli_le i hil t) (J i)).1
      ⟨h1, h2, h3⟩
    have hbound : ∀ t < s + 1, rj a t / 2 * li i t < 2 ^ q := by
      intro t _
      have := hmul_le (rj a t / 2) (li i t) (hli_le i hil t)
      have := hrj_digit a t
      omega
    rcases Nat.lt_or_ge t (s + 1) with ht | ht
    · simp only [hjv_def, hJ]
      exact digit_blocks hQ0 hbound t ht
    · simp only [hjv_def, hJ]
      rw [hli_zero i hil t (by omega), mul_zero]
      exact digit_eq_zero_of_lt hQ0 (blocks_lt hbound) ht
  have hMb : ∀ (i : ℕ) (a b : Fin r), P[i]? = some (.add a b) →
      M i = blocks (2 ^ q) (s + 1) (mv i) := by
    intro i a b hi
    have hil : i < P.length := (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨h1, h2, h3⟩ := H.addMask i a b hi
    rw [hR b] at h1
    rw [hL i hil] at h2
    rw [hR b, hI, hL i hil] at h3
    have hM := (mask47_iff (fun t _ => hrj_digit b t) (fun t _ => hli_le i hil t) (M i)).1
      ⟨h1, h2, h3⟩
    rw [hM]
    exact blocks_congr fun t _ => (hmv_eq i a b hi t).symm
  have hJb : ∀ (i : ℕ) (a : Fin r), P[i]? = some (.half a) →
      J i = blocks (2 ^ q) (s + 1) (jv i) := by
    intro i a hi
    have hil : i < P.length := (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨h1, h2, h3⟩ := H.halfMask i a hi
    rw [hR a] at h1
    rw [hL i hil] at h2
    rw [hR a, hI, hL i hil] at h3
    have hJ := (mask49_iff hq1 (fun t _ => hrj_digit a t) (fun t _ => hli_le i hil t) (J i)).1
      ⟨h1, h2, h3⟩
    rw [hJ]
    exact blocks_congr fun t _ => (hjv_eq i a hi t).symm
  -- the sums over the lines, read at a single time
  have hdec_gen : ∀ (p : ℤ → Prop) [DecidablePred p] (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if p (xdelta P i j) then li i t else 0)
        = if p (xdelta P (pc t) j) then 1 else 0 := by
    intro p _ j t ht
    rw [sum_congr rfl (fun i hi => by rw [hli_eq t ht i (mem_range.1 hi)])]
    exact sum_ite_indicator (hpc t ht).1 _ _ (fun i => rfl)
  have hdec_zero_gen : ∀ (p : ℤ → Prop) [DecidablePred p] (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if p (xdelta P i j) then li i t else 0) = 0 := by
    intro p _ j t ht
    apply sum_eq_zero
    intro i hi
    rw [hli_zero i (mem_range.1 hi) t ht]
    simp
  have hdecm : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if xdelta P i j = -1 then li i t else 0)
        = if xdelta P (pc t) j = -1 then 1 else 0 := hdec_gen (fun d => d = -1)
  have hdecp : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if xdelta P i j = 1 then li i t else 0)
        = if xdelta P (pc t) j = 1 then 1 else 0 := hdec_gen (fun d => d = 1)
  have hdecm0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if xdelta P i j = -1 then li i t else 0) = 0 :=
    hdec_zero_gen (fun d => d = -1)
  have hdecp0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if xdelta P i j = 1 then li i t else 0) = 0 :=
    hdec_zero_gen (fun d => d = 1)
  have hdecM : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if isAdd P i j = true then mv i t else 0)
        = if isAdd P (pc t) j = true then mv (pc t) t else 0 := by
    intro j t ht
    refine sum_eq_single_of_mem (pc t) (mem_range.2 (hpc t ht).1) (fun i hi hne => ?_)
    by_cases hadd : isAdd P i j = true
    · rw [if_pos hadd]
      obtain ⟨b, hb⟩ := hisAdd i j hadd
      rw [hmv_eq i j b hb t, hli_eq t ht i (mem_range.1 hi), if_neg hne, mul_zero]
    · rw [if_neg hadd]
  have hdecJ : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if isHalf P i j = true then jv i t else 0)
        = if isHalf P (pc t) j = true then jv (pc t) t else 0 := by
    intro j t ht
    refine sum_eq_single_of_mem (pc t) (mem_range.2 (hpc t ht).1) (fun i hi hne => ?_)
    by_cases hhalf' : isHalf P i j = true
    · rw [if_pos hhalf']
      have hb := hisHalf i j hhalf'
      rw [hjv_eq i j hb t, hli_eq t ht i (mem_range.1 hi), if_neg hne, mul_zero]
    · rw [if_neg hhalf']
  have hdecM0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if isAdd P i j = true then mv i t else 0) = 0 := by
    intro j t ht
    refine sum_eq_zero fun i hi => ?_
    by_cases hadd : isAdd P i j = true
    · rw [if_pos hadd]
      obtain ⟨b, hb⟩ := hisAdd i j hadd
      rw [hmv_eq i j b hb t, hli_zero i (mem_range.1 hi) t ht, mul_zero]
    · rw [if_neg hadd]
  have hdecJ0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if isHalf P i j = true then jv i t else 0) = 0 := by
    intro j t ht
    refine sum_eq_zero fun i hi => ?_
    by_cases hhalf' : isHalf P i j = true
    · rw [if_pos hhalf']
      have hb := hisHalf i j hhalf'
      rw [hjv_eq i j hb t, hli_zero i (mem_range.1 hi) t ht, mul_zero]
    · rw [if_neg hhalf']
  -- the sizes of the contributions of the fast commands
  have hJval : ∀ (j : Fin r) (t : ℕ), t ≤ s →
      (if isHalf P (pc t) j = true then jv (pc t) t else 0) ≤ rj j t / 2 := by
    intro j t ht
    split_ifs with hh
    · have hp := hisHalf (pc t) j hh
      rw [hjv_eq (pc t) j hp t]
      exact hmul_le _ _ (hli_le (pc t) (hpc t ht).1 t)
    · omega
  have hMlt : ∀ (j : Fin r) (t : ℕ), t ≤ s →
      2 * (if isAdd P (pc t) j = true then mv (pc t) t else 0) < 2 ^ q := by
    intro j t ht
    split_ifs with hh
    · obtain ⟨b, hb⟩ := hisAdd (pc t) j hh
      rw [hmv_eq (pc t) j b hb t]
      have h1 := hmul_le (rj b t) (li (pc t) t) (hli_le _ (hpc t ht).1 t)
      have h2 := hrj_lt b t
      omega
    · omega
  -- the register equations, block by block
  have hreg : ∀ j, ∀ t < s + 2,
      rj j t
          + (if t = 0 then 0
              else ∑ i ∈ range P.length, if xdelta P i j = -1 then li i (t - 1) else 0)
          + (if t = 0 then 0
              else ∑ i ∈ range P.length, if isHalf P i j = true then jv i (t - 1) else 0)
        = (if t = 0 then 0 else rj j (t - 1))
          + (if t = 0 then 0
              else ∑ i ∈ range P.length, if xdelta P i j = 1 then li i (t - 1) else 0)
          + (if t = 0 then 0
              else ∑ i ∈ range P.length, if isAdd P i j = true then mv i (t - 1) else 0)
          + (if t = 0 then (if j.val = 0 then x else 0) else 0) := by
    intro j
    have h := H.regs j
    unfold xregEq at h
    have hS1 : ∑ i ∈ range P.length, (if xdelta P i j = -1 then 2 ^ q * L i else 0)
        = ∑ i ∈ range P.length,
            (if xdelta P i j = -1 then 2 ^ q * blocks (2 ^ q) (s + 1) (li i) else 0) :=
      sum_congr rfl (fun i hi => by rw [hL i (mem_range.1 hi)])
    have hS2 : ∑ i ∈ range P.length, (if xdelta P i j = 1 then 2 ^ q * L i else 0)
        = ∑ i ∈ range P.length,
            (if xdelta P i j = 1 then 2 ^ q * blocks (2 ^ q) (s + 1) (li i) else 0) :=
      sum_congr rfl (fun i hi => by rw [hL i (mem_range.1 hi)])
    have hSM : ∑ i ∈ range P.length, (if isAdd P i j = true then 2 ^ q * M i else 0)
        = ∑ i ∈ range P.length,
            (if isAdd P i j = true then 2 ^ q * blocks (2 ^ q) (s + 1) (mv i) else 0) := by
      refine sum_congr rfl fun i _ => ?_
      by_cases hadd : isAdd P i j = true
      · obtain ⟨b, hb⟩ := hisAdd i j hadd
        rw [if_pos hadd, if_pos hadd, hMb i j b hb]
      · rw [if_neg hadd, if_neg hadd]
    have hSJ : ∑ i ∈ range P.length, (if isHalf P i j = true then 2 ^ q * J i else 0)
        = ∑ i ∈ range P.length,
            (if isHalf P i j = true then 2 ^ q * blocks (2 ^ q) (s + 1) (jv i) else 0) := by
      refine sum_congr rfl fun i _ => ?_
      by_cases hh : isHalf P i j = true
      · have hb := hisHalf i j hh
        rw [if_pos hh, if_pos hh, hJb i j hb]
      · rw [if_neg hh, if_neg hh]
    rw [hS1, hS2, hSM, hSJ, hR j, sum_ite_mul_blocks, sum_ite_mul_blocks, sum_ite_mul_blocks,
      sum_ite_mul_blocks, blocks_shift, blocks_shift, blocks_shift, blocks_shift, blocks_shift,
      (blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => hrj_zero j t (by omega))).symm] at h
    have hx0 : (if j.val = 0 then x else 0)
        = blocks (2 ^ q) (s + 2) (fun t => if t = 0 then (if j.val = 0 then x else 0) else 0) := by
      rw [blocks_single_mul (by omega)]; simp
    rw [hx0, ← blocks_add, ← blocks_add, ← blocks_add, ← blocks_add, ← blocks_add] at h
    refine (blocks_eq_iff hQ0 ?_ ?_).1 h
    · intro t ht
      cases t with
      | zero => simp only [↓reduceIte, Nat.add_zero]; have := hrj_lt j 0; omega
      | succ t =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have h1 := hrj_lt j (t + 1)
        have h2 := hrj_lt j t
        rcases Nat.lt_or_ge s t with h' | h'
        · rw [hdecm0 j t h', hdecJ0 j t h']; omega
        · rw [hdecm j t h', hdecJ j t h']
          have h3 := hJval j t h'
          split_ifs at h3 ⊢ <;> omega
    · intro t ht
      cases t with
      | zero => simp only [↓reduceIte, Nat.zero_add]; split_ifs <;> omega
      | succ t =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
        have h1 := hrj_lt j t
        rcases Nat.lt_or_ge s t with h' | h'
        · rw [hdecp0 j t h', hdecM0 j t h']; omega
        · rw [hdecp j t h', hdecM j t h']
          have h3 := hMlt j t h'
          split_ifs at h3 ⊢ <;> omega
  have hdig0 : ∀ j, rj j 0 = if j.val = 0 then x else 0 := by
    intro j
    have := hreg j 0 (by omega)
    simpa using this
  have hdig : ∀ j, ∀ t ≤ s,
      rj j (t + 1) + (if xdelta P (pc t) j = -1 then 1 else 0)
          + (if isHalf P (pc t) j = true then jv (pc t) t else 0)
        = rj j t + (if xdelta P (pc t) j = 1 then 1 else 0)
          + (if isAdd P (pc t) j = true then mv (pc t) t else 0) := by
    intro j t ht
    have := hreg j (t + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero] at this
    rwa [hdecm j t ht, hdecp j t ht, hdecM j t ht, hdecJ j t ht] at this
  -- a step at most doubles a register
  have hgrow : ∀ t ≤ s, ∀ j, rj j t + 1 ≤ 2 ^ t * (x + 1) := by
    intro t
    induction t with
    | zero =>
      intro _ j
      rw [hdig0 j]
      simp only [pow_zero, one_mul]
      split_ifs <;> omega
    | succ t ih =>
      intro ht j
      have hIH := ih (by omega)
      have hAA : 2 ^ (t + 1) * (x + 1) = 2 * (2 ^ t * (x + 1)) := by ring
      have h1 := hdig j t (by omega)
      have hj := hIH j
      have hM : (if isAdd P (pc t) j = true then mv (pc t) t else 0) + 1 ≤ 2 ^ t * (x + 1) := by
        split_ifs with hh
        · obtain ⟨b, hb⟩ := hisAdd (pc t) j hh
          rw [hmv_eq (pc t) j b hb t]
          have := hmul_le (rj b t) (li (pc t) t) (hli_le _ (hpc t (by omega)).1 t)
          have := hIH b
          omega
        · omega
      rw [hAA]
      split_ifs at h1 hM <;> omega
  -- the registers are zero at time `s`
  have hrj_s : ∀ j, rj j s = 0 := by
    intro j
    have h1 := hdig j s le_rfl
    have hd : xdelta P (pc s) j = 0 := by simp [xdelta, hpcs, hP.last_stop]
    have ha : isAdd P (pc s) j = false := by simp [isAdd, hpcs, hP.last_stop]
    have hb : isHalf P (pc s) j = false := by simp [isHalf, hpcs, hP.last_stop]
    rw [hrj_zero j (s + 1) (by omega), hd, ha, hb] at h1
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
  have hcompare : ∀ i n (a b : Operand r), i < P.length → n < P.length → n ≠ i →
      P[i]? ≠ some (.base Cmd.stop : XCmd r) →
      2 ^ q * L i ≼ L n + 2 ^ q * I + 2 * a.enc I R - 2 * b.enc I R →
      ∀ t < s, pc t = i → (pc (t + 1) = n ↔ opdOf s rj t a < opdOf s rj t b) := by
    intro i n a b hi hn hni hstop h t ht hpt
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
      have hs2 : 2 ≤ s := by omega
      have h4 : (4 : ℕ) ≤ 2 ^ s := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs2
      have h8 : 4 * (x + 1) ≤ 2 ^ s * (x + 1) := Nat.mul_le_mul_right _ h4
      have hmono : 2 ^ t' * (x + 1) ≤ 2 ^ s * (x + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      cases a with
      | reg j0 =>
        have hg := hgrow t' (by omega) j0
        simp only [opdOf]
        omega
      | zero => simp only [opdOf]; omega
      | one => simp only [opdOf]; rw [if_pos (by omega)]; omega
  -- the main induction
  have hrun : ∀ t ≤ s, xrun P (init r x) t = some ⟨pc t, fun j => rj j t⟩ := by
    intro t
    induction t with
    | zero =>
      intro _
      simp only [xrun, init, Option.some.injEq, Config.mk.injEq]
      refine ⟨hpc0.symm, ?_⟩
      funext j
      exact (hdig0 j).symm
    | succ t ih =>
      intro ht
      have ht' : t < s := by omega
      rw [xrun_succ_of_eq (ih (by omega))]
      obtain ⟨c, hc, hcs⟩ := hcmd t ht'
      have hpcl := (hpc t (by omega)).1
      have hne := hpc_ne t ht'
      unfold xstep
      simp only
      rw [hc]
      have hd := fun j => hdig j t (by omega)
      have hlione : li (pc t) t = 1 := by rw [hli_eq t (by omega) (pc t) hpcl, if_pos rfl]
      cases c with
      | base cb =>
        cases cb with
        | goto k =>
          have hk := hP.goto_lt _ _ hc
          have hcond : 2 ^ q * L (pc t) ≼ L k := H.lines _ _ hc
          have hn := hjump _ k hpcl hk hcond t ht' rfl
          simp only [XCmd.exec, Cmd.exec, Option.some.injEq, Config.mk.injEq]
          refine ⟨hn.symm, ?_⟩
          funext j
          have h1 := hd j
          have hx : xdelta P (pc t) j = 0 := by simp [xdelta, hc]
          have ha : isAdd P (pc t) j = false := by simp [isAdd, hc]
          have hb : isHalf P (pc t) j = false := by simp [isHalf, hc]
          rw [hx, ha, hb] at h1
          simp at h1
          omega
        | arith δ =>
          have hb := hP.arith_ok _ _ hc
          have hcond : 2 ^ q * L (pc t) ≼ L (pc t + 1) := H.lines _ _ hc
          have hn := hjump _ (pc t + 1) hpcl (by omega) hcond t ht' rfl
          simp only [XCmd.exec, Cmd.exec]
          have hxd : ∀ j, xdelta P (pc t) j = δ j := by intro j; simp [xdelta, hc]
          have ha : ∀ j, isAdd P (pc t) j = false := by intro j; simp [isAdd, hc]
          have hh : ∀ j, isHalf P (pc t) j = false := by intro j; simp [isHalf, hc]
          have hd' : ∀ j, rj j (t + 1) + (if δ j = -1 then 1 else 0)
              = rj j t + (if δ j = 1 then 1 else 0) := by
            intro j
            have h1 := hd j
            rw [hxd j, ha j, hh j] at h1
            simpa using h1
          have hδ : ∀ j, 0 ≤ (rj j t : ℤ) + δ j := by
            intro j
            have h1 := hd' j
            have := hb j
            split_ifs at h1 <;> omega
          rw [if_pos hδ]
          simp only [Option.some.injEq, Config.mk.injEq]
          refine ⟨hn.symm, ?_⟩
          funext j
          have h1 := hd' j
          have := hb j
          split_ifs at h1 <;> omega
        | ifLt a b k =>
          obtain ⟨hk, hki, hki1⟩ := hP.ifLt_ok _ a b k hc
          obtain ⟨h1, h2⟩ : (2 ^ q * L (pc t) ≼ L k + L (pc t + 1)) ∧
              (2 ^ q * L (pc t) ≼ L k + 2 ^ q * I + 2 * a.enc I R - 2 * b.enc I R) :=
            H.lines _ _ hc
          have hbr := hbranch _ k (by omega) hk hki1 h1 t ht' rfl
          have hcmp := hcompare _ k a b hpcl hk hki (by rw [hc]; simp) h2 t ht' rfl
          simp only [XCmd.exec, Cmd.exec, Option.some.injEq, Config.mk.injEq]
          refine ⟨?_, ?_⟩
          · rw [hval t (by omega) a, hval t (by omega) b]
            split_ifs with hlt
            · exact (hcmp.2 hlt).symm
            · rcases hbr with h | h
              · exact absurd (hcmp.1 h) hlt
              · exact h.symm
          · funext j
            have h3 := hd j
            have hx : xdelta P (pc t) j = 0 := by simp [xdelta, hc]
            have ha : isAdd P (pc t) j = false := by simp [isAdd, hc]
            have hb' : isHalf P (pc t) j = false := by simp [isHalf, hc]
            rw [hx, ha, hb'] at h3
            simp at h3
            omega
        | ifLe a b k =>
          obtain ⟨hk, hki, hki1⟩ := hP.ifLe_ok _ a b k hc
          obtain ⟨h1, h2⟩ : (2 ^ q * L (pc t) ≼ L k + L (pc t + 1)) ∧
              (2 ^ q * L (pc t) ≼ L (pc t + 1) + 2 ^ q * I + 2 * b.enc I R - 2 * a.enc I R) :=
            H.lines _ _ hc
          have hbr := hbranch _ k (by omega) hk hki1 h1 t ht' rfl
          have hcmp := hcompare _ (pc t + 1) b a hpcl (by omega) (by omega) (by rw [hc]; simp)
            h2 t ht' rfl
          simp only [XCmd.exec, Cmd.exec, Option.some.injEq, Config.mk.injEq]
          refine ⟨?_, ?_⟩
          · rw [hval t (by omega) a, hval t (by omega) b]
            split_ifs with hle
            · rcases hbr with h | h
              · exact h.symm
              · exact absurd (hcmp.1 h) (by omega)
            · exact (hcmp.2 (by omega)).symm
          · funext j
            have h3 := hd j
            have hx : xdelta P (pc t) j = 0 := by simp [xdelta, hc]
            have ha : isAdd P (pc t) j = false := by simp [isAdd, hc]
            have hb' : isHalf P (pc t) j = false := by simp [isHalf, hc]
            rw [hx, ha, hb'] at h3
            simp at h3
            omega
        | stop => exact absurd rfl hcs
      | add a b =>
        have hcond : 2 ^ q * L (pc t) ≼ L (pc t + 1) := H.lines _ _ hc
        have hn := hjump _ (pc t + 1) hpcl (by omega) hcond t ht' rfl
        simp only [XCmd.exec, Option.some.injEq, Config.mk.injEq]
        refine ⟨hn.symm, ?_⟩
        funext j
        have h1 := hd j
        have hx : xdelta P (pc t) j = 0 := by simp [xdelta, hc]
        have hh : isHalf P (pc t) j = false := by simp [isHalf, hc]
        rw [hx, hh] at h1
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
        rw [if_neg (by norm_num : ¬((0 : ℤ) = -1)), if_neg (by norm_num : ¬((0 : ℤ) = 1)),
          Nat.add_zero, Nat.add_zero] at h1
        by_cases hja : j = a
        · subst hja
          have ha : isAdd P (pc t) j = true := by simp [isAdd, hc]
          rw [if_pos ha, hmv_eq (pc t) j b hc t, hlione, mul_one] at h1
          rw [Function.update_self]
          omega
        · have ha : isAdd P (pc t) j = false := by simp [isAdd, hc, Ne.symm hja]
          rw [ha] at h1
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
          rw [Function.update_of_ne hja]
          omega
      | half a =>
        have hcond : 2 ^ q * L (pc t) ≼ L (pc t + 1) := H.lines _ _ hc
        have hn := hjump _ (pc t + 1) hpcl (by omega) hcond t ht' rfl
        simp only [XCmd.exec, Option.some.injEq, Config.mk.injEq]
        refine ⟨hn.symm, ?_⟩
        funext j
        have h1 := hd j
        have hx : xdelta P (pc t) j = 0 := by simp [xdelta, hc]
        have ha : isAdd P (pc t) j = false := by simp [isAdd, hc]
        rw [hx, ha] at h1
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
        rw [if_neg (by norm_num : ¬((0 : ℤ) = -1)), if_neg (by norm_num : ¬((0 : ℤ) = 1)),
          Nat.add_zero] at h1
        by_cases hja : j = a
        · subst hja
          have hh : isHalf P (pc t) j = true := by simp [isHalf, hc]
          rw [if_pos hh, hjv_eq (pc t) j hc t, hlione, mul_one] at h1
          rw [Function.update_self]
          omega
        · have hh : isHalf P (pc t) j = false := by simp [isHalf, hc, Ne.symm hja]
          rw [hh] at h1
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
          rw [Function.update_of_ne hja]
          omega
  rw [hrun s le_rfl]
  simp only [xfinal, Option.some.injEq, Config.mk.injEq]
  exact ⟨hpcs, funext hrj_s⟩

/-- A solution of the extended system gives an accepting computation. -/
theorem xaccepts_of_xsys {P : XProgram r} (hP : XWF P) {x s Q I : ℕ} {R : Fin r → ℕ}
    {L M J : ℕ → ℕ} (H : XSys P x s Q I R L M J) : XAccepts P x :=
  ⟨s, xrun_of_xsys hP H⟩

/-- **The system of §4 is equivalent to acceptance**: a machine with the fast commands (41),
(42) accepts `x` exactly when the extended system (46)–(50) has a solution. -/
theorem xaccepts_iff {r : ℕ} (P : XProgram r) (hP : XWF P) (x : ℕ) :
    XAccepts P x ↔
      ∃ (s Q I : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ), XSys P x s Q I R L M J := by
  refine ⟨xsys_of_accepts hP, ?_⟩
  rintro ⟨s, Q, I, R, L, M, J, H⟩
  exact xaccepts_of_xsys hP H

end RM
end JM1984
