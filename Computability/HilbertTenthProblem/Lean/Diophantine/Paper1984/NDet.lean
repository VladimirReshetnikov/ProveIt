import Diophantine.Paper1984.FastSoundness

/-!
# Jones–Matijasevič 1984, §5: the nondeterministic command (51)

The machines of §4 are extended by the nondeterministic command (51)

  `Ln  BRANCH (Li, Lj)`,

which transfers to `Li` or to `Lj`.  A computation is a run guided by a sequence of choices
`ch : ℕ → Bool`, and `P` accepts `x` when some sequence of choices leads to the accepting
configuration.  Arithmetically a branch line `n` carries the single condition (52)

  `Q L_n ≼ L_i + L_j`   (`i ≠ j`),

read by `branch_iff`: line `n` is not active at the last step, and every step from line `n`
goes to line `i` or to line `j`.  For `i = j` the deterministic condition `Q L_n ≼ L_i` is used
instead, since `L_i + L_i` shifts the bits of the mask rather than duplicating the target.
-/

namespace JM1984
namespace RM

open Finset

variable {r : ℕ}

/-- The commands of §5: those of §4 together with `BRANCH`. -/
inductive NCmd (r : ℕ)
  | ext (c : XCmd r)
  | branch (i j : ℕ)

/-- A program for a nondeterministic register machine. -/
abbrev NProgram (r : ℕ) := List (NCmd r)

/-- One command, executed with the choice bit `ch`. -/
def NCmd.exec (pc : ℕ) (regs : Fin r → ℕ) (ch : Bool) : NCmd r → Option (Config r)
  | .ext c => c.exec pc regs
  | .branch i j => some ⟨if ch then i else j, regs⟩

/-- One step of the machine. -/
def nstep (P : NProgram r) (ch : Bool) (c : Config r) : Option (Config r) :=
  match P[c.pc]? with
  | some cmd => cmd.exec c.pc c.regs ch
  | none => none

/-- The run guided by the choices `ch`. -/
def nrun (P : NProgram r) (ch : ℕ → Bool) (c : Config r) : ℕ → Option (Config r)
  | 0 => some c
  | n + 1 => (nrun P ch c n).bind (nstep P (ch n))

/-- The change of register `j` prescribed by a base arithmetic line. -/
def ndelta (P : NProgram r) (i : ℕ) (j : Fin r) : ℤ :=
  match P[i]? with
  | some (.ext (.base (.arith δ))) => δ j
  | _ => 0

/-- Line `i` adds into register `j`. -/
def nisAdd (P : NProgram r) (i : ℕ) (j : Fin r) : Bool :=
  match P[i]? with
  | some (.ext (.add a _)) => decide (a = j)
  | _ => false

/-- Line `i` halves register `j`. -/
def nisHalf (P : NProgram r) (i : ℕ) (j : Fin r) : Bool :=
  match P[i]? with
  | some (.ext (.half a)) => decide (a = j)
  | _ => false

/-- The condition attached to a line; a branch line carries (52). -/
def nlineCond (Q I : ℕ) (R : Fin r → ℕ) (L : ℕ → ℕ) (i : ℕ) : NCmd r → Prop
  | .ext c => xlineCond Q I R L i c
  | .branch a b => if a = b then Q * L i ≼ L a else Q * L i ≼ L a + L b

/-- The register equation with the contributions of the fast commands. -/
def nregEq (P : NProgram r) (x Q : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ) (j : Fin r) : Prop :=
  R j + ∑ i ∈ range P.length, (if ndelta P i j = -1 then Q * L i else 0)
      + ∑ i ∈ range P.length, (if nisHalf P i j = true then Q * J i else 0)
    = Q * R j + ∑ i ∈ range P.length, (if ndelta P i j = 1 then Q * L i else 0)
      + ∑ i ∈ range P.length, (if nisAdd P i j = true then Q * M i else 0)
      + (if j.val = 0 then x else 0)

/-- Well-formed nondeterministic programs. -/
structure NWF (P : NProgram r) : Prop where
  pos : 0 < P.length
  last_stop : P[P.length - 1]? = some (.ext (.base .stop))
  stop_last : ∀ i : ℕ, P[i]? = some (.ext (.base .stop) : NCmd r) → i = P.length - 1
  goto_lt : ∀ i k : ℕ, P[i]? = some (.ext (.base (.goto k)) : NCmd r) → k < P.length
  ifLt_ok : ∀ (i : ℕ) (a b : Operand r) (k : ℕ),
    P[i]? = some (.ext (.base (.ifLt a b k))) → k < P.length ∧ k ≠ i ∧ k ≠ i + 1
  ifLe_ok : ∀ (i : ℕ) (a b : Operand r) (k : ℕ),
    P[i]? = some (.ext (.base (.ifLe a b k))) → k < P.length ∧ k ≠ i ∧ k ≠ i + 1
  arith_ok : ∀ (i : ℕ) (δ : Fin r → ℤ), P[i]? = some (.ext (.base (.arith δ))) →
    ∀ j, -1 ≤ δ j ∧ δ j ≤ 1
  branch_ok : ∀ (i a b : ℕ), P[i]? = some (.branch a b) → a < P.length ∧ b < P.length

/-- The system for nondeterministic programs. -/
structure NSys (P : NProgram r) (x s Q I : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ) : Prop where
  c46 : 2 * (2 ^ s * (x + 1)) < Q
  c25 : P.length < Q
  c26 : ∃ q, Q = 2 ^ q
  c27 : 1 + (Q - 1) * I = Q ^ (s + 1)
  c29 : ∀ j, R j ≼ (Q / 2 - 1) * I
  c30 : I = ∑ i ∈ range P.length, L i
  c31 : ∀ i < P.length, L i ≼ I
  c32 : 1 ≼ L 0
  c33 : L (P.length - 1) = Q ^ s
  lines : ∀ (i : ℕ) (c : NCmd r), P[i]? = some c → nlineCond Q I R L i c
  addMask : ∀ (i : ℕ) (j k : Fin r), P[i]? = some (.ext (.add j k)) →
    M i ≼ R k ∧ M i ≼ (Q - 1) * L i ∧ R k ≼ (Q - 1) * (I - L i) + M i
  halfMask : ∀ (i : ℕ) (j : Fin r), P[i]? = some (.ext (.half j)) →
    2 * J i ≼ R j ∧ J i ≼ (Q / 2 - 1) * L i ∧ R j ≼ (Q - 1) * (I - L i) + 2 * J i + L i
  regs : ∀ j, nregEq P x Q R L M J j

/-- The accepting configuration. -/
def nfinal (P : NProgram r) : Config r := ⟨P.length - 1, fun _ => 0⟩

/-- `P` accepts `x`: some sequence of choices leads from line `0` with `x` in `R1` to the last
line with all registers zero. -/
def NAccepts (P : NProgram r) (x : ℕ) : Prop :=
  ∃ (ch : ℕ → Bool) (s : ℕ), nrun P ch (init r x) s = some (nfinal P)

/-! ### The trace of a run -/

/-- Register `j` at time `t`. -/
def nregAt (P : NProgram r) (ch : ℕ → Bool) (x : ℕ) (j : Fin r) (t : ℕ) : ℕ :=
  match nrun P ch (init r x) t with
  | some c => c.regs j
  | none => 0

/-- `1` if line `i` is executed at time `t`. -/
def nlinAt (P : NProgram r) (ch : ℕ → Bool) (x : ℕ) (i t : ℕ) : ℕ :=
  match nrun P ch (init r x) t with
  | some c => if c.pc = i then 1 else 0
  | none => 0

/-- The value of an operand at time `t`. -/
def nopdAt (P : NProgram r) (ch : ℕ → Bool) (x : ℕ) (a : Operand r) (t : ℕ) : ℕ :=
  match nrun P ch (init r x) t with
  | some c => a.val c.regs
  | none => 0

/-- The digits of the unknown `M_i` of (48). -/
def nmFun (P : NProgram r) (ch : ℕ → Bool) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.ext (.add _ k)) => nregAt P ch x k t * nlinAt P ch x i t
  | _ => 0

/-- The digits of the unknown `J_i` of (50). -/
def njFun (P : NProgram r) (ch : ℕ → Bool) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.ext (.half j)) => nregAt P ch x j t / 2 * nlinAt P ch x i t
  | _ => 0

/-- The register read by an addition line. -/
def nmHead (P : NProgram r) (ch : ℕ → Bool) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.ext (.add _ k)) => nregAt P ch x k t
  | _ => 0

/-- Half the register of a halving line. -/
def njHead (P : NProgram r) (ch : ℕ → Bool) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.ext (.half j)) => nregAt P ch x j t / 2
  | _ => 0

variable {P : NProgram r} {ch : ℕ → Bool} {x t : ℕ}

theorem nregAt_of_eq {c : Config r} (h : nrun P ch (init r x) t = some c) (j : Fin r) :
    nregAt P ch x j t = c.regs j := by simp [nregAt, h]

theorem nlinAt_of_eq {c : Config r} (h : nrun P ch (init r x) t = some c) (i : ℕ) :
    nlinAt P ch x i t = if c.pc = i then 1 else 0 := by simp [nlinAt, h]

theorem nopdAt_of_eq {c : Config r} (h : nrun P ch (init r x) t = some c) (a : Operand r) :
    nopdAt P ch x a t = a.val c.regs := by simp [nopdAt, h]

theorem nregAt_of_none (h : nrun P ch (init r x) t = none) (j : Fin r) :
    nregAt P ch x j t = 0 := by simp [nregAt, h]

theorem nlinAt_of_none (h : nrun P ch (init r x) t = none) (i : ℕ) :
    nlinAt P ch x i t = 0 := by simp [nlinAt, h]

theorem nopdAt_of_none (h : nrun P ch (init r x) t = none) (a : Operand r) :
    nopdAt P ch x a t = 0 := by simp [nopdAt, h]

theorem nlinAt_le_one (P : NProgram r) (ch : ℕ → Bool) (x i t : ℕ) : nlinAt P ch x i t ≤ 1 := by
  unfold nlinAt
  split
  · split_ifs <;> omega
  · omega

theorem nrun_succ (P : NProgram r) (ch : ℕ → Bool) (c : Config r) (n : ℕ) :
    nrun P ch c (n + 1) = (nrun P ch c n).bind (nstep P (ch n)) := rfl

theorem nrun_succ_of_eq {c d : Config r} {n : ℕ} (h : nrun P ch c n = some d) :
    nrun P ch c (n + 1) = nstep P (ch n) d := by rw [nrun_succ, h]; rfl

theorem nrun_isSome_of_le {c d : Config r} {s : ℕ} (h : nrun P ch c s = some d) :
    ∀ t ≤ s, ∃ e, nrun P ch c t = some e := by
  intro t ht
  induction s generalizing d with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact ⟨c, rfl⟩
  | succ s ih =>
    rcases Nat.eq_or_lt_of_le ht with rfl | hlt
    · exact ⟨d, h⟩
    · rw [nrun_succ] at h
      cases hs : nrun P ch c s with
      | none => rw [hs] at h; simp at h
      | some e => exact ih hs (by omega)

theorem npc_lt_of_step {b : Bool} {d e : Config r} (h : nstep P b d = some e) :
    d.pc < P.length ∧ P[d.pc]? ≠ some (.ext (.base .stop)) := by
  unfold nstep at h
  cases hp : P[d.pc]? with
  | none => rw [hp] at h; simp at h
  | some cmd =>
    rw [hp] at h
    refine ⟨List.getElem?_eq_some_iff.1 hp |>.1, ?_⟩
    intro hc
    have hcmd : cmd = NCmd.ext (.base Cmd.stop) := Option.some.inj hc
    subst hcmd
    simp [NCmd.exec, XCmd.exec, Cmd.exec] at h

theorem nstep_final (hP : NWF P) (b : Bool) : nstep P b (nfinal P) = none := by
  unfold nstep
  simp [nfinal, hP.last_stop, NCmd.exec, XCmd.exec, Cmd.exec]

theorem nrun_none_of_gt (hP : NWF P) {s : ℕ} (hs : nrun P ch (init r x) s = some (nfinal P)) :
    ∀ t, s < t → nrun P ch (init r x) t = none := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge s t with h | h
    · rw [nrun_succ, ih h]; rfl
    · have : t = s := by omega
      subst this
      rw [nrun_succ_of_eq hs, nstep_final hP]

/-- Registers at most double at each step. -/
theorem nregs_run_le (hP : NWF P) : ∀ {t : ℕ} {c : Config r},
    nrun P ch (init r x) t = some c → ∀ j, c.regs j + 1 ≤ 2 ^ t * (x + 1) := by
  intro t
  induction t with
  | zero =>
    intro c h j
    cases h
    simp only [init, pow_zero, one_mul]
    split_ifs <;> omega
  | succ t ih =>
    intro c h j
    rw [nrun_succ] at h
    cases hd : nrun P ch (init r x) t with
    | none => rw [hd] at h; simp at h
    | some d =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      have hle := ih hd
      have hA1 : 1 ≤ 2 ^ t * (x + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      have hAA : 2 ^ (t + 1) * (x + 1) = 2 * (2 ^ t * (x + 1)) := by ring
      have hmono : ∀ u : ℕ, u + 1 ≤ 2 ^ t * (x + 1) → u + 1 ≤ 2 ^ (t + 1) * (x + 1) := by
        intro u hu; rw [hAA]; omega
      have hsucc : ∀ u : ℕ, u + 1 ≤ 2 ^ t * (x + 1) → u + 1 + 1 ≤ 2 ^ (t + 1) * (x + 1) := by
        intro u hu; rw [hAA]; omega
      have hadd : ∀ u v : ℕ, u + 1 ≤ 2 ^ t * (x + 1) → v + 1 ≤ 2 ^ t * (x + 1) →
          u + v + 1 ≤ 2 ^ (t + 1) * (x + 1) := by
        intro u v hu hv; rw [hAA]; omega
      unfold nstep at h
      cases hp : P[d.pc]? with
      | none => rw [hp] at h; simp at h
      | some cmd =>
        rw [hp] at h
        cases cmd with
        | ext xc =>
          cases xc with
          | base cb =>
            cases cb with
            | goto k =>
              simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at h
              rw [← h]; exact hmono _ (hle j)
            | ifLt a b k =>
              simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at h
              rw [← h]; exact hmono _ (hle j)
            | ifLe a b k =>
              simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at h
              rw [← h]; exact hmono _ (hle j)
            | arith δ =>
              simp only [NCmd.exec, XCmd.exec, Cmd.exec] at h
              split_ifs at h with hδ
              simp only [Option.some.injEq] at h
              rw [← h]
              simp only
              have hb := hP.arith_ok _ _ hp j
              have hj := hle j
              have hδj := hδ j
              have : ((d.regs j : ℤ) + δ j).toNat ≤ d.regs j + 1 := by omega
              exact le_trans (by omega) (hsucc _ hj)
            | stop => simp [NCmd.exec, XCmd.exec, Cmd.exec] at h
          | add a b =>
            simp only [NCmd.exec, XCmd.exec, Option.some.injEq] at h
            rw [← h]
            simp only
            by_cases hj : j = a
            · subst hj
              rw [Function.update_self]
              exact hadd _ _ (hle j) (hle b)
            · rw [Function.update_of_ne hj]
              exact hmono _ (hle j)
          | half a =>
            simp only [NCmd.exec, XCmd.exec, Option.some.injEq] at h
            rw [← h]
            simp only
            by_cases hj : j = a
            · subst hj
              rw [Function.update_self]
              have hj := hle j
              exact le_trans (by omega) (hmono _ hj)
            · rw [Function.update_of_ne hj]
              exact hmono _ (hle j)
        | branch a b =>
          simp only [NCmd.exec, Option.some.injEq] at h
          rw [← h]
          exact hmono _ (hle j)

theorem nmFun_eq (P : NProgram r) (ch : ℕ → Bool) (x i t : ℕ) :
    nmFun P ch x i t = nmHead P ch x i t * nlinAt P ch x i t := by
  unfold nmFun nmHead
  cases P[i]? with
  | none => simp
  | some c => cases c with
    | ext xc => cases xc <;> simp
    | branch a b => simp

theorem njFun_eq (P : NProgram r) (ch : ℕ → Bool) (x i t : ℕ) :
    njFun P ch x i t = njHead P ch x i t * nlinAt P ch x i t := by
  unfold njFun njHead
  cases P[i]? with
  | none => simp
  | some c => cases c with
    | ext xc => cases xc <;> simp
    | branch a b => simp

set_option maxHeartbeats 4000000 in
/-- An accepting computation of an extended program solves the system. -/
theorem nsys_of_accepts (hP : NWF P) (h : NAccepts P x) :
    ∃ (s Q I : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ), NSys P x s Q I R L M J := by
  obtain ⟨ch, s, hs⟩ := h
  have hlen : 0 < P.length := hP.pos
  generalize hq : s + x + P.length + 3 = q
  have hq2 : 2 ≤ q := by omega
  have hQ0 : 0 < 2 ^ q := by positivity
  have hQ4 : 4 ≤ 2 ^ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
  have hx1 : x + 1 ≤ 2 ^ (x + 1) := by
    have := Nat.lt_two_pow_self (n := x)
    have : 2 ^ x ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h46 : 2 * (2 ^ s * (x + 1)) < 2 ^ q := by
    calc 2 * (2 ^ s * (x + 1)) ≤ 2 * (2 ^ s * 2 ^ (x + 1)) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hx1)
      _ = 2 ^ (s + x + 2) := by rw [← pow_add]; ring
      _ < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h25 : P.length < 2 ^ q :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- facts about the run
  have hsome : ∀ t ≤ s, ∃ c, nrun P ch (init r x) t = some c := nrun_isSome_of_le hs
  have hnone : ∀ t, s < t → nrun P ch (init r x) t = none := nrun_none_of_gt hP hs
  have hstep : ∀ t < s, ∀ c, nrun P ch (init r x) t = some c →
      ∃ c', nrun P ch (init r x) (t + 1) = some c' ∧ nstep P (ch t) c = some c' := by
    intro t ht c hc
    obtain ⟨c', hc'⟩ := hsome (t + 1) (by omega)
    exact ⟨c', hc', by rw [← hc', nrun_succ_of_eq hc]⟩
  have hpc_lt : ∀ t < s, ∀ c, nrun P ch (init r x) t = some c →
      c.pc < P.length ∧ P[c.pc]? ≠ some (.ext (.base .stop)) := by
    intro t ht c hc
    obtain ⟨c', -, hstep'⟩ := hstep t ht c hc
    exact npc_lt_of_step hstep'
  have hpc_ne : ∀ t < s, ∀ c, nrun P ch (init r x) t = some c → c.pc ≠ P.length - 1 := by
    intro t ht c hc heq
    have := (hpc_lt t ht c hc).2
    rw [heq] at this
    exact this hP.last_stop
  have hts_of : ∀ t c, nrun P ch (init r x) t = some c → t ≤ s := by
    intro t c hc
    by_contra hcon
    rw [hnone t (by omega)] at hc
    cases hc
  have hreg_le : ∀ t c, nrun P ch (init r x) t = some c → ∀ j, c.regs j + 1 ≤ 2 ^ t * (x + 1) :=
    fun t c hc j => nregs_run_le hP hc j
  have hreg_bound : ∀ j t, 2 * nregAt P ch x j t < 2 ^ q := by
    intro j t
    cases hc : nrun P ch (init r x) t with
    | none => rw [nregAt_of_none hc]; omega
    | some c =>
      rw [nregAt_of_eq hc]
      have hts := hts_of t c hc
      have hb := hreg_le t c hc j
      have hmono : 2 ^ t * (x + 1) ≤ 2 ^ s * (x + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hts)
      omega
  have hpc_le : ∀ t ≤ s, ∀ c, nrun P ch (init r x) t = some c → c.pc < P.length := by
    intro t ht c hc
    rcases Nat.lt_or_ge t s with h | h
    · exact (hpc_lt t h c hc).1
    · have : t = s := by omega
      subst this
      rw [hs] at hc
      cases hc
      simp [nfinal]; omega
  have huniq : ∀ t ≤ s, ∑ i ∈ range P.length, nlinAt P ch x i t = 1 := by
    intro t ht
    obtain ⟨c, hc⟩ := hsome t ht
    simp only [nlinAt_of_eq hc]
    rw [sum_ite_eq]
    simp [mem_range, hpc_le t ht c hc]
  have hlin_zero : ∀ i t, s < t → nlinAt P ch x i t = 0 := fun i t ht => nlinAt_of_none (hnone t ht) i
  have hreg_zero : ∀ j t, s < t → nregAt P ch x j t = 0 := fun j t ht => nregAt_of_none (hnone t ht) j
  have hexec : ∀ i t, P[i]? ≠ some (.ext (.base .stop)) → nlinAt P ch x i t = 1 →
      ∃ c c', nrun P ch (init r x) t = some c ∧ c.pc = i ∧ t < s ∧
        nrun P ch (init r x) (t + 1) = some c' ∧ nstep P (ch t) c = some c' := by
    intro i t hi hl
    have hts : t ≤ s := by
      by_contra hc
      rw [hlin_zero i t (by omega)] at hl
      omega
    obtain ⟨c, hc⟩ := hsome t hts
    rw [nlinAt_of_eq hc] at hl
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
  refine ⟨s, 2 ^ q, blocks (2 ^ q) (s + 1) (fun _ => 1),
    fun j => blocks (2 ^ q) (s + 1) (nregAt P ch x j),
    fun i => blocks (2 ^ q) (s + 1) (nlinAt P ch x i),
    fun i => blocks (2 ^ q) (s + 1) (nmFun P ch x i),
    fun i => blocks (2 ^ q) (s + 1) (njFun P ch x i), ?_⟩
  have hextL : ∀ i, blocks (2 ^ q) (s + 1) (nlinAt P ch x i) = blocks (2 ^ q) (s + 2) (nlinAt P ch x i) :=
    fun i => (blocks_of_zero_of_ge (by omega) (fun t ht => hlin_zero i t (by omega))).symm
  have hextR : ∀ j, blocks (2 ^ q) (s + 1) (nregAt P ch x j)
      = blocks (2 ^ q) (s + 2) (nregAt P ch x j) :=
    fun j => (blocks_of_zero_of_ge (by omega) (fun t ht => hreg_zero j t (by omega))).symm
  have hlin_lt : ∀ i t, nlinAt P ch x i t < 2 ^ q := fun i t => by
    have := nlinAt_le_one P ch x i t; omega
  have hjump : ∀ i n, P[i]? ≠ some (.ext (.base .stop)) →
      (∀ t c c', nrun P ch (init r x) t = some c → c.pc = i → nstep P (ch t) c = some c' → c'.pc = n) →
      2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼ blocks (2 ^ q) (s + 1) (nlinAt P ch x n) := by
    intro i n hi hn
    rw [blocks_shift, hextL n,
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hlin_lt _ _))
        (fun t _ => hlin_lt _ _), forall_lt_succ']
    simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    refine ⟨zero_mask _, fun t _ => ?_⟩
    rw [mask_of_le_one_iff (nlinAt_le_one _ _ _ _ _)]
    intro hl
    obtain ⟨c, c', hc, hpc, -, hc', hst⟩ := hexec i t hi hl
    rw [nlinAt_of_eq hc', if_pos (hn t c c' hc hpc hst)]
  have henc : ∀ a : Operand r, Operand.enc (blocks (2 ^ q) (s + 1) fun _ => 1)
      (fun j => blocks (2 ^ q) (s + 1) (nregAt P ch x j)) a = blocks (2 ^ q) (s + 1) (nopdAt P ch x a) := by
    intro a
    cases a with
    | reg j =>
      simp only [Operand.enc]
      apply blocks_congr
      intro t _
      cases hc : nrun P ch (init r x) t with
      | none => rw [nregAt_of_none hc, nopdAt_of_none hc]
      | some c => rw [nregAt_of_eq hc, nopdAt_of_eq hc]; rfl
    | zero =>
      simp only [Operand.enc]
      rw [← blocks_const_zero (2 ^ q) (s + 1)]
      apply blocks_congr
      intro t _
      cases hc : nrun P ch (init r x) t with
      | none => rw [nopdAt_of_none hc]
      | some c => rw [nopdAt_of_eq hc]; rfl
    | one =>
      simp only [Operand.enc]
      apply blocks_congr
      intro t ht
      obtain ⟨c, hc⟩ := hsome t (by omega)
      rw [nopdAt_of_eq hc]; rfl
  have hopd_lt : ∀ a t, 2 * nopdAt P ch x a t < 2 ^ q := by
    intro a t
    cases hc : nrun P ch (init r x) t with
    | none => rw [nopdAt_of_none hc]; omega
    | some c =>
      rw [nopdAt_of_eq hc]
      cases a with
      | reg j => simpa only [Operand.val, ← nregAt_of_eq hc] using hreg_bound j t
      | zero => simp only [Operand.val]; omega
      | one => simp only [Operand.val]; omega
  have hopd_le' : ∀ a t, 1 ≤ t → t < s → 2 * nopdAt P ch x a t + 3 ≤ 2 ^ q := by
    intro a t h1 h2
    obtain ⟨c, hc⟩ := hsome t (by omega)
    rw [nopdAt_of_eq hc]
    cases a with
    | reg j =>
      simp only [Operand.val]
      have hb := hreg_le t c hc j
      have hmono : 2 ^ t * (x + 1) ≤ 2 ^ s * (x + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    | zero => simp only [Operand.val]; omega
    | one =>
      simp only [Operand.val]
      have : 2 ^ 4 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hcond1 : ∀ i k m, P[i]? ≠ some (.ext (.base .stop)) → k ≠ m →
      (∀ t c c', nrun P ch (init r x) t = some c → c.pc = i → nstep P (ch t) c = some c' →
        c'.pc = k ∨ c'.pc = m) →
      2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼
        blocks (2 ^ q) (s + 1) (nlinAt P ch x k) + blocks (2 ^ q) (s + 1) (nlinAt P ch x m) := by
    intro i k m hi hk hn
    rw [blocks_shift, hextL k, hextL m, ← blocks_add,
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hlin_lt _ _))
        (fun t _ => by
          have := nlinAt_le_one P ch x k t; have := nlinAt_le_one P ch x m t; omega),
      forall_lt_succ']
    simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    refine ⟨zero_mask _, fun t _ => ?_⟩
    rw [mask_of_le_one_iff (nlinAt_le_one _ _ _ _ _)]
    intro hl
    obtain ⟨c, c', hc, hpc, -, hc', hst⟩ := hexec i t hi hl
    rw [nlinAt_of_eq hc', nlinAt_of_eq hc']
    rcases hn t c c' hc hpc hst with h | h
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h]
  have h29 : ∀ j, blocks (2 ^ q) (s + 1) (nregAt P ch x j) ≼
      (2 ^ q / 2 - 1) * blocks (2 ^ q) (s + 1) (fun _ => 1) := by
    intro j
    rw [← blocks_smul]
    refine (mask_blocks_iff (fun t _ => by have := hreg_bound j t; omega) (fun t _ => ?_)).2 ?_
    · simp only [mul_one]
      have := two_pow_div_two (q := q) (by omega)
      omega
    · intro t _
      simp only [mul_one]
      rw [two_pow_div_two (by omega), mask_two_pow_sub_one_iff]
      have h1 := hreg_bound j t
      have h2 := two_mul_two_pow_div_two (q := q) (by omega)
      rw [two_pow_div_two (by omega)] at h2
      omega
  have h30 : blocks (2 ^ q) (s + 1) (fun _ => 1)
      = ∑ i ∈ range P.length, blocks (2 ^ q) (s + 1) (nlinAt P ch x i) := by
    rw [← blocks_sum]
    apply blocks_congr
    intro t ht
    exact (huniq t (by omega)).symm
  have h31 : ∀ i < P.length, blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼
      blocks (2 ^ q) (s + 1) (fun _ => 1) := by
    intro i _
    refine (mask_blocks_iff (fun t _ => hlin_lt i t) (fun t _ => by omega)).2 ?_
    intro t _
    rw [mask_of_le_one_iff (nlinAt_le_one _ _ _ _ _)]
    intro _
    rfl
  have h32 : 1 ≼ blocks (2 ^ q) (s + 1) (nlinAt P ch x 0) := by
    have key : blocks (2 ^ q) (s + 1) (fun t => if t = 0 then 1 else 0) ≼
        blocks (2 ^ q) (s + 1) (nlinAt P ch x 0) := by
      refine (mask_blocks_iff (fun t _ => by split_ifs <;> omega) (fun t _ => hlin_lt _ _)).2 ?_
      intro t _
      split_ifs with h0
      · subst h0
        rw [nlinAt_of_eq (rfl : nrun P ch (init r x) 0 = some (init r x))]
        simp only [init, if_pos rfl]
        exact Mask.refl 1
      · exact zero_mask _
    rwa [blocks_single (by omega), pow_zero] at key
  have h33 : blocks (2 ^ q) (s + 1) (nlinAt P ch x (P.length - 1)) = (2 ^ q) ^ s := by
    rw [← blocks_single (Q := 2 ^ q) (n := s + 1) (k := s) (by omega)]
    apply blocks_congr
    intro t ht
    rcases Nat.lt_or_ge t s with h | h
    · obtain ⟨c, hc⟩ := hsome t (by omega)
      rw [nlinAt_of_eq hc, if_neg (hpc_ne t h c hc), if_neg (by omega)]
    · have : t = s := by omega
      subst this
      rw [nlinAt_of_eq hs]
      simp [nfinal]
  -- the line conditions
  have hlines : ∀ (i : ℕ) (c : NCmd r), P[i]? = some c →
      nlineCond (2 ^ q) (blocks (2 ^ q) (s + 1) fun _ => 1)
        (fun j => blocks (2 ^ q) (s + 1) (nregAt P ch x j))
        (fun i => blocks (2 ^ q) (s + 1) (nlinAt P ch x i)) i c := by
    intro i c hc
    cases c with
    | ext xc =>
      cases xc with
      | add a b =>
        have hi : P[i]? ≠ some (.ext (.base .stop)) := by rw [hc]; simp
        show 2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼
          blocks (2 ^ q) (s + 1) (nlinAt P ch x (i + 1))
        apply hjump i (i + 1) hi
        intro t c c' _ hpc hst
        unfold nstep at hst
        rw [hpc, hc] at hst
        simp only [NCmd.exec, XCmd.exec, Option.some.injEq] at hst
        rw [← hst]
      | half a =>
        have hi : P[i]? ≠ some (.ext (.base .stop)) := by rw [hc]; simp
        show 2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼
          blocks (2 ^ q) (s + 1) (nlinAt P ch x (i + 1))
        apply hjump i (i + 1) hi
        intro t c c' _ hpc hst
        unfold nstep at hst
        rw [hpc, hc] at hst
        simp only [NCmd.exec, XCmd.exec, Option.some.injEq] at hst
        rw [← hst]
      | base cb =>
        cases cb with
        | goto k =>
          have hi : P[i]? ≠ some (.ext (.base .stop)) := by rw [hc]; simp
          show 2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼ blocks (2 ^ q) (s + 1) (nlinAt P ch x k)
          apply hjump i k hi
          intro t c c' _ hpc hst
          unfold nstep at hst
          rw [hpc, hc] at hst
          simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
          rw [← hst]
        | arith δ =>
          have hi : P[i]? ≠ some (.ext (.base .stop)) := by rw [hc]; simp
          show 2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼
            blocks (2 ^ q) (s + 1) (nlinAt P ch x (i + 1))
          apply hjump i (i + 1) hi
          intro t c c' _ hpc hst
          unfold nstep at hst
          rw [hpc, hc] at hst
          simp only [NCmd.exec, XCmd.exec, Cmd.exec] at hst
          split_ifs at hst
          simp only [Option.some.injEq] at hst
          rw [← hst]
        | stop => trivial
        | ifLt a b k =>
          have hi : P[i]? ≠ some (.ext (.base .stop)) := by rw [hc]; simp
          obtain ⟨hk, hki, hki1⟩ := hP.ifLt_ok i a b k hc
          refine ⟨hcond1 i k (i + 1) hi hki1 ?_, ?_⟩
          · intro t c c' _ hpc hst
            unfold nstep at hst
            rw [hpc, hc] at hst
            simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
            rw [← hst]
            simp only
            split_ifs <;> simp
          · show 2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼
              blocks (2 ^ q) (s + 1) (nlinAt P ch x k) + 2 ^ q * blocks (2 ^ q) (s + 1) (fun _ => 1)
                + 2 * Operand.enc _ _ a - 2 * Operand.enc _ _ b
            rw [henc a, henc b]
            refine (compare_cond rfl hq2 (nlinAt_le_one P ch x i) (nlinAt_le_one P ch x k) ?_ ?_
              (hopd_lt a) (hopd_lt b) ?_).2 ?_
            · intro t hl
              obtain ⟨c, c', hct, hpc, -, -, -⟩ := hexec i t hi hl
              rw [nlinAt_of_eq hct, if_neg (by omega)]
            · intro t hl
              obtain ⟨c, c', -, -, hts, -, -⟩ := hexec i t hi hl
              exact hts
            · intro t h1 h2
              have := nlinAt_le_one P ch x k t
              have := hopd_le' a t h1 h2
              omega
            · intro t hl
              obtain ⟨c, c', hct, hpc, -, hc', hst⟩ := hexec i t hi hl
              unfold nstep at hst
              rw [hpc, hc] at hst
              simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
              rw [nlinAt_of_eq hc', ← hst, nopdAt_of_eq hct, nopdAt_of_eq hct]
              simp only
              by_cases hab : a.val c.regs < b.val c.regs
              · simp [hab]
              · simp [hab, Ne.symm hki1]
        | ifLe a b k =>
          have hi : P[i]? ≠ some (.ext (.base .stop)) := by rw [hc]; simp
          obtain ⟨hk, hki, hki1⟩ := hP.ifLe_ok i a b k hc
          refine ⟨hcond1 i k (i + 1) hi hki1 ?_, ?_⟩
          · intro t c c' _ hpc hst
            unfold nstep at hst
            rw [hpc, hc] at hst
            simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
            rw [← hst]
            simp only
            split_ifs <;> simp
          · show 2 ^ q * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ≼
              blocks (2 ^ q) (s + 1) (nlinAt P ch x (i + 1))
                + 2 ^ q * blocks (2 ^ q) (s + 1) (fun _ => 1)
                + 2 * Operand.enc _ _ b - 2 * Operand.enc _ _ a
            rw [henc a, henc b]
            refine (compare_cond rfl hq2 (nlinAt_le_one P ch x i) (nlinAt_le_one P ch x (i + 1)) ?_ ?_
              (hopd_lt b) (hopd_lt a) ?_).2 ?_
            · intro t hl
              obtain ⟨c, c', hct, hpc, -, -, -⟩ := hexec i t hi hl
              rw [nlinAt_of_eq hct, if_neg (by omega)]
            · intro t hl
              obtain ⟨c, c', -, -, hts, -, -⟩ := hexec i t hi hl
              exact hts
            · intro t h1 h2
              have := nlinAt_le_one P ch x (i + 1) t
              have := hopd_le' b t h1 h2
              omega
            · intro t hl
              obtain ⟨c, c', hct, hpc, -, hc', hst⟩ := hexec i t hi hl
              unfold nstep at hst
              rw [hpc, hc] at hst
              simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
              rw [nlinAt_of_eq hc', ← hst, nopdAt_of_eq hct, nopdAt_of_eq hct]
              simp only
              by_cases hab : a.val c.regs ≤ b.val c.regs
              · simp [hab, hki1]
              · have := Nat.lt_of_not_le hab
                simp [hab, this]
    | branch a b =>
      have hi : P[i]? ≠ some (.ext (.base .stop)) := by rw [hc]; simp
      have hbr : ∀ t c c', nrun P ch (init r x) t = some c → c.pc = i →
          nstep P (ch t) c = some c' → c'.pc = a ∨ c'.pc = b := by
        intro t c c' _ hpc hst
        unfold nstep at hst
        rw [hpc, hc] at hst
        simp only [NCmd.exec, Option.some.injEq] at hst
        rw [← hst]
        simp only
        split_ifs <;> simp
      simp only [nlineCond]
      split_ifs with hab
      · subst hab
        refine hjump i a hi (fun t c c' hc0 hpc hst => ?_)
        rcases hbr t c c' hc0 hpc hst with h | h <;> exact h
      · exact hcond1 i a b hi hab hbr
  -- (47) and (49)
  have haddMask : ∀ (i : ℕ) (j k : Fin r), P[i]? = some (.ext (.add j k)) →
      blocks (2 ^ q) (s + 1) (nmFun P ch x i) ≼ blocks (2 ^ q) (s + 1) (nregAt P ch x k) ∧
      blocks (2 ^ q) (s + 1) (nmFun P ch x i) ≼
        (2 ^ q - 1) * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ∧
      blocks (2 ^ q) (s + 1) (nregAt P ch x k) ≼
        (2 ^ q - 1) * (blocks (2 ^ q) (s + 1) (fun _ => 1)
          - blocks (2 ^ q) (s + 1) (nlinAt P ch x i)) + blocks (2 ^ q) (s + 1) (nmFun P ch x i) := by
    intro i j k hp
    refine (mask47_iff (q := q) (n := s + 1) (fun t _ => by have := hreg_bound k t; omega)
      (fun t _ => nlinAt_le_one P ch x i t) _).2 ?_
    apply blocks_congr
    intro t _
    simp only [nmFun, hp]
  have hhalfMask : ∀ (i : ℕ) (j : Fin r), P[i]? = some (.ext (.half j)) →
      2 * blocks (2 ^ q) (s + 1) (njFun P ch x i) ≼ blocks (2 ^ q) (s + 1) (nregAt P ch x j) ∧
      blocks (2 ^ q) (s + 1) (njFun P ch x i) ≼
        (2 ^ q / 2 - 1) * blocks (2 ^ q) (s + 1) (nlinAt P ch x i) ∧
      blocks (2 ^ q) (s + 1) (nregAt P ch x j) ≼
        (2 ^ q - 1) * (blocks (2 ^ q) (s + 1) (fun _ => 1)
          - blocks (2 ^ q) (s + 1) (nlinAt P ch x i)) + 2 * blocks (2 ^ q) (s + 1) (njFun P ch x i)
          + blocks (2 ^ q) (s + 1) (nlinAt P ch x i) := by
    intro i j hp
    refine (mask49_iff (q := q) (n := s + 1) (by omega)
      (fun t _ => by have := hreg_bound j t; omega)
      (fun t _ => nlinAt_le_one P ch x i t) _).2 ?_
    apply blocks_congr
    intro t _
    simp only [njFun, hp]
  -- the register equations
  have hlin_eq : ∀ t c, nrun P ch (init r x) t = some c →
      ∀ i, nlinAt P ch x i t = if i = c.pc then 1 else 0 := by
    intro t c hc i
    rw [nlinAt_of_eq hc]
    simp only [eq_comm]
  have hsum_one : ∀ (t : ℕ) (c : Config r), nrun P ch (init r x) t = some c → c.pc < P.length →
      ∀ (p : ℕ → Bool) (g : ℕ → ℕ → ℕ),
        ∑ i ∈ range P.length, (if p i = true then g i t * nlinAt P ch x i t else 0)
          = if p c.pc = true then g c.pc t else 0 := by
    intro t c hc hpc p g
    rw [sum_eq_single c.pc]
    · rw [hlin_eq t c hc c.pc, if_pos rfl, mul_one]
    · intro i _ hi
      rw [hlin_eq t c hc i, if_neg hi, mul_zero]
      simp
    · intro h; exact absurd (mem_range.2 hpc) h
  have hregs : ∀ j, nregEq P x (2 ^ q) (fun j => blocks (2 ^ q) (s + 1) (nregAt P ch x j))
      (fun i => blocks (2 ^ q) (s + 1) (nlinAt P ch x i))
      (fun i => blocks (2 ^ q) (s + 1) (nmFun P ch x i))
      (fun i => blocks (2 ^ q) (s + 1) (njFun P ch x i)) j := by
    intro j
    unfold nregEq
    simp only
    rw [sum_ite_mul_blocks, sum_ite_mul_blocks, sum_ite_mul_blocks, sum_ite_mul_blocks,
      blocks_shift, blocks_shift, blocks_shift, blocks_shift, blocks_shift, hextR j]
    have hx0 : (if j.val = 0 then x else 0)
        = blocks (2 ^ q) (s + 2) (fun t => if t = 0 then (if j.val = 0 then x else 0) else 0) := by
      rw [blocks_single_mul (by omega)]; simp
    rw [hx0, ← blocks_add, ← blocks_add, ← blocks_add, ← blocks_add, ← blocks_add]
    apply blocks_congr
    intro t ht
    cases t with
    | zero =>
      simp only [↓reduceIte, Nat.zero_add, Nat.add_zero]
      rw [nregAt_of_eq (rfl : nrun P ch (init r x) 0 = some (init r x))]
      rfl
    | succ t =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
      have hts : t ≤ s := by omega
      obtain ⟨c, hc⟩ := hsome t hts
      have hpcl := hpc_le t hts c hc
      have hlin : ∀ i, nlinAt P ch x i t = if i = c.pc then 1 else 0 := hlin_eq t c hc
      have hM := hsum_one t c hc hpcl (fun i => nisAdd P i j) (nmHead P ch x)
      have hJ := hsum_one t c hc hpcl (fun i => nisHalf P i j) (njHead P ch x)
      simp only [← nmFun_eq] at hM
      simp only [← njFun_eq] at hJ
      rw [sum_ite_indicator hpcl _ _ hlin, sum_ite_indicator hpcl _ _ hlin, hM, hJ,
        nregAt_of_eq hc]
      rcases Nat.lt_or_ge t s with hlt | hge
      · obtain ⟨c', hc', hst⟩ := hstep t hlt c hc
        rw [nregAt_of_eq hc']
        unfold nstep at hst
        cases hp : P[c.pc]? with
        | none => rw [hp] at hst; simp at hst
        | some cmd =>
          rw [hp] at hst
          cases cmd with
          | ext xc =>
            cases xc with
            | base cb =>
              cases cb with
              | goto k =>
                simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
                simp [ndelta, nisAdd, nisHalf, hp, ← hst]
              | ifLt a b k =>
                simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
                simp [ndelta, nisAdd, nisHalf, hp, ← hst]
              | ifLe a b k =>
                simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq] at hst
                simp [ndelta, nisAdd, nisHalf, hp, ← hst]
              | arith δ =>
                simp only [NCmd.exec, XCmd.exec, Cmd.exec] at hst
                split_ifs at hst with hδ
                simp only [Option.some.injEq] at hst
                have hδj := hδ j
                have hb := hP.arith_ok _ _ hp j
                simp only [ndelta, nisAdd, nisHalf, hp, ← hst, Bool.false_eq_true, ↓reduceIte,
                  Nat.add_zero, Nat.zero_add]
                split_ifs <;> omega
              | stop => simp [NCmd.exec, XCmd.exec, Cmd.exec] at hst
            | add a b =>
              simp only [NCmd.exec, XCmd.exec, Option.some.injEq] at hst
              by_cases hja : j = a
              · subst hja
                simp [ndelta, nisAdd, nisHalf, nmHead, njHead, hp, ← hst, Function.update_self,
                  nregAt_of_eq hc]
              · simp [ndelta, nisAdd, nisHalf, nmHead, njHead, hp, ← hst,
                  Function.update_of_ne hja, Ne.symm hja]
            | half a =>
              simp only [NCmd.exec, XCmd.exec, Option.some.injEq] at hst
              by_cases hja : j = a
              · subst hja
                simp only [ndelta, nisAdd, nisHalf, nmHead, njHead, hp, ← hst, Function.update_self,
                  decide_true, if_true, Bool.false_eq_true, ↓reduceIte, nregAt_of_eq hc,
                  Nat.add_zero, Nat.zero_add]
                norm_num
                omega
              · simp [ndelta, nisAdd, nisHalf, nmHead, njHead, hp, ← hst,
                  Function.update_of_ne hja, Ne.symm hja]
          | branch a b =>
            simp only [NCmd.exec, Option.some.injEq] at hst
            simp [ndelta, nisAdd, nisHalf, hp, ← hst]
      · have hts' : t = s := by omega
        rw [hts', hs] at hc
        cases hc
        rw [hts', hreg_zero j (s + 1) (by omega)]
        simp [ndelta, nisAdd, nisHalf, nmHead, njHead, nfinal, hP.last_stop]
  exact {
    c46 := h46
    c25 := h25
    c26 := ⟨q, rfl⟩
    c27 := geom_blocks (by omega) (s + 1)
    c29 := h29
    c30 := h30
    c31 := h31
    c32 := h32
    c33 := h33
    lines := hlines
    addMask := haddMask
    halfMask := hhalfMask
    regs := hregs }


set_option maxHeartbeats 4000000 in
/-- A solution of the extended system describes the accepting computation: the machine reaches
the accepting configuration at time `s`. -/
theorem naccepts_of_nsys {P : NProgram r} (hP : NWF P) {x s Q I : ℕ} {R : Fin r → ℕ}
    {L M J : ℕ → ℕ} (H : NSys P x s Q I R L M J) : NAccepts P x := by
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
  -- the sequence of choices read off from the line indicators
  obtain ⟨ch, hch⟩ : ∃ ch : ℕ → Bool, ch = fun t =>
      match P[pc t]? with
      | some (.branch a _) => decide (pc (t + 1) = a)
      | _ => true := ⟨_, rfl⟩
  have hch_branch : ∀ t a b, P[pc t]? = some (.branch a b) →
      ch t = decide (pc (t + 1) = a) := by
    intro t a b hb
    simp only [hch, hb]
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
  have hcmd : ∀ t < s, ∃ c, P[pc t]? = some c ∧ c ≠ (NCmd.ext (.base Cmd.stop) : NCmd r) := by
    intro t ht
    have hlt := (hpc t (by omega)).1
    refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
    intro hstop
    exact hpc_ne t ht (hP.stop_last _ (by rw [List.getElem?_eq_getElem hlt, hstop]))
  -- which lines add into, or halve, a register
  have hisAdd : ∀ (i : ℕ) (j : Fin r), nisAdd P i j = true →
      ∃ b, P[i]? = some (.ext (.add j b)) := by
    intro i j h
    unfold nisAdd at h
    cases hp : P[i]? with
    | none => rw [hp] at h; simp at h
    | some c =>
      rw [hp] at h
      cases c with
      | ext xc =>
        cases xc with
        | base c' => simp at h
        | add a b =>
          simp only [decide_eq_true_eq] at h
          subst h
          exact ⟨b, rfl⟩
        | half a => simp at h
      | branch a b => simp at h
  have hisHalf : ∀ (i : ℕ) (j : Fin r), nisHalf P i j = true →
      P[i]? = some (.ext (.half j)) := by
    intro i j h
    unfold nisHalf at h
    cases hp : P[i]? with
    | none => rw [hp] at h; simp at h
    | some c =>
      rw [hp] at h
      cases c with
      | ext xc =>
        cases xc with
        | base c' => simp at h
        | add a b => simp at h
        | half a =>
          simp only [decide_eq_true_eq] at h
          subst h
          rfl
      | branch a b => simp at h
  -- (47)–(50): the blocks of `M_i` and `J_i`
  obtain ⟨mv, hmv_def⟩ : ∃ mv : ℕ → ℕ → ℕ, mv = fun i t => digit (2 ^ q) (M i) t := ⟨_, rfl⟩
  obtain ⟨jv, hjv_def⟩ : ∃ jv : ℕ → ℕ → ℕ, jv = fun i t => digit (2 ^ q) (J i) t := ⟨_, rfl⟩
  have hmv_eq : ∀ (i : ℕ) (a b : Fin r), P[i]? = some (.ext (.add a b)) → ∀ t,
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
  have hjv_eq : ∀ (i : ℕ) (a : Fin r), P[i]? = some (.ext (.half a)) → ∀ t,
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
  have hMb : ∀ (i : ℕ) (a b : Fin r), P[i]? = some (.ext (.add a b)) →
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
  have hJb : ∀ (i : ℕ) (a : Fin r), P[i]? = some (.ext (.half a)) →
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
      (∑ i ∈ range P.length, if p (ndelta P i j) then li i t else 0)
        = if p (ndelta P (pc t) j) then 1 else 0 := by
    intro p _ j t ht
    rw [sum_congr rfl (fun i hi => by rw [hli_eq t ht i (mem_range.1 hi)])]
    exact sum_ite_indicator (hpc t ht).1 _ _ (fun i => rfl)
  have hdec_zero_gen : ∀ (p : ℤ → Prop) [DecidablePred p] (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if p (ndelta P i j) then li i t else 0) = 0 := by
    intro p _ j t ht
    apply sum_eq_zero
    intro i hi
    rw [hli_zero i (mem_range.1 hi) t ht]
    simp
  have hdecm : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if ndelta P i j = -1 then li i t else 0)
        = if ndelta P (pc t) j = -1 then 1 else 0 := hdec_gen (fun d => d = -1)
  have hdecp : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if ndelta P i j = 1 then li i t else 0)
        = if ndelta P (pc t) j = 1 then 1 else 0 := hdec_gen (fun d => d = 1)
  have hdecm0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if ndelta P i j = -1 then li i t else 0) = 0 :=
    hdec_zero_gen (fun d => d = -1)
  have hdecp0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if ndelta P i j = 1 then li i t else 0) = 0 :=
    hdec_zero_gen (fun d => d = 1)
  have hdecM : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if nisAdd P i j = true then mv i t else 0)
        = if nisAdd P (pc t) j = true then mv (pc t) t else 0 := by
    intro j t ht
    refine sum_eq_single_of_mem (pc t) (mem_range.2 (hpc t ht).1) (fun i hi hne => ?_)
    by_cases hadd : nisAdd P i j = true
    · rw [if_pos hadd]
      obtain ⟨b, hb⟩ := hisAdd i j hadd
      rw [hmv_eq i j b hb t, hli_eq t ht i (mem_range.1 hi), if_neg hne, mul_zero]
    · rw [if_neg hadd]
  have hdecJ : ∀ (j : Fin r), ∀ t ≤ s,
      (∑ i ∈ range P.length, if nisHalf P i j = true then jv i t else 0)
        = if nisHalf P (pc t) j = true then jv (pc t) t else 0 := by
    intro j t ht
    refine sum_eq_single_of_mem (pc t) (mem_range.2 (hpc t ht).1) (fun i hi hne => ?_)
    by_cases hhalf' : nisHalf P i j = true
    · rw [if_pos hhalf']
      have hb := hisHalf i j hhalf'
      rw [hjv_eq i j hb t, hli_eq t ht i (mem_range.1 hi), if_neg hne, mul_zero]
    · rw [if_neg hhalf']
  have hdecM0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if nisAdd P i j = true then mv i t else 0) = 0 := by
    intro j t ht
    refine sum_eq_zero fun i hi => ?_
    by_cases hadd : nisAdd P i j = true
    · rw [if_pos hadd]
      obtain ⟨b, hb⟩ := hisAdd i j hadd
      rw [hmv_eq i j b hb t, hli_zero i (mem_range.1 hi) t ht, mul_zero]
    · rw [if_neg hadd]
  have hdecJ0 : ∀ (j : Fin r), ∀ t, s < t →
      (∑ i ∈ range P.length, if nisHalf P i j = true then jv i t else 0) = 0 := by
    intro j t ht
    refine sum_eq_zero fun i hi => ?_
    by_cases hhalf' : nisHalf P i j = true
    · rw [if_pos hhalf']
      have hb := hisHalf i j hhalf'
      rw [hjv_eq i j hb t, hli_zero i (mem_range.1 hi) t ht, mul_zero]
    · rw [if_neg hhalf']
  -- the sizes of the contributions of the fast commands
  have hJval : ∀ (j : Fin r) (t : ℕ), t ≤ s →
      (if nisHalf P (pc t) j = true then jv (pc t) t else 0) ≤ rj j t / 2 := by
    intro j t ht
    split_ifs with hh
    · have hp := hisHalf (pc t) j hh
      rw [hjv_eq (pc t) j hp t]
      exact hmul_le _ _ (hli_le (pc t) (hpc t ht).1 t)
    · omega
  have hMlt : ∀ (j : Fin r) (t : ℕ), t ≤ s →
      2 * (if nisAdd P (pc t) j = true then mv (pc t) t else 0) < 2 ^ q := by
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
              else ∑ i ∈ range P.length, if ndelta P i j = -1 then li i (t - 1) else 0)
          + (if t = 0 then 0
              else ∑ i ∈ range P.length, if nisHalf P i j = true then jv i (t - 1) else 0)
        = (if t = 0 then 0 else rj j (t - 1))
          + (if t = 0 then 0
              else ∑ i ∈ range P.length, if ndelta P i j = 1 then li i (t - 1) else 0)
          + (if t = 0 then 0
              else ∑ i ∈ range P.length, if nisAdd P i j = true then mv i (t - 1) else 0)
          + (if t = 0 then (if j.val = 0 then x else 0) else 0) := by
    intro j
    have h := H.regs j
    unfold nregEq at h
    have hS1 : ∑ i ∈ range P.length, (if ndelta P i j = -1 then 2 ^ q * L i else 0)
        = ∑ i ∈ range P.length,
            (if ndelta P i j = -1 then 2 ^ q * blocks (2 ^ q) (s + 1) (li i) else 0) :=
      sum_congr rfl (fun i hi => by rw [hL i (mem_range.1 hi)])
    have hS2 : ∑ i ∈ range P.length, (if ndelta P i j = 1 then 2 ^ q * L i else 0)
        = ∑ i ∈ range P.length,
            (if ndelta P i j = 1 then 2 ^ q * blocks (2 ^ q) (s + 1) (li i) else 0) :=
      sum_congr rfl (fun i hi => by rw [hL i (mem_range.1 hi)])
    have hSM : ∑ i ∈ range P.length, (if nisAdd P i j = true then 2 ^ q * M i else 0)
        = ∑ i ∈ range P.length,
            (if nisAdd P i j = true then 2 ^ q * blocks (2 ^ q) (s + 1) (mv i) else 0) := by
      refine sum_congr rfl fun i _ => ?_
      by_cases hadd : nisAdd P i j = true
      · obtain ⟨b, hb⟩ := hisAdd i j hadd
        rw [if_pos hadd, if_pos hadd, hMb i j b hb]
      · rw [if_neg hadd, if_neg hadd]
    have hSJ : ∑ i ∈ range P.length, (if nisHalf P i j = true then 2 ^ q * J i else 0)
        = ∑ i ∈ range P.length,
            (if nisHalf P i j = true then 2 ^ q * blocks (2 ^ q) (s + 1) (jv i) else 0) := by
      refine sum_congr rfl fun i _ => ?_
      by_cases hh : nisHalf P i j = true
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
      rj j (t + 1) + (if ndelta P (pc t) j = -1 then 1 else 0)
          + (if nisHalf P (pc t) j = true then jv (pc t) t else 0)
        = rj j t + (if ndelta P (pc t) j = 1 then 1 else 0)
          + (if nisAdd P (pc t) j = true then mv (pc t) t else 0) := by
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
      have hM : (if nisAdd P (pc t) j = true then mv (pc t) t else 0) + 1 ≤ 2 ^ t * (x + 1) := by
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
    have hd : ndelta P (pc s) j = 0 := by simp [ndelta, hpcs, hP.last_stop]
    have ha : nisAdd P (pc s) j = false := by simp [nisAdd, hpcs, hP.last_stop]
    have hb : nisHalf P (pc s) j = false := by simp [nisHalf, hpcs, hP.last_stop]
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
  have hbranch : ∀ i k m, i < P.length → k < P.length → m < P.length → k ≠ m →
      2 ^ q * L i ≼ L k + L m →
      ∀ t < s, pc t = i → pc (t + 1) = k ∨ pc (t + 1) = m := by
    intro i k m hi hk hm hki h t ht hpt
    rw [hL i hi, hL k hk, hL m hm, blocks_shift,
      ← blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => hli_zero k hk t (by omega)),
      ← blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => hli_zero m hm t (by omega)),
      ← blocks_add,
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hli_digit _ _))
        (fun t _ => by have := hli_le k hk t; have := hli_le m hm t; omega)] at h
    have := h (t + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [mask_of_le_one_iff (hli_le i hi t)] at this
    have h1 := this (by rw [hli_eq t (by omega) i hi, if_pos hpt.symm])
    rw [hli_eq (t + 1) (by omega) k hk, hli_eq (t + 1) (by omega) m hm] at h1
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
      P[i]? ≠ some (.ext (.base Cmd.stop) : NCmd r) →
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
  have hrun : ∀ t ≤ s, nrun P ch (init r x) t = some ⟨pc t, fun j => rj j t⟩ := by
    intro t
    induction t with
    | zero =>
      intro _
      simp only [nrun, init, Option.some.injEq, Config.mk.injEq]
      refine ⟨hpc0.symm, ?_⟩
      funext j
      exact (hdig0 j).symm
    | succ t ih =>
      intro ht
      have ht' : t < s := by omega
      rw [nrun_succ_of_eq (ih (by omega))]
      obtain ⟨c, hc, hcs⟩ := hcmd t ht'
      have hpcl := (hpc t (by omega)).1
      have hne := hpc_ne t ht'
      unfold nstep
      simp only
      rw [hc]
      have hd := fun j => hdig j t (by omega)
      have hlione : li (pc t) t = 1 := by rw [hli_eq t (by omega) (pc t) hpcl, if_pos rfl]
      cases c with
      | ext xc =>
        cases xc with
        | base cb =>
          cases cb with
          | goto k =>
            have hk := hP.goto_lt _ _ hc
            have hcond : 2 ^ q * L (pc t) ≼ L k := H.lines _ _ hc
            have hn := hjump _ k hpcl hk hcond t ht' rfl
            simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq, Config.mk.injEq]
            refine ⟨hn.symm, ?_⟩
            funext j
            have h1 := hd j
            have hx : ndelta P (pc t) j = 0 := by simp [ndelta, hc]
            have ha : nisAdd P (pc t) j = false := by simp [nisAdd, hc]
            have hb : nisHalf P (pc t) j = false := by simp [nisHalf, hc]
            rw [hx, ha, hb] at h1
            simp at h1
            omega
          | arith δ =>
            have hb := hP.arith_ok _ _ hc
            have hcond : 2 ^ q * L (pc t) ≼ L (pc t + 1) := H.lines _ _ hc
            have hn := hjump _ (pc t + 1) hpcl (by omega) hcond t ht' rfl
            simp only [NCmd.exec, XCmd.exec, Cmd.exec]
            have hxd : ∀ j, ndelta P (pc t) j = δ j := by intro j; simp [ndelta, hc]
            have ha : ∀ j, nisAdd P (pc t) j = false := by intro j; simp [nisAdd, hc]
            have hh : ∀ j, nisHalf P (pc t) j = false := by intro j; simp [nisHalf, hc]
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
            have hbr := hbranch _ k (pc t + 1) hpcl hk (by omega) hki1 h1 t ht' rfl
            have hcmp := hcompare _ k a b hpcl hk hki (by rw [hc]; simp) h2 t ht' rfl
            simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq, Config.mk.injEq]
            refine ⟨?_, ?_⟩
            · rw [hval t (by omega) a, hval t (by omega) b]
              split_ifs with hlt
              · exact (hcmp.2 hlt).symm
              · rcases hbr with h | h
                · exact absurd (hcmp.1 h) hlt
                · exact h.symm
            · funext j
              have h3 := hd j
              have hx : ndelta P (pc t) j = 0 := by simp [ndelta, hc]
              have ha : nisAdd P (pc t) j = false := by simp [nisAdd, hc]
              have hb' : nisHalf P (pc t) j = false := by simp [nisHalf, hc]
              rw [hx, ha, hb'] at h3
              simp at h3
              omega
          | ifLe a b k =>
            obtain ⟨hk, hki, hki1⟩ := hP.ifLe_ok _ a b k hc
            obtain ⟨h1, h2⟩ : (2 ^ q * L (pc t) ≼ L k + L (pc t + 1)) ∧
                (2 ^ q * L (pc t) ≼ L (pc t + 1) + 2 ^ q * I + 2 * b.enc I R - 2 * a.enc I R) :=
              H.lines _ _ hc
            have hbr := hbranch _ k (pc t + 1) hpcl hk (by omega) hki1 h1 t ht' rfl
            have hcmp := hcompare _ (pc t + 1) b a hpcl (by omega) (by omega) (by rw [hc]; simp)
              h2 t ht' rfl
            simp only [NCmd.exec, XCmd.exec, Cmd.exec, Option.some.injEq, Config.mk.injEq]
            refine ⟨?_, ?_⟩
            · rw [hval t (by omega) a, hval t (by omega) b]
              split_ifs with hle
              · rcases hbr with h | h
                · exact h.symm
                · exact absurd (hcmp.1 h) (by omega)
              · exact (hcmp.2 (by omega)).symm
            · funext j
              have h3 := hd j
              have hx : ndelta P (pc t) j = 0 := by simp [ndelta, hc]
              have ha : nisAdd P (pc t) j = false := by simp [nisAdd, hc]
              have hb' : nisHalf P (pc t) j = false := by simp [nisHalf, hc]
              rw [hx, ha, hb'] at h3
              simp at h3
              omega
          | stop => exact absurd rfl hcs
        | add a b =>
          have hcond : 2 ^ q * L (pc t) ≼ L (pc t + 1) := H.lines _ _ hc
          have hn := hjump _ (pc t + 1) hpcl (by omega) hcond t ht' rfl
          simp only [NCmd.exec, XCmd.exec, Option.some.injEq, Config.mk.injEq]
          refine ⟨hn.symm, ?_⟩
          funext j
          have h1 := hd j
          have hx : ndelta P (pc t) j = 0 := by simp [ndelta, hc]
          have hh : nisHalf P (pc t) j = false := by simp [nisHalf, hc]
          rw [hx, hh] at h1
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
          rw [if_neg (by norm_num : ¬((0 : ℤ) = -1)), if_neg (by norm_num : ¬((0 : ℤ) = 1)),
            Nat.add_zero, Nat.add_zero] at h1
          by_cases hja : j = a
          · subst hja
            have ha : nisAdd P (pc t) j = true := by simp [nisAdd, hc]
            rw [if_pos ha, hmv_eq (pc t) j b hc t, hlione, mul_one] at h1
            rw [Function.update_self]
            omega
          · have ha : nisAdd P (pc t) j = false := by simp [nisAdd, hc, Ne.symm hja]
            rw [ha] at h1
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
            rw [Function.update_of_ne hja]
            omega
        | half a =>
          have hcond : 2 ^ q * L (pc t) ≼ L (pc t + 1) := H.lines _ _ hc
          have hn := hjump _ (pc t + 1) hpcl (by omega) hcond t ht' rfl
          simp only [NCmd.exec, XCmd.exec, Option.some.injEq, Config.mk.injEq]
          refine ⟨hn.symm, ?_⟩
          funext j
          have h1 := hd j
          have hx : ndelta P (pc t) j = 0 := by simp [ndelta, hc]
          have ha : nisAdd P (pc t) j = false := by simp [nisAdd, hc]
          rw [hx, ha] at h1
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
          rw [if_neg (by norm_num : ¬((0 : ℤ) = -1)), if_neg (by norm_num : ¬((0 : ℤ) = 1)),
            Nat.add_zero] at h1
          by_cases hja : j = a
          · subst hja
            have hh : nisHalf P (pc t) j = true := by simp [nisHalf, hc]
            rw [if_pos hh, hjv_eq (pc t) j hc t, hlione, mul_one] at h1
            rw [Function.update_self]
            omega
          · have hh : nisHalf P (pc t) j = false := by simp [nisHalf, hc, Ne.symm hja]
            rw [hh] at h1
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
            rw [Function.update_of_ne hja]
            omega
      | branch a b =>
        have hab := hP.branch_ok _ a b hc
        have hbr : pc (t + 1) = a ∨ pc (t + 1) = b := by
          have hcond := H.lines _ _ hc
          simp only [nlineCond] at hcond
          split_ifs at hcond with hab'
          · subst hab'
            exact Or.inl (hjump _ a hpcl hab.1 hcond t ht' rfl)
          · exact hbranch _ a b hpcl hab.1 hab.2 hab' hcond t ht' rfl
        simp only [NCmd.exec, Option.some.injEq, Config.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [hch_branch t a b hc]
          by_cases ha : pc (t + 1) = a
          · simp [ha]
          · rcases hbr with h | h
            · exact absurd h ha
            · simp [ha, h]
              omega
        · funext j
          have h1 := hd j
          have hx : ndelta P (pc t) j = 0 := by simp [ndelta, hc]
          have ha2 : nisAdd P (pc t) j = false := by simp [nisAdd, hc]
          have hb2 : nisHalf P (pc t) j = false := by simp [nisHalf, hc]
          rw [hx, ha2, hb2] at h1
          simp at h1
          omega
  refine ⟨ch, s, ?_⟩
  rw [hrun s le_rfl]
  simp only [nfinal, Option.some.injEq, Config.mk.injEq]
  exact ⟨hpcs, funext hrj_s⟩


/-- **The system of §5 is equivalent to acceptance**: a nondeterministic machine with the fast
commands and `BRANCH` accepts `x` exactly when the system (46)–(50), (52) has a solution. -/
theorem naccepts_iff {r : ℕ} (P : NProgram r) (hP : NWF P) (x : ℕ) :
    NAccepts P x ↔
      ∃ (s Q I : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ), NSys P x s Q I R L M J := by
  refine ⟨nsys_of_accepts hP, ?_⟩
  rintro ⟨s, Q, I, R, L, M, J, H⟩
  exact naccepts_of_nsys hP H

end RM
end JM1984
