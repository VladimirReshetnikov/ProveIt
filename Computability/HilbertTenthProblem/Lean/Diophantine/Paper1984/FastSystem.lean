import Diophantine.Paper1984.FastMachine
import Diophantine.Paper1984.FastMasks
import Diophantine.Paper1984.Encoding

/-!
# Jones–Matijasevič 1984, §4: the system for machines with the fast commands

The system (24)–(39) of §3 is extended to programs with the commands (41) `Ri ← Ri + Rj` and
(42) `Rj ← ⌈Rj/2⌉`: (24) is replaced by (46) `2^s(x+1) < Q/2`, every fast line gets the
fall-through condition `Q L_n ≼ L_{n+1}`, each addition line `n` carries an unknown `M_n`
subject to (47) and contributes `Q M_n` to the register equation of its target, and each
halving line `p` carries an unknown `J_p` subject to (49) (with the corrected term `L_p`) and
contributes `−Q J_p` to the register equation of its register.
-/

namespace JM1984
namespace RM

open Finset

variable {r : ℕ}

/-- The change of register `j` prescribed by a base arithmetic line. -/
def xdelta (P : XProgram r) (i : ℕ) (j : Fin r) : ℤ :=
  match P[i]? with
  | some (.base (.arith δ)) => δ j
  | _ => 0

/-- Line `i` adds into register `j`. -/
def isAdd (P : XProgram r) (i : ℕ) (j : Fin r) : Bool :=
  match P[i]? with
  | some (.add a _) => decide (a = j)
  | _ => false

/-- Line `i` halves register `j`. -/
def isHalf (P : XProgram r) (i : ℕ) (j : Fin r) : Bool :=
  match P[i]? with
  | some (.half a) => decide (a = j)
  | _ => false

/-- The condition attached to an extended line. -/
def xlineCond (Q I : ℕ) (R : Fin r → ℕ) (L : ℕ → ℕ) (i : ℕ) : XCmd r → Prop
  | .base c => lineCond Q I R L i c
  | .add _ _ => Q * L i ≼ L (i + 1)
  | .half _ => Q * L i ≼ L (i + 1)

/-- The register equation with the contributions of the fast commands. -/
def xregEq (P : XProgram r) (x Q : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ) (j : Fin r) : Prop :=
  R j + ∑ i ∈ range P.length, (if xdelta P i j = -1 then Q * L i else 0)
      + ∑ i ∈ range P.length, (if isHalf P i j = true then Q * J i else 0)
    = Q * R j + ∑ i ∈ range P.length, (if xdelta P i j = 1 then Q * L i else 0)
      + ∑ i ∈ range P.length, (if isAdd P i j = true then Q * M i else 0)
      + (if j.val = 0 then x else 0)

/-- Well-formed extended programs. -/
structure XWF (P : XProgram r) : Prop where
  pos : 0 < P.length
  last_stop : P[P.length - 1]? = some (.base .stop)
  stop_last : ∀ i : ℕ, P[i]? = some (.base .stop : XCmd r) → i = P.length - 1
  goto_lt : ∀ i k : ℕ, P[i]? = some (.base (.goto k) : XCmd r) → k < P.length
  ifLt_ok : ∀ (i : ℕ) (a b : Operand r) (k : ℕ),
    P[i]? = some (.base (.ifLt a b k)) → k < P.length ∧ k ≠ i ∧ k ≠ i + 1
  ifLe_ok : ∀ (i : ℕ) (a b : Operand r) (k : ℕ),
    P[i]? = some (.base (.ifLe a b k)) → k < P.length ∧ k ≠ i ∧ k ≠ i + 1
  arith_ok : ∀ (i : ℕ) (δ : Fin r → ℤ), P[i]? = some (.base (.arith δ)) → ∀ j, -1 ≤ δ j ∧ δ j ≤ 1

/-- The system for extended programs. -/
structure XSys (P : XProgram r) (x s Q I : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ) : Prop where
  c46 : 2 * (2 ^ s * (x + 1)) < Q
  c25 : P.length < Q
  c26 : ∃ q, Q = 2 ^ q
  c27 : 1 + (Q - 1) * I = Q ^ (s + 1)
  c29 : ∀ j, R j ≼ (Q / 2 - 1) * I
  c30 : I = ∑ i ∈ range P.length, L i
  c31 : ∀ i < P.length, L i ≼ I
  c32 : 1 ≼ L 0
  c33 : L (P.length - 1) = Q ^ s
  lines : ∀ (i : ℕ) (c : XCmd r), P[i]? = some c → xlineCond Q I R L i c
  addMask : ∀ (i : ℕ) (j k : Fin r), P[i]? = some (.add j k) →
    M i ≼ R k ∧ M i ≼ (Q - 1) * L i ∧ R k ≼ (Q - 1) * (I - L i) + M i
  halfMask : ∀ (i : ℕ) (j : Fin r), P[i]? = some (.half j) →
    2 * J i ≼ R j ∧ J i ≼ (Q / 2 - 1) * L i ∧ R j ≼ (Q - 1) * (I - L i) + 2 * J i + L i
  regs : ∀ j, xregEq P x Q R L M J j

/-- The accepting configuration of an extended program. -/
def xfinal (P : XProgram r) : Config r := ⟨P.length - 1, fun _ => 0⟩

/-- `P` accepts `x`: from line `0` with `x` in `R1`, the machine reaches the last line with all
registers zero. -/
def XAccepts (P : XProgram r) (x : ℕ) : Prop :=
  ∃ s, xrun P (init r x) s = some (xfinal P)

/-! ### The trace of an extended run -/

/-- Register `j` at time `t`. -/
def xregAt (P : XProgram r) (x : ℕ) (j : Fin r) (t : ℕ) : ℕ :=
  match xrun P (init r x) t with
  | some c => c.regs j
  | none => 0

/-- `1` if line `i` is executed at time `t`. -/
def xlinAt (P : XProgram r) (x : ℕ) (i t : ℕ) : ℕ :=
  match xrun P (init r x) t with
  | some c => if c.pc = i then 1 else 0
  | none => 0

/-- The value of an operand at time `t`. -/
def xopdAt (P : XProgram r) (x : ℕ) (a : Operand r) (t : ℕ) : ℕ :=
  match xrun P (init r x) t with
  | some c => a.val c.regs
  | none => 0

/-- The digits of the unknown `M_i` of (48). -/
def mFun (P : XProgram r) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.add _ k) => xregAt P x k t * xlinAt P x i t
  | _ => 0

/-- The digits of the unknown `J_i` of (50). -/
def jFun (P : XProgram r) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.half j) => xregAt P x j t / 2 * xlinAt P x i t
  | _ => 0

variable {P : XProgram r} {x t : ℕ}

theorem xregAt_of_eq {c : Config r} (h : xrun P (init r x) t = some c) (j : Fin r) :
    xregAt P x j t = c.regs j := by simp [xregAt, h]

theorem xlinAt_of_eq {c : Config r} (h : xrun P (init r x) t = some c) (i : ℕ) :
    xlinAt P x i t = if c.pc = i then 1 else 0 := by simp [xlinAt, h]

theorem xopdAt_of_eq {c : Config r} (h : xrun P (init r x) t = some c) (a : Operand r) :
    xopdAt P x a t = a.val c.regs := by simp [xopdAt, h]

theorem xregAt_of_none (h : xrun P (init r x) t = none) (j : Fin r) : xregAt P x j t = 0 := by
  simp [xregAt, h]

theorem xlinAt_of_none (h : xrun P (init r x) t = none) (i : ℕ) : xlinAt P x i t = 0 := by
  simp [xlinAt, h]

theorem xopdAt_of_none (h : xrun P (init r x) t = none) (a : Operand r) : xopdAt P x a t = 0 := by
  simp [xopdAt, h]

theorem xlinAt_le_one (P : XProgram r) (x i t : ℕ) : xlinAt P x i t ≤ 1 := by
  unfold xlinAt
  split
  · split_ifs <;> omega
  · omega

theorem xrun_succ (P : XProgram r) (c : Config r) (n : ℕ) :
    xrun P c (n + 1) = (xrun P c n).bind (xstep P) := rfl

theorem xrun_succ_of_eq {c d : Config r} {n : ℕ} (h : xrun P c n = some d) :
    xrun P c (n + 1) = xstep P d := by rw [xrun_succ, h]; rfl

theorem xrun_isSome_of_le {c d : Config r} {s : ℕ} (h : xrun P c s = some d) :
    ∀ t ≤ s, ∃ e, xrun P c t = some e := by
  intro t ht
  induction s generalizing d with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact ⟨c, rfl⟩
  | succ s ih =>
    rcases Nat.eq_or_lt_of_le ht with rfl | hlt
    · exact ⟨d, h⟩
    · rw [xrun_succ] at h
      cases hs : xrun P c s with
      | none => rw [hs] at h; simp at h
      | some e => exact ih hs (by omega)

theorem xpc_lt_of_step {d e : Config r} (h : xstep P d = some e) :
    d.pc < P.length ∧ P[d.pc]? ≠ some (.base .stop) := by
  unfold xstep at h
  cases hp : P[d.pc]? with
  | none => rw [hp] at h; simp at h
  | some cmd =>
    rw [hp] at h
    refine ⟨List.getElem?_eq_some_iff.1 hp |>.1, ?_⟩
    intro hc
    have hcmd : cmd = XCmd.base Cmd.stop := Option.some.inj hc
    subst hcmd
    simp [XCmd.exec, Cmd.exec] at h

theorem xstep_final (hP : XWF P) : xstep P (xfinal P) = none := by
  unfold xstep
  simp [xfinal, hP.last_stop, XCmd.exec, Cmd.exec]

theorem xrun_none_of_gt (hP : XWF P) {s : ℕ} (hs : xrun P (init r x) s = some (xfinal P)) :
    ∀ t, s < t → xrun P (init r x) t = none := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge s t with h | h
    · rw [xrun_succ, ih h]; rfl
    · have : t = s := by omega
      subst this
      rw [xrun_succ_of_eq hs, xstep_final hP]

/-- Registers at most double at each step. -/
theorem xregs_run_le (hP : XWF P) : ∀ {t : ℕ} {c : Config r}, xrun P (init r x) t = some c →
    ∀ j, c.regs j + 1 ≤ 2 ^ t * (x + 1) := by
  intro t
  induction t with
  | zero =>
    intro c h j
    cases h
    simp only [init, pow_zero, one_mul]
    split_ifs <;> omega
  | succ t ih =>
    intro c h j
    rw [xrun_succ] at h
    cases hd : xrun P (init r x) t with
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
      unfold xstep at h
      cases hp : P[d.pc]? with
      | none => rw [hp] at h; simp at h
      | some cmd =>
        rw [hp] at h
        cases cmd with
        | base cb =>
          cases cb with
          | goto k =>
            simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at h
            rw [← h]; exact hmono _ (hle j)
          | ifLt a b k =>
            simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at h
            rw [← h]; exact hmono _ (hle j)
          | ifLe a b k =>
            simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at h
            rw [← h]; exact hmono _ (hle j)
          | arith δ =>
            simp only [XCmd.exec, Cmd.exec] at h
            split_ifs at h with hδ
            simp only [Option.some.injEq] at h
            rw [← h]
            simp only
            have hb := hP.arith_ok _ _ hp j
            have hj := hle j
            have hδj := hδ j
            have : ((d.regs j : ℤ) + δ j).toNat ≤ d.regs j + 1 := by omega
            exact le_trans (by omega) (hsucc _ hj)
          | stop => simp [XCmd.exec, Cmd.exec] at h
        | add a b =>
          simp only [XCmd.exec, Option.some.injEq] at h
          rw [← h]
          simp only
          by_cases hj : j = a
          · subst hj
            rw [Function.update_self]
            exact hadd _ _ (hle j) (hle b)
          · rw [Function.update_of_ne hj]
            exact hmono _ (hle j)
        | half a =>
          simp only [XCmd.exec, Option.some.injEq] at h
          rw [← h]
          simp only
          by_cases hj : j = a
          · subst hj
            rw [Function.update_self]
            have hj := hle j
            exact le_trans (by omega) (hmono _ hj)
          · rw [Function.update_of_ne hj]
            exact hmono _ (hle j)

/-- The register read by an addition line. -/
def mHead (P : XProgram r) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.add _ k) => xregAt P x k t
  | _ => 0

/-- Half the register of a halving line. -/
def jHead (P : XProgram r) (x : ℕ) (i t : ℕ) : ℕ :=
  match P[i]? with
  | some (.half j) => xregAt P x j t / 2
  | _ => 0

theorem mFun_eq (P : XProgram r) (x i t : ℕ) :
    mFun P x i t = mHead P x i t * xlinAt P x i t := by
  unfold mFun mHead
  cases P[i]? with
  | none => simp
  | some c => cases c <;> simp

theorem jFun_eq (P : XProgram r) (x i t : ℕ) :
    jFun P x i t = jHead P x i t * xlinAt P x i t := by
  unfold jFun jHead
  cases P[i]? with
  | none => simp
  | some c => cases c <;> simp


set_option maxHeartbeats 4000000 in
/-- An accepting computation of an extended program solves the system. -/
theorem xsys_of_accepts (hP : XWF P) (h : XAccepts P x) :
    ∃ (s Q I : ℕ) (R : Fin r → ℕ) (L M J : ℕ → ℕ), XSys P x s Q I R L M J := by
  obtain ⟨s, hs⟩ := h
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
  have hsome : ∀ t ≤ s, ∃ c, xrun P (init r x) t = some c := xrun_isSome_of_le hs
  have hnone : ∀ t, s < t → xrun P (init r x) t = none := xrun_none_of_gt hP hs
  have hstep : ∀ t < s, ∀ c, xrun P (init r x) t = some c →
      ∃ c', xrun P (init r x) (t + 1) = some c' ∧ xstep P c = some c' := by
    intro t ht c hc
    obtain ⟨c', hc'⟩ := hsome (t + 1) (by omega)
    exact ⟨c', hc', by rw [← hc', xrun_succ_of_eq hc]⟩
  have hpc_lt : ∀ t < s, ∀ c, xrun P (init r x) t = some c →
      c.pc < P.length ∧ P[c.pc]? ≠ some (.base .stop) := by
    intro t ht c hc
    obtain ⟨c', -, hstep'⟩ := hstep t ht c hc
    exact xpc_lt_of_step hstep'
  have hpc_ne : ∀ t < s, ∀ c, xrun P (init r x) t = some c → c.pc ≠ P.length - 1 := by
    intro t ht c hc heq
    have := (hpc_lt t ht c hc).2
    rw [heq] at this
    exact this hP.last_stop
  have hts_of : ∀ t c, xrun P (init r x) t = some c → t ≤ s := by
    intro t c hc
    by_contra hcon
    rw [hnone t (by omega)] at hc
    cases hc
  have hreg_le : ∀ t c, xrun P (init r x) t = some c → ∀ j, c.regs j + 1 ≤ 2 ^ t * (x + 1) :=
    fun t c hc j => xregs_run_le hP hc j
  have hreg_bound : ∀ j t, 2 * xregAt P x j t < 2 ^ q := by
    intro j t
    cases hc : xrun P (init r x) t with
    | none => rw [xregAt_of_none hc]; omega
    | some c =>
      rw [xregAt_of_eq hc]
      have hts := hts_of t c hc
      have hb := hreg_le t c hc j
      have hmono : 2 ^ t * (x + 1) ≤ 2 ^ s * (x + 1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hts)
      omega
  have hpc_le : ∀ t ≤ s, ∀ c, xrun P (init r x) t = some c → c.pc < P.length := by
    intro t ht c hc
    rcases Nat.lt_or_ge t s with h | h
    · exact (hpc_lt t h c hc).1
    · have : t = s := by omega
      subst this
      rw [hs] at hc
      cases hc
      simp [xfinal]; omega
  have huniq : ∀ t ≤ s, ∑ i ∈ range P.length, xlinAt P x i t = 1 := by
    intro t ht
    obtain ⟨c, hc⟩ := hsome t ht
    simp only [xlinAt_of_eq hc]
    rw [sum_ite_eq]
    simp [mem_range, hpc_le t ht c hc]
  have hlin_zero : ∀ i t, s < t → xlinAt P x i t = 0 := fun i t ht => xlinAt_of_none (hnone t ht) i
  have hreg_zero : ∀ j t, s < t → xregAt P x j t = 0 := fun j t ht => xregAt_of_none (hnone t ht) j
  have hexec : ∀ i t, P[i]? ≠ some (.base .stop) → xlinAt P x i t = 1 →
      ∃ c c', xrun P (init r x) t = some c ∧ c.pc = i ∧ t < s ∧
        xrun P (init r x) (t + 1) = some c' ∧ xstep P c = some c' := by
    intro i t hi hl
    have hts : t ≤ s := by
      by_contra hc
      rw [hlin_zero i t (by omega)] at hl
      omega
    obtain ⟨c, hc⟩ := hsome t hts
    rw [xlinAt_of_eq hc] at hl
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
    fun j => blocks (2 ^ q) (s + 1) (xregAt P x j),
    fun i => blocks (2 ^ q) (s + 1) (xlinAt P x i),
    fun i => blocks (2 ^ q) (s + 1) (mFun P x i),
    fun i => blocks (2 ^ q) (s + 1) (jFun P x i), ?_⟩
  have hextL : ∀ i, blocks (2 ^ q) (s + 1) (xlinAt P x i) = blocks (2 ^ q) (s + 2) (xlinAt P x i) :=
    fun i => (blocks_of_zero_of_ge (by omega) (fun t ht => hlin_zero i t (by omega))).symm
  have hextR : ∀ j, blocks (2 ^ q) (s + 1) (xregAt P x j)
      = blocks (2 ^ q) (s + 2) (xregAt P x j) :=
    fun j => (blocks_of_zero_of_ge (by omega) (fun t ht => hreg_zero j t (by omega))).symm
  have hlin_lt : ∀ i t, xlinAt P x i t < 2 ^ q := fun i t => by
    have := xlinAt_le_one P x i t; omega
  have hjump : ∀ i n, P[i]? ≠ some (.base .stop) →
      (∀ t c c', xrun P (init r x) t = some c → c.pc = i → xstep P c = some c' → c'.pc = n) →
      2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼ blocks (2 ^ q) (s + 1) (xlinAt P x n) := by
    intro i n hi hn
    rw [blocks_shift, hextL n,
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hlin_lt _ _))
        (fun t _ => hlin_lt _ _), forall_lt_succ']
    simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    refine ⟨zero_mask _, fun t _ => ?_⟩
    rw [mask_of_le_one_iff (xlinAt_le_one _ _ _ _)]
    intro hl
    obtain ⟨c, c', hc, hpc, -, hc', hst⟩ := hexec i t hi hl
    rw [xlinAt_of_eq hc', if_pos (hn t c c' hc hpc hst)]
  have henc : ∀ a : Operand r, Operand.enc (blocks (2 ^ q) (s + 1) fun _ => 1)
      (fun j => blocks (2 ^ q) (s + 1) (xregAt P x j)) a = blocks (2 ^ q) (s + 1) (xopdAt P x a) := by
    intro a
    cases a with
    | reg j =>
      simp only [Operand.enc]
      apply blocks_congr
      intro t _
      cases hc : xrun P (init r x) t with
      | none => rw [xregAt_of_none hc, xopdAt_of_none hc]
      | some c => rw [xregAt_of_eq hc, xopdAt_of_eq hc]; rfl
    | zero =>
      simp only [Operand.enc]
      rw [← blocks_const_zero (2 ^ q) (s + 1)]
      apply blocks_congr
      intro t _
      cases hc : xrun P (init r x) t with
      | none => rw [xopdAt_of_none hc]
      | some c => rw [xopdAt_of_eq hc]; rfl
    | one =>
      simp only [Operand.enc]
      apply blocks_congr
      intro t ht
      obtain ⟨c, hc⟩ := hsome t (by omega)
      rw [xopdAt_of_eq hc]; rfl
  have hopd_lt : ∀ a t, 2 * xopdAt P x a t < 2 ^ q := by
    intro a t
    cases hc : xrun P (init r x) t with
    | none => rw [xopdAt_of_none hc]; omega
    | some c =>
      rw [xopdAt_of_eq hc]
      cases a with
      | reg j => simpa only [Operand.val, ← xregAt_of_eq hc] using hreg_bound j t
      | zero => simp only [Operand.val]; omega
      | one => simp only [Operand.val]; omega
  have hopd_le' : ∀ a t, 1 ≤ t → t < s → 2 * xopdAt P x a t + 3 ≤ 2 ^ q := by
    intro a t h1 h2
    obtain ⟨c, hc⟩ := hsome t (by omega)
    rw [xopdAt_of_eq hc]
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
  have hcond1 : ∀ i k, P[i]? ≠ some (.base .stop) → k ≠ i + 1 →
      (∀ t c c', xrun P (init r x) t = some c → c.pc = i → xstep P c = some c' →
        c'.pc = k ∨ c'.pc = i + 1) →
      2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼
        blocks (2 ^ q) (s + 1) (xlinAt P x k) + blocks (2 ^ q) (s + 1) (xlinAt P x (i + 1)) := by
    intro i k hi hk hn
    rw [blocks_shift, hextL k, hextL (i + 1), ← blocks_add,
      mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | exact hlin_lt _ _))
        (fun t _ => by
          have := xlinAt_le_one P x k t; have := xlinAt_le_one P x (i + 1) t; omega),
      forall_lt_succ']
    simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    refine ⟨zero_mask _, fun t _ => ?_⟩
    rw [mask_of_le_one_iff (xlinAt_le_one _ _ _ _)]
    intro hl
    obtain ⟨c, c', hc, hpc, -, hc', hst⟩ := hexec i t hi hl
    rw [xlinAt_of_eq hc', xlinAt_of_eq hc']
    rcases hn t c c' hc hpc hst with h | h
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h]
  have h29 : ∀ j, blocks (2 ^ q) (s + 1) (xregAt P x j) ≼
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
      = ∑ i ∈ range P.length, blocks (2 ^ q) (s + 1) (xlinAt P x i) := by
    rw [← blocks_sum]
    apply blocks_congr
    intro t ht
    exact (huniq t (by omega)).symm
  have h31 : ∀ i < P.length, blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼
      blocks (2 ^ q) (s + 1) (fun _ => 1) := by
    intro i _
    refine (mask_blocks_iff (fun t _ => hlin_lt i t) (fun t _ => by omega)).2 ?_
    intro t _
    rw [mask_of_le_one_iff (xlinAt_le_one _ _ _ _)]
    intro _
    rfl
  have h32 : 1 ≼ blocks (2 ^ q) (s + 1) (xlinAt P x 0) := by
    have key : blocks (2 ^ q) (s + 1) (fun t => if t = 0 then 1 else 0) ≼
        blocks (2 ^ q) (s + 1) (xlinAt P x 0) := by
      refine (mask_blocks_iff (fun t _ => by split_ifs <;> omega) (fun t _ => hlin_lt _ _)).2 ?_
      intro t _
      split_ifs with h0
      · subst h0
        rw [xlinAt_of_eq (rfl : xrun P (init r x) 0 = some (init r x))]
        simp only [init, if_pos rfl]
        exact Mask.refl 1
      · exact zero_mask _
    rwa [blocks_single (by omega), pow_zero] at key
  have h33 : blocks (2 ^ q) (s + 1) (xlinAt P x (P.length - 1)) = (2 ^ q) ^ s := by
    rw [← blocks_single (Q := 2 ^ q) (n := s + 1) (k := s) (by omega)]
    apply blocks_congr
    intro t ht
    rcases Nat.lt_or_ge t s with h | h
    · obtain ⟨c, hc⟩ := hsome t (by omega)
      rw [xlinAt_of_eq hc, if_neg (hpc_ne t h c hc), if_neg (by omega)]
    · have : t = s := by omega
      subst this
      rw [xlinAt_of_eq hs]
      simp [xfinal]
  -- the line conditions
  have hlines : ∀ (i : ℕ) (c : XCmd r), P[i]? = some c →
      xlineCond (2 ^ q) (blocks (2 ^ q) (s + 1) fun _ => 1)
        (fun j => blocks (2 ^ q) (s + 1) (xregAt P x j))
        (fun i => blocks (2 ^ q) (s + 1) (xlinAt P x i)) i c := by
    intro i c hc
    cases c with
    | add a b =>
      have hi : P[i]? ≠ some (.base .stop) := by rw [hc]; simp
      show 2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼
        blocks (2 ^ q) (s + 1) (xlinAt P x (i + 1))
      apply hjump i (i + 1) hi
      intro t c c' _ hpc hst
      unfold xstep at hst
      rw [hpc, hc] at hst
      simp only [XCmd.exec, Option.some.injEq] at hst
      rw [← hst]
    | half a =>
      have hi : P[i]? ≠ some (.base .stop) := by rw [hc]; simp
      show 2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼
        blocks (2 ^ q) (s + 1) (xlinAt P x (i + 1))
      apply hjump i (i + 1) hi
      intro t c c' _ hpc hst
      unfold xstep at hst
      rw [hpc, hc] at hst
      simp only [XCmd.exec, Option.some.injEq] at hst
      rw [← hst]
    | base cb =>
      cases cb with
      | goto k =>
        have hi : P[i]? ≠ some (.base .stop) := by rw [hc]; simp
        show 2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼ blocks (2 ^ q) (s + 1) (xlinAt P x k)
        apply hjump i k hi
        intro t c c' _ hpc hst
        unfold xstep at hst
        rw [hpc, hc] at hst
        simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
        rw [← hst]
      | arith δ =>
        have hi : P[i]? ≠ some (.base .stop) := by rw [hc]; simp
        show 2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼
          blocks (2 ^ q) (s + 1) (xlinAt P x (i + 1))
        apply hjump i (i + 1) hi
        intro t c c' _ hpc hst
        unfold xstep at hst
        rw [hpc, hc] at hst
        simp only [XCmd.exec, Cmd.exec] at hst
        split_ifs at hst
        simp only [Option.some.injEq] at hst
        rw [← hst]
      | stop => trivial
      | ifLt a b k =>
        have hi : P[i]? ≠ some (.base .stop) := by rw [hc]; simp
        obtain ⟨hk, hki, hki1⟩ := hP.ifLt_ok i a b k hc
        refine ⟨hcond1 i k hi hki1 ?_, ?_⟩
        · intro t c c' _ hpc hst
          unfold xstep at hst
          rw [hpc, hc] at hst
          simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
          rw [← hst]
          simp only
          split_ifs <;> simp
        · show 2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼
            blocks (2 ^ q) (s + 1) (xlinAt P x k) + 2 ^ q * blocks (2 ^ q) (s + 1) (fun _ => 1)
              + 2 * Operand.enc _ _ a - 2 * Operand.enc _ _ b
          rw [henc a, henc b]
          refine (compare_cond rfl hq2 (xlinAt_le_one P x i) (xlinAt_le_one P x k) ?_ ?_
            (hopd_lt a) (hopd_lt b) ?_).2 ?_
          · intro t hl
            obtain ⟨c, c', hct, hpc, -, -, -⟩ := hexec i t hi hl
            rw [xlinAt_of_eq hct, if_neg (by omega)]
          · intro t hl
            obtain ⟨c, c', -, -, hts, -, -⟩ := hexec i t hi hl
            exact hts
          · intro t h1 h2
            have := xlinAt_le_one P x k t
            have := hopd_le' a t h1 h2
            omega
          · intro t hl
            obtain ⟨c, c', hct, hpc, -, hc', hst⟩ := hexec i t hi hl
            unfold xstep at hst
            rw [hpc, hc] at hst
            simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
            rw [xlinAt_of_eq hc', ← hst, xopdAt_of_eq hct, xopdAt_of_eq hct]
            simp only
            by_cases hab : a.val c.regs < b.val c.regs
            · simp [hab]
            · simp [hab, Ne.symm hki1]
      | ifLe a b k =>
        have hi : P[i]? ≠ some (.base .stop) := by rw [hc]; simp
        obtain ⟨hk, hki, hki1⟩ := hP.ifLe_ok i a b k hc
        refine ⟨hcond1 i k hi hki1 ?_, ?_⟩
        · intro t c c' _ hpc hst
          unfold xstep at hst
          rw [hpc, hc] at hst
          simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
          rw [← hst]
          simp only
          split_ifs <;> simp
        · show 2 ^ q * blocks (2 ^ q) (s + 1) (xlinAt P x i) ≼
            blocks (2 ^ q) (s + 1) (xlinAt P x (i + 1))
              + 2 ^ q * blocks (2 ^ q) (s + 1) (fun _ => 1)
              + 2 * Operand.enc _ _ b - 2 * Operand.enc _ _ a
          rw [henc a, henc b]
          refine (compare_cond rfl hq2 (xlinAt_le_one P x i) (xlinAt_le_one P x (i + 1)) ?_ ?_
            (hopd_lt b) (hopd_lt a) ?_).2 ?_
          · intro t hl
            obtain ⟨c, c', hct, hpc, -, -, -⟩ := hexec i t hi hl
            rw [xlinAt_of_eq hct, if_neg (by omega)]
          · intro t hl
            obtain ⟨c, c', -, -, hts, -, -⟩ := hexec i t hi hl
            exact hts
          · intro t h1 h2
            have := xlinAt_le_one P x (i + 1) t
            have := hopd_le' b t h1 h2
            omega
          · intro t hl
            obtain ⟨c, c', hct, hpc, -, hc', hst⟩ := hexec i t hi hl
            unfold xstep at hst
            rw [hpc, hc] at hst
            simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
            rw [xlinAt_of_eq hc', ← hst, xopdAt_of_eq hct, xopdAt_of_eq hct]
            simp only
            by_cases hab : a.val c.regs ≤ b.val c.regs
            · simp [hab, hki1]
            · have := Nat.lt_of_not_le hab
              simp [hab, this]
  -- (47) and (49)
  have haddMask : ∀ (i : ℕ) (j k : Fin r), P[i]? = some (.add j k) →
      blocks (2 ^ q) (s + 1) (mFun P x i) ≼ blocks (2 ^ q) (s + 1) (xregAt P x k) ∧
      blocks (2 ^ q) (s + 1) (mFun P x i) ≼
        (2 ^ q - 1) * blocks (2 ^ q) (s + 1) (xlinAt P x i) ∧
      blocks (2 ^ q) (s + 1) (xregAt P x k) ≼
        (2 ^ q - 1) * (blocks (2 ^ q) (s + 1) (fun _ => 1)
          - blocks (2 ^ q) (s + 1) (xlinAt P x i)) + blocks (2 ^ q) (s + 1) (mFun P x i) := by
    intro i j k hp
    refine (mask47_iff (q := q) (n := s + 1) (fun t _ => by have := hreg_bound k t; omega)
      (fun t _ => xlinAt_le_one P x i t) _).2 ?_
    apply blocks_congr
    intro t _
    simp only [mFun, hp]
  have hhalfMask : ∀ (i : ℕ) (j : Fin r), P[i]? = some (.half j) →
      2 * blocks (2 ^ q) (s + 1) (jFun P x i) ≼ blocks (2 ^ q) (s + 1) (xregAt P x j) ∧
      blocks (2 ^ q) (s + 1) (jFun P x i) ≼
        (2 ^ q / 2 - 1) * blocks (2 ^ q) (s + 1) (xlinAt P x i) ∧
      blocks (2 ^ q) (s + 1) (xregAt P x j) ≼
        (2 ^ q - 1) * (blocks (2 ^ q) (s + 1) (fun _ => 1)
          - blocks (2 ^ q) (s + 1) (xlinAt P x i)) + 2 * blocks (2 ^ q) (s + 1) (jFun P x i)
          + blocks (2 ^ q) (s + 1) (xlinAt P x i) := by
    intro i j hp
    refine (mask49_iff (q := q) (n := s + 1) (by omega)
      (fun t _ => by have := hreg_bound j t; omega)
      (fun t _ => xlinAt_le_one P x i t) _).2 ?_
    apply blocks_congr
    intro t _
    simp only [jFun, hp]
  -- the register equations
  have hlin_eq : ∀ t c, xrun P (init r x) t = some c →
      ∀ i, xlinAt P x i t = if i = c.pc then 1 else 0 := by
    intro t c hc i
    rw [xlinAt_of_eq hc]
    simp only [eq_comm]
  have hsum_one : ∀ (t : ℕ) (c : Config r), xrun P (init r x) t = some c → c.pc < P.length →
      ∀ (p : ℕ → Bool) (g : ℕ → ℕ → ℕ),
        ∑ i ∈ range P.length, (if p i = true then g i t * xlinAt P x i t else 0)
          = if p c.pc = true then g c.pc t else 0 := by
    intro t c hc hpc p g
    rw [sum_eq_single c.pc]
    · rw [hlin_eq t c hc c.pc, if_pos rfl, mul_one]
    · intro i _ hi
      rw [hlin_eq t c hc i, if_neg hi, mul_zero]
      simp
    · intro h; exact absurd (mem_range.2 hpc) h
  have hregs : ∀ j, xregEq P x (2 ^ q) (fun j => blocks (2 ^ q) (s + 1) (xregAt P x j))
      (fun i => blocks (2 ^ q) (s + 1) (xlinAt P x i))
      (fun i => blocks (2 ^ q) (s + 1) (mFun P x i))
      (fun i => blocks (2 ^ q) (s + 1) (jFun P x i)) j := by
    intro j
    unfold xregEq
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
      rw [xregAt_of_eq (rfl : xrun P (init r x) 0 = some (init r x))]
      rfl
    | succ t =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
      have hts : t ≤ s := by omega
      obtain ⟨c, hc⟩ := hsome t hts
      have hpcl := hpc_le t hts c hc
      have hlin : ∀ i, xlinAt P x i t = if i = c.pc then 1 else 0 := hlin_eq t c hc
      have hM := hsum_one t c hc hpcl (fun i => isAdd P i j) (mHead P x)
      have hJ := hsum_one t c hc hpcl (fun i => isHalf P i j) (jHead P x)
      simp only [← mFun_eq] at hM
      simp only [← jFun_eq] at hJ
      rw [sum_ite_indicator hpcl _ _ hlin, sum_ite_indicator hpcl _ _ hlin, hM, hJ,
        xregAt_of_eq hc]
      rcases Nat.lt_or_ge t s with hlt | hge
      · obtain ⟨c', hc', hst⟩ := hstep t hlt c hc
        rw [xregAt_of_eq hc']
        unfold xstep at hst
        cases hp : P[c.pc]? with
        | none => rw [hp] at hst; simp at hst
        | some cmd =>
          rw [hp] at hst
          cases cmd with
          | base cb =>
            cases cb with
            | goto k =>
              simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
              simp [xdelta, isAdd, isHalf, hp, ← hst]
            | ifLt a b k =>
              simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
              simp [xdelta, isAdd, isHalf, hp, ← hst]
            | ifLe a b k =>
              simp only [XCmd.exec, Cmd.exec, Option.some.injEq] at hst
              simp [xdelta, isAdd, isHalf, hp, ← hst]
            | arith δ =>
              simp only [XCmd.exec, Cmd.exec] at hst
              split_ifs at hst with hδ
              simp only [Option.some.injEq] at hst
              have hδj := hδ j
              have hb := hP.arith_ok _ _ hp j
              simp only [xdelta, isAdd, isHalf, hp, ← hst, Bool.false_eq_true, ↓reduceIte,
                Nat.add_zero, Nat.zero_add]
              split_ifs <;> omega
            | stop => simp [XCmd.exec, Cmd.exec] at hst
          | add a b =>
            simp only [XCmd.exec, Option.some.injEq] at hst
            by_cases hja : j = a
            · subst hja
              simp [xdelta, isAdd, isHalf, mHead, jHead, hp, ← hst, Function.update_self,
                xregAt_of_eq hc]
            · simp [xdelta, isAdd, isHalf, mHead, jHead, hp, ← hst,
                Function.update_of_ne hja, Ne.symm hja]
          | half a =>
            simp only [XCmd.exec, Option.some.injEq] at hst
            by_cases hja : j = a
            · subst hja
              simp only [xdelta, isAdd, isHalf, mHead, jHead, hp, ← hst, Function.update_self,
                decide_true, if_true, Bool.false_eq_true, ↓reduceIte, xregAt_of_eq hc,
                Nat.add_zero, Nat.zero_add]
              norm_num
              omega
            · simp [xdelta, isAdd, isHalf, mHead, jHead, hp, ← hst,
                Function.update_of_ne hja, Ne.symm hja]
      · have hts' : t = s := by omega
        rw [hts', hs] at hc
        cases hc
        rw [hts', hreg_zero j (s + 1) (by omega)]
        simp [xdelta, isAdd, isHalf, mHead, jHead, xfinal, hP.last_stop]
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

end RM
end JM1984
