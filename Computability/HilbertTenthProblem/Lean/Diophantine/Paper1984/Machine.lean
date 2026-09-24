import Mathlib.Tactic

/-!
# Jones–Matijasevič 1984, §3: register machines

A register machine has registers `R1, …, Rr` (here indexed by `Fin r`, so `R1` is
register `0`) and a program written on lines `L0, …, Ll`.  The commands are
(15) `GO TO Lk`, (16) `IF Rj < Rm GO TO Lk`, (19) `IF Rj ≤ Rm GO TO Lk`,
(17) `Rj ← Rj + 1`, (18) `Rj ← Rj − 1`, and `STOP`.

Following the paper we allow the constants `0` and `1` in place of register
names in the comparisons, and we allow several `±1` updates of *different*
registers on one line (the "parallel" lines of Example 1); such a line is
`arith δ` with `δ j ∈ {-1, 0, 1}`.

Semantics: a configuration is a program counter and a register file; one step
is a partial function (`STOP`, an out-of-range line, or an attempted
subtraction from a zero register have no successor — the paper assumes the
latter "never occurs", and the encoding indeed has no solution for such runs).

`Accepts P x`: started at `L0` with `x` in `R1` and zeros elsewhere, the
machine eventually reaches the `STOP` line with all registers zero.
-/

namespace JM1984
namespace RM

/-- An operand of a comparison: a register, or one of the constants `0`, `1`. -/
inductive Operand (r : ℕ)
  | reg (j : Fin r)
  | zero
  | one

/-- The value of an operand under the register file `regs`. -/
def Operand.val {r : ℕ} (regs : Fin r → ℕ) : Operand r → ℕ
  | .reg j => regs j
  | .zero => 0
  | .one => 1

/-- Commands (15)–(19) and STOP; `arith δ` is a parallel `±1` update. -/
inductive Cmd (r : ℕ)
  | goto (k : ℕ)
  | ifLt (a b : Operand r) (k : ℕ)
  | ifLe (a b : Operand r) (k : ℕ)
  | arith (δ : Fin r → ℤ)
  | stop

/-- A program: the commands on lines `L0, L1, …`. -/
abbrev Program (r : ℕ) := List (Cmd r)

/-- A configuration: program counter and register contents. -/
structure Config (r : ℕ) where
  pc : ℕ
  regs : Fin r → ℕ

variable {r : ℕ}

/-- Executing the command on line `pc` with register file `regs`. -/
def Cmd.exec (pc : ℕ) (regs : Fin r → ℕ) : Cmd r → Option (Config r)
  | .goto k => some ⟨k, regs⟩
  | .ifLt a b k => some ⟨if a.val regs < b.val regs then k else pc + 1, regs⟩
  | .ifLe a b k => some ⟨if a.val regs ≤ b.val regs then k else pc + 1, regs⟩
  | .arith δ =>
      if ∀ j, 0 ≤ (regs j : ℤ) + δ j then
        some ⟨pc + 1, fun j => ((regs j : ℤ) + δ j).toNat⟩
      else none
  | .stop => none

/-- One step of the machine. -/
def step (P : Program r) (c : Config r) : Option (Config r) :=
  match P[c.pc]? with
  | some cmd => cmd.exec c.pc c.regs
  | none => none

/-- The configuration after `n` steps (`none` once the machine cannot proceed). -/
def run (P : Program r) (c : Config r) : ℕ → Option (Config r)
  | 0 => some c
  | n + 1 => (run P c n).bind (step P)

/-- The initial configuration: line `L0`, `x` in `R1`, zeros elsewhere. -/
def init (r x : ℕ) : Config r := ⟨0, fun j => if j.val = 0 then x else 0⟩

/-- The accepting configuration: the STOP line with all registers zero. -/
def final (P : Program r) : Config r := ⟨P.length - 1, fun _ => 0⟩

/-- `P` accepts `x`. -/
def Accepts (P : Program r) (x : ℕ) : Prop := ∃ s, run P (init r x) s = some (final P)

/-- Well-formed programs: STOP occurs exactly once, on the last line; jump targets are
lines of the program; conditional jumps are normalised (`k ∉ {i, i+1}`, see the
discussion after (33)); parallel updates change each register by at most one. -/
structure WF (P : Program r) : Prop where
  pos : 0 < P.length
  last_stop : P[P.length - 1]? = some Cmd.stop
  stop_last : ∀ i : ℕ, P[i]? = some Cmd.stop → i = P.length - 1
  goto_lt : ∀ i k : ℕ, P[i]? = some (Cmd.goto k : Cmd r) → k < P.length
  ifLt_ok : ∀ (i : ℕ) (a b : Operand r) (k : ℕ),
    P[i]? = some (Cmd.ifLt a b k) → k < P.length ∧ k ≠ i ∧ k ≠ i + 1
  ifLe_ok : ∀ (i : ℕ) (a b : Operand r) (k : ℕ),
    P[i]? = some (Cmd.ifLe a b k) → k < P.length ∧ k ≠ i ∧ k ≠ i + 1
  arith_ok : ∀ (i : ℕ) (δ : Fin r → ℤ), P[i]? = some (Cmd.arith δ) → ∀ j, -1 ≤ δ j ∧ δ j ≤ 1

/-! ### Elementary facts about runs -/

@[simp] theorem run_zero (P : Program r) (c : Config r) : run P c 0 = some c := rfl

theorem run_succ (P : Program r) (c : Config r) (n : ℕ) :
    run P c (n + 1) = (run P c n).bind (step P) := rfl

theorem run_succ_of_eq {P : Program r} {c d : Config r} {n : ℕ} (h : run P c n = some d) :
    run P c (n + 1) = step P d := by
  rw [run_succ, h]; rfl

/-- A run that is defined at time `s` is defined at all earlier times. -/
theorem run_isSome_of_le {P : Program r} {c d : Config r} {s : ℕ} (h : run P c s = some d) :
    ∀ t ≤ s, ∃ e, run P c t = some e := by
  intro t ht
  induction s generalizing d with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact ⟨c, rfl⟩
  | succ s ih =>
    rcases Nat.eq_or_lt_of_le ht with rfl | hlt
    · exact ⟨d, h⟩
    · rw [run_succ] at h
      cases hs : run P c s with
      | none => rw [hs] at h; simp at h
      | some e => exact ih hs (by omega)

/-- If a step from `d` happens, the line `d.pc` exists and is not STOP. -/
theorem pc_lt_of_step {P : Program r} {d e : Config r} (h : step P d = some e) :
    d.pc < P.length ∧ P[d.pc]? ≠ some .stop := by
  unfold step at h
  cases hp : P[d.pc]? with
  | none => rw [hp] at h; simp at h
  | some cmd =>
    rw [hp] at h
    refine ⟨List.getElem?_eq_some_iff.1 hp |>.1, ?_⟩
    intro hc
    cases hc
    simp [Cmd.exec] at h

/-- Each step changes every register by at most one. -/
theorem regs_step_le {P : Program r} {d e : Config r} (hP : WF P) (h : step P d = some e) (j : Fin r) :
    e.regs j ≤ d.regs j + 1 := by
  unfold step at h
  cases hp : P[d.pc]? with
  | none => rw [hp] at h; simp at h
  | some cmd =>
    rw [hp] at h
    cases cmd with
    | goto k => simp [Cmd.exec] at h; subst h; simp
    | ifLt a b k => simp [Cmd.exec] at h; subst h; simp
    | ifLe a b k => simp [Cmd.exec] at h; subst h; simp
    | arith δ =>
      simp only [Cmd.exec] at h
      split_ifs at h with hδ
      · cases h
        have := (hP.arith_ok _ _ hp j).2
        show ((d.regs j : ℤ) + δ j).toNat ≤ d.regs j + 1
        omega
    | stop => simp [Cmd.exec] at h

/-- The contents of any register at time `t` cannot exceed `x + t`. -/
theorem regs_run_le {P : Program r} (hP : WF P) {x : ℕ} {t : ℕ} {c : Config r}
    (h : run P (init r x) t = some c) (j : Fin r) : c.regs j ≤ x + t := by
  induction t generalizing c with
  | zero =>
    simp only [run_zero, Option.some.injEq] at h
    subst h
    simp only [init]
    split_ifs <;> omega
  | succ t ih =>
    rw [run_succ] at h
    cases hs : run P (init r x) t with
    | none => rw [hs] at h; simp at h
    | some d =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      have := regs_step_le hP h j
      have := ih hs
      omega

end RM
end JM1984
