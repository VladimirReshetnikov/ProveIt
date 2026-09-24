import Diophantine.Paper1984.Machine
import Mathlib.Data.Nat.Size

/-!
# Jones–Matijasevič 1984, §4: register machines with fast commands

The commands (41) `Ri ← Ri + Rj` and (42) `Rj ← ⌈Rj/2⌉` are added to the commands of §3.
We verify the macros of §4, each placed at an offset `o` of a program and exiting to the line
after it:

* `R ← 0`: iterate (42) while `R > 1`, then subtract `1` if `R = 1` (the edition's repair: halving
  alone never clears a positive register); `3⌈log₂ R⌉ + 3` steps suffice;
* the even test (44), through the trick (43) `R ≡ 0 (mod 2) ⟺ 2⌈R/2⌉ ≤ R` with one scratch
  register;
* the multiplication (45) `Ri ← Rj · Rk`, destroying `Rj` and `Rk`, in `O(log Rk)` passes.
-/

namespace JM1984
namespace RM

variable {r : ℕ}

/-- Commands of §3 and the fast commands (41), (42). -/
inductive XCmd (r : ℕ)
  | base (c : Cmd r)
  | add (i j : Fin r)
  | half (j : Fin r)

/-- One command. -/
def XCmd.exec (pc : ℕ) (regs : Fin r → ℕ) : XCmd r → Option (Config r)
  | .base c => c.exec pc regs
  | .add i j => some ⟨pc + 1, Function.update regs i (regs i + regs j)⟩
  | .half j => some ⟨pc + 1, Function.update regs j ((regs j + 1) / 2)⟩

abbrev XProgram (r : ℕ) := List (XCmd r)

def xstep (P : XProgram r) (c : Config r) : Option (Config r) :=
  match P[c.pc]? with
  | some cmd => cmd.exec c.pc c.regs
  | none => none

def xrun (P : XProgram r) (c : Config r) : ℕ → Option (Config r)
  | 0 => some c
  | n + 1 => (xrun P c n).bind (xstep P)

theorem xrun_add (P : XProgram r) (c : Config r) (m n : ℕ) :
    xrun P c (m + n) = (xrun P c m).bind (fun d => xrun P d n) := by
  induction n with
  | zero => cases xrun P c m <;> rfl
  | succ n ih =>
    rw [← Nat.add_assoc, xrun, ih]
    cases xrun P c m with
    | none => rfl
    | some d => rfl

/-- `c` reaches `d` in exactly `n` steps. -/
def Reaches (P : XProgram r) (c d : Config r) (n : ℕ) : Prop := xrun P c n = some d

theorem Reaches.refl (P : XProgram r) (c : Config r) : Reaches P c c 0 := rfl

theorem Reaches.trans {P : XProgram r} {c d e : Config r} {m n : ℕ}
    (h1 : Reaches P c d m) (h2 : Reaches P d e n) : Reaches P c e (m + n) := by
  unfold Reaches at *
  rw [xrun_add, h1]; exact h2

theorem Reaches.single {P : XProgram r} {c d : Config r} (h : xstep P c = some d) :
    Reaches P c d 1 := by
  unfold Reaches xrun; simp only [xrun, Option.bind_some]; exact h

theorem xstep_of_get {P : XProgram r} {c : Config r} {cmd : XCmd r}
    (h : P[c.pc]? = some cmd) : xstep P c = cmd.exec c.pc c.regs := by
  unfold xstep; rw [h]

/-! ### Clearing a register -/

/-- `R_j ← 0` at offset `o`. -/
def zeroMacro (o : ℕ) (j : Fin r) : List (XCmd r) :=
  [.base (.ifLe (.reg j) .one (o + 3)), .half j, .base (.goto o),
    .base (.ifLt (.reg j) .one (o + 5)), .base (.arith fun k => if k = j then -1 else 0)]

/-- The macro placed at offset `o` of `P`. -/
def Placed (P : XProgram r) (o : ℕ) (M : List (XCmd r)) : Prop :=
  ∀ k (hk : k < M.length), P[o + k]? = some (M[k]'hk)

/-- The halving loop: from line `o` with `R_j = v`, line `o + 3` is reached with `R_j = min v 1`
after `3⌈log₂ v⌉ + 1` steps. -/
theorem zero_loop {P : XProgram r} {o : ℕ} {j : Fin r} (hP : Placed P o (zeroMacro o j)) :
    ∀ (v : ℕ) (regs : Fin r → ℕ), regs j = v →
      Reaches P ⟨o, regs⟩ ⟨o + 3, Function.update regs j (min v 1)⟩ (3 * Nat.clog 2 v + 1) := by
  intro v
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro regs hv
    have l0 : P[o]? = some (.base (.ifLe (.reg j) .one (o + 3))) := hP 0 (by simp [zeroMacro])
    rcases Nat.lt_or_ge 1 v with hv1 | hv1
    · have l1 : P[o + 1]? = some (.half j) := hP 1 (by simp [zeroMacro])
      have l2 : P[o + 2]? = some (.base (.goto o)) := hP 2 (by simp [zeroMacro])
      have s0 : Reaches P ⟨o, regs⟩ ⟨o + 1, regs⟩ 1 := by
        apply Reaches.single
        rw [xstep_of_get (c := ⟨o, regs⟩) l0]
        simp [XCmd.exec, Cmd.exec, Operand.val, hv]; omega
      have s1 : Reaches P ⟨o + 1, regs⟩
          ⟨o + 2, Function.update regs j ((v + 1) / 2)⟩ 1 := by
        apply Reaches.single
        rw [xstep_of_get (c := ⟨o + 1, regs⟩) l1]
        simp [XCmd.exec, hv]
      have s2 : Reaches P ⟨o + 2, Function.update regs j ((v + 1) / 2)⟩
          ⟨o, Function.update regs j ((v + 1) / 2)⟩ 1 := by
        apply Reaches.single
        rw [xstep_of_get (c := ⟨o + 2, _⟩) l2]
        simp [XCmd.exec, Cmd.exec]
      have hrec := ih ((v + 1) / 2) (by omega) (Function.update regs j ((v + 1) / 2)) (by simp)
      have hmin : min ((v + 1) / 2) 1 = min v 1 := by omega
      rw [Function.update_idem, hmin] at hrec
      have hclog : Nat.clog 2 v = Nat.clog 2 ((v + 1) / 2) + 1 := by
        have := Nat.clog_of_one_lt (b := 2) (by norm_num) hv1
        simpa using this
      have := ((s0.trans s1).trans s2).trans hrec
      rw [hclog]
      convert this using 1
      ring
    · rw [Nat.clog_of_right_le_one hv1]
      show Reaches P _ _ 1
      apply Reaches.single
      rw [xstep_of_get (c := ⟨o, regs⟩) l0]
      simp only [XCmd.exec, Cmd.exec, Operand.val, hv, if_pos hv1]
      have : Function.update regs j (min v 1) = regs := by
        rw [show min v 1 = v by omega, ← hv, Function.update_eq_self]
      rw [this]

/-- **`R_j ← 0`**, in at most `3⌈log₂ R_j⌉ + 3` steps. -/
theorem zero_macro {P : XProgram r} {o : ℕ} {j : Fin r} (hP : Placed P o (zeroMacro o j))
    (regs : Fin r → ℕ) :
    ∃ n ≤ 3 * Nat.clog 2 (regs j) + 3,
      Reaches P ⟨o, regs⟩ ⟨o + 5, Function.update regs j 0⟩ n := by
  have hloop := zero_loop hP (regs j) regs rfl
  have l3 : P[o + 3]? = some (.base (.ifLt (.reg j) .one (o + 5))) := hP 3 (by simp [zeroMacro])
  have l4 : P[o + 4]? = some (.base (.arith fun k => if k = j then -1 else 0)) :=
    hP 4 (by simp [zeroMacro])
  rcases Nat.eq_zero_or_pos (regs j) with h0 | hpos
  · refine ⟨3 * Nat.clog 2 (regs j) + 1 + 1, by omega, hloop.trans (Reaches.single ?_)⟩
    rw [xstep_of_get (c := ⟨o + 3, _⟩) l3]
    simp [XCmd.exec, Cmd.exec, Operand.val, h0]
  · refine ⟨3 * Nat.clog 2 (regs j) + 1 + 1 + 1, by omega,
      (hloop.trans (Reaches.single (d := ⟨o + 4, Function.update regs j 1⟩) ?_)).trans
        (Reaches.single ?_)⟩
    · rw [xstep_of_get (c := ⟨o + 3, _⟩) l3]
      simp [XCmd.exec, Cmd.exec, Operand.val, show min (regs j) 1 = 1 by omega]
    · rw [xstep_of_get (c := ⟨o + 4, _⟩) l4]
      simp only [XCmd.exec, Cmd.exec]
      rw [if_pos (fun k => by
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk])]
      simp only [Option.some.injEq, Config.mk.injEq, true_and]
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]

theorem Placed.sub {P : XProgram r} {o : ℕ} {M N : List (XCmd r)} (h : Placed P o (M ++ N)) :
    Placed P o M := fun k hk => by
  have := h k (by simp; omega)
  rwa [List.getElem_append_left hk] at this

theorem Placed.shift {P : XProgram r} {o : ℕ} {M N : List (XCmd r)} (h : Placed P o (M ++ N)) :
    Placed P (o + M.length) N := fun k hk => by
  have := h (M.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

/-! ### The even test (44) -/

/-- `IF R_i ≡ 0 (mod 2) GO TO k`, with the scratch register `t ≠ i`, by (43). -/
def evenMacro (o : ℕ) (i t : Fin r) (k : ℕ) : List (XCmd r) :=
  zeroMacro o t ++ [.add t i, .half t, .add t t, .base (.ifLe (.reg t) (.reg i) k)]

theorem evenMacro_length (o : ℕ) (i t : Fin r) (k : ℕ) : (evenMacro o i t k).length = 9 := rfl

/-- **The even test (44).** -/
theorem even_macro {P : XProgram r} {o k : ℕ} {i t : Fin r} (hit : i ≠ t)
    (hP : Placed P o (evenMacro o i t k)) (regs : Fin r → ℕ) :
    ∃ n ≤ 3 * Nat.clog 2 (regs t) + 7,
      Reaches P ⟨o, regs⟩
        ⟨if regs i % 2 = 0 then k else o + 9,
          Function.update regs t (2 * ((regs i + 1) / 2))⟩ n := by
  obtain ⟨n₀, hn₀, h₀⟩ := zero_macro (Placed.sub hP) regs
  have hQ := Placed.shift hP
  have l5 : P[o + 5]? = some (.add t i) := hQ 0 (by simp)
  have l6 : P[o + 6]? = some (.half t) := hQ 1 (by simp)
  have l7 : P[o + 7]? = some (.add t t) := hQ 2 (by simp)
  have l8 : P[o + 8]? = some (.base (.ifLe (.reg t) (.reg i) k)) :=
    hQ 3 (by simp)
  have hti : t ≠ i := fun h => hit h.symm
  refine ⟨n₀ + 1 + 1 + 1 + 1, by omega, (((h₀.trans
    (Reaches.single (d := ⟨o + 6, Function.update regs t (regs i)⟩) ?_)).trans
    (Reaches.single (d := ⟨o + 7, Function.update regs t ((regs i + 1) / 2)⟩) ?_)).trans
    (Reaches.single (d := ⟨o + 8, Function.update regs t (2 * ((regs i + 1) / 2))⟩) ?_)).trans
    (Reaches.single ?_)⟩
  · rw [xstep_of_get (c := ⟨o + 5, _⟩) l5]
    simp [XCmd.exec, Function.update_of_ne hit]
  · rw [xstep_of_get (c := ⟨o + 6, _⟩) l6]
    simp [XCmd.exec]
  · rw [xstep_of_get (c := ⟨o + 7, _⟩) l7]
    simp [XCmd.exec, two_mul]
  · rw [xstep_of_get (c := ⟨o + 8, _⟩) l8]
    simp only [XCmd.exec, Cmd.exec, Operand.val, Function.update_self,
      Function.update_of_ne hit, Option.some.injEq, Config.mk.injEq, and_true]
    by_cases h : regs i % 2 = 0
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-! ### The quotient `R_i ← ⌊R_i/2⌋` -/

/-- `R_i ← ⌊R_i/2⌋`, with the scratch register `t ≠ i`. -/
def quotMacro (o : ℕ) (i t : Fin r) : List (XCmd r) :=
  evenMacro o i t (o + 10) ++ [.base (.arith fun k => if k = i then -1 else 0), .half i]

theorem quotMacro_length (o : ℕ) (i t : Fin r) : (quotMacro o i t).length = 11 := rfl

/-- **The quotient macro.** -/
theorem quot_macro {P : XProgram r} {o : ℕ} {i t : Fin r} (hit : i ≠ t)
    (hP : Placed P o (quotMacro o i t)) (regs : Fin r → ℕ) :
    ∃ n ≤ 3 * Nat.clog 2 (regs t) + 9,
      Reaches P ⟨o, regs⟩
        ⟨o + 11, Function.update (Function.update regs t (2 * ((regs i + 1) / 2))) i
          (regs i / 2)⟩ n := by
  obtain ⟨n₀, hn₀, h₀⟩ := even_macro hit (Placed.sub hP) regs
  have hQ := Placed.shift hP
  have l9 : P[o + 9]? = some (.base (.arith fun k => if k = i then -1 else 0)) :=
    hQ 0 (by simp)
  have l10 : P[o + 10]? = some (.half i) := hQ 1 (by simp)
  set regs' := Function.update regs t (2 * ((regs i + 1) / 2)) with hregs'
  have hri : regs' i = regs i := by rw [hregs', Function.update_of_ne hit]
  by_cases h : regs i % 2 = 0
  · rw [if_pos h] at h₀
    refine ⟨n₀ + 1, by omega, h₀.trans (Reaches.single ?_)⟩
    rw [xstep_of_get (c := ⟨o + 10, _⟩) l10]
    simp only [XCmd.exec, hri, Option.some.injEq, Config.mk.injEq, true_and]
    congr 1; omega
  · rw [if_neg h] at h₀
    refine ⟨n₀ + 1 + 1, by omega,
      (h₀.trans (Reaches.single (d := ⟨o + 10, Function.update regs' i (regs i - 1)⟩) ?_)).trans
        (Reaches.single ?_)⟩
    · rw [xstep_of_get (c := ⟨o + 9, _⟩) l9]
      simp only [XCmd.exec, Cmd.exec]
      rw [if_pos (fun k => by
        by_cases hk : k = i
        · subst hk; simp [hri]; omega
        · simp [hk])]
      simp only [Option.some.injEq, Config.mk.injEq, true_and]
      funext k
      by_cases hk : k = i
      · subst hk; simp [hri]; omega
      · simp [hk]
    · rw [xstep_of_get (c := ⟨o + 10, _⟩) l10]
      simp only [XCmd.exec, Function.update_self, Function.update_idem, Option.some.injEq,
        Config.mk.injEq, true_and]
      congr 1; omega

/-! ### Multiplication (45) -/

/-- (45): `R_i ← R_j · R_k` for distinct `i, j, k` and a scratch register `t`. -/
def mulMacro (o : ℕ) (i j k t : Fin r) : List (XCmd r) :=
  zeroMacro o i ++ evenMacro (o + 5) k t (o + 15) ++ [.add i j] ++ quotMacro (o + 15) k t ++
    [.add j j, .base (.ifLt .zero (.reg k) (o + 5))]

theorem mulMacro_length (o : ℕ) (i j k t : Fin r) : (mulMacro o i j k t).length = 28 := rfl

theorem mulMacro_get (o : ℕ) (i j k t : Fin r) (m : ℕ) (hm : m < 28) :
    (mulMacro o i j k t)[m]'(by rw [mulMacro_length]; exact hm) =
      if h : m < 5 then (zeroMacro o i)[m]'(by simpa [zeroMacro] using h)
      else if h' : m < 14 then (evenMacro (o + 5) k t (o + 15))[m - 5]'(by
          rw [evenMacro_length]; omega)
      else if m = 14 then .add i j
      else if h'' : m < 26 then (quotMacro (o + 15) k t)[m - 15]'(by
          rw [quotMacro_length]; omega)
      else if m = 26 then .add j j
      else .base (.ifLt .zero (.reg k) (o + 5)) := by
  interval_cases m <;> rfl

theorem clog_mono {a b : ℕ} (h : a ≤ b) : Nat.clog 2 a ≤ Nat.clog 2 b :=
  Nat.clog_mono_right 2 h

set_option maxHeartbeats 1000000 in
/-- The loop of (45), entered at `L1 = o + 5` with `R_k = b`. -/
theorem mul_loop {P : XProgram r} {o : ℕ} {i j k t : Fin r} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hit : i ≠ t) (hjt : j ≠ t) (hkt : k ≠ t)
    (hP : Placed P o (mulMacro o i j k t)) :
    ∀ (b : ℕ) (regs : Fin r → ℕ), regs k = b →
      ∃ regs' : Fin r → ℕ, ∃ n ≤ (Nat.size b + 1) * (6 * Nat.clog 2 (max (regs t) (b + 1)) + 21),
        Reaches P ⟨o + 5, regs⟩ ⟨o + 28, regs'⟩ n ∧ regs' i = regs i + regs j * b ∧ regs' k = 0 ∧
          ∀ m, m ≠ i → m ≠ j → m ≠ k → m ≠ t → regs' m = regs m := by
  have hE : Placed P (o + 5) (evenMacro (o + 5) k t (o + 15)) := fun m hm => by
    rw [evenMacro_length] at hm
    have := hP (5 + m) (by rw [mulMacro_length]; omega)
    rw [mulMacro_get o i j k t (5 + m) (by omega), dif_neg (by omega), dif_pos (by omega)] at this
    rw [← Nat.add_assoc] at this
    simpa using this
  have l14 : P[o + 14]? = some (.add i j) := by
    have := hP 14 (by rw [mulMacro_length]; decide); rw [mulMacro_get o i j k t 14 (by decide)] at this; simpa using this
  have hQm : Placed P (o + 15) (quotMacro (o + 15) k t) := fun m hm => by
    rw [quotMacro_length] at hm
    have := hP (15 + m) (by rw [mulMacro_length]; omega)
    rw [mulMacro_get o i j k t (15 + m) (by omega), dif_neg (by omega), dif_neg (by omega),
      if_neg (by omega), dif_pos (by omega)] at this
    rw [← Nat.add_assoc] at this
    simpa using this
  have l26 : P[o + 26]? = some (.add j j) := by
    have := hP 26 (by rw [mulMacro_length]; decide); rw [mulMacro_get o i j k t 26 (by decide)] at this; simpa using this
  have l27 : P[o + 27]? = some (.base (.ifLt .zero (.reg k) (o + 5))) := by
    have := hP 27 (by rw [mulMacro_length]; decide); rw [mulMacro_get o i j k t 27 (by decide)] at this; simpa using this
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro regs hb
    -- the even test
    obtain ⟨n₁, hn₁, h₁⟩ := even_macro hkt hE regs
    rw [hb] at h₁
    set regs1 := Function.update regs t (2 * ((b + 1) / 2)) with hregs1
    -- the conditional addition
    obtain ⟨regs2, n₂, hn₂, h₂, h2i, h2j, h2k, h2t, h2m⟩ :
        ∃ regs2 : Fin r → ℕ, ∃ n₂ ≤ 1, Reaches P ⟨if b % 2 = 0 then o + 15 else o + 5 + 9, regs1⟩
          ⟨o + 15, regs2⟩ n₂ ∧ regs2 i = regs i + regs j * (b % 2) ∧ regs2 j = regs j ∧
          regs2 k = b ∧ regs2 t = 2 * ((b + 1) / 2) ∧
          ∀ m, m ≠ i → m ≠ j → m ≠ k → m ≠ t → regs2 m = regs m := by
      by_cases hev : b % 2 = 0
      · refine ⟨regs1, 0, by norm_num, by rw [if_pos hev]; exact Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hregs1, Function.update_of_ne hit, hev]; ring
        · rw [hregs1, Function.update_of_ne hjt]
        · rw [hregs1, Function.update_of_ne hkt, hb]
        · rw [hregs1, Function.update_self]
        · intro m _ _ _ hmt; rw [hregs1, Function.update_of_ne hmt]
      · refine ⟨Function.update regs1 i (regs1 i + regs1 j), 1, by norm_num,
          by rw [if_neg hev]; exact Reaches.single (by
            rw [xstep_of_get (c := ⟨o + 5 + 9, _⟩) l14]; rfl), ?_, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_self, hregs1, Function.update_of_ne hit, Function.update_of_ne hjt,
            show b % 2 = 1 by omega, mul_one]
        · rw [Function.update_of_ne (Ne.symm hij), hregs1, Function.update_of_ne hjt]
        · rw [Function.update_of_ne (Ne.symm hik), hregs1, Function.update_of_ne hkt, hb]
        · rw [Function.update_of_ne (Ne.symm hit), hregs1, Function.update_self]
        · intro m hmi _ _ hmt
          rw [Function.update_of_ne hmi, hregs1, Function.update_of_ne hmt]
    -- the quotient
    obtain ⟨n₃, hn₃, h₃⟩ := quot_macro hkt hQm regs2
    set regs3 := Function.update (Function.update regs2 t (2 * ((regs2 k + 1) / 2))) k
      (regs2 k / 2) with hregs3
    -- doubling `R_j`
    have h₄ : Reaches P ⟨o + 15 + 11, regs3⟩
        ⟨o + 27, Function.update regs3 j (regs3 j + regs3 j)⟩ 1 :=
      Reaches.single (by rw [xstep_of_get (c := ⟨o + 15 + 11, _⟩) l26]; rfl)
    set regs4 := Function.update regs3 j (regs3 j + regs3 j) with hregs4
    have h4k : regs4 k = b / 2 := by
      rw [hregs4, Function.update_of_ne (Ne.symm hjk), hregs3, Function.update_self, h2k]
    have h4i : regs4 i = regs i + regs j * (b % 2) := by
      rw [hregs4, Function.update_of_ne hij, hregs3, Function.update_of_ne hik,
        Function.update_of_ne hit, h2i]
    have h4j : regs4 j = 2 * regs j := by
      rw [hregs4, Function.update_self, hregs3, Function.update_of_ne hjk,
        Function.update_of_ne hjt, h2j]; ring
    have h4t : regs4 t = 2 * ((b + 1) / 2) := by
      rw [hregs4, Function.update_of_ne (Ne.symm hjt), hregs3, Function.update_of_ne (Ne.symm hkt),
        Function.update_self, h2k]
    have h4m : ∀ m, m ≠ i → m ≠ j → m ≠ k → m ≠ t → regs4 m = regs m := by
      intro m hmi hmj hmk hmt
      rw [hregs4, Function.update_of_ne hmj, hregs3, Function.update_of_ne hmk,
        Function.update_of_ne hmt, h2m m hmi hmj hmk hmt]
    have hsteps : ∀ M, 2 * ((b + 1) / 2) ≤ M → regs t ≤ M →
        n₁ + n₂ + n₃ + 1 + 1 ≤ 6 * Nat.clog 2 M + 21 := by
      intro M h1 h2
      have c1 := clog_mono h2
      have c2 : Nat.clog 2 (regs2 t) ≤ Nat.clog 2 M := clog_mono (by rw [h2t]; exact h1)
      omega
    have h12 := h₁.trans h₂
    by_cases hb2 : 0 < b / 2
    · -- loop again
      have h₅ : Reaches P ⟨o + 27, regs4⟩ ⟨o + 5, regs4⟩ 1 := Reaches.single (by
        rw [xstep_of_get (c := ⟨o + 27, _⟩) l27]
        simp [XCmd.exec, Cmd.exec, Operand.val, h4k, hb2])
      obtain ⟨regs', n', hn', h', h'i, h'k, h'm⟩ := ih (b / 2) (by omega) regs4 h4k
      refine ⟨regs', n₁ + n₂ + n₃ + 1 + 1 + n', ?_,
        (((h12.trans h₃).trans h₄).trans h₅).trans h', ?_, h'k, ?_⟩
      · have hsz : Nat.size b = Nat.size (b / 2) + 1 := by
          have hb0 : b ≠ 0 := by omega
          have h := Nat.size_bit (b := b.bodd) (n := b.div2) (by rw [Nat.bit_bodd_div2]; exact hb0)
          rw [Nat.bit_bodd_div2, Nat.div2_val] at h
          omega
        set M := max (regs t) (b + 1)
        have hM1 : 2 * ((b + 1) / 2) ≤ M := le_trans (by omega) (le_max_right _ _)
        have hM2 : max (regs4 t) (b / 2 + 1) ≤ M := by
          rw [h4t]; exact max_le hM1 (le_trans (by omega) (le_max_right _ _))
        have c3 := clog_mono hM2
        have hs := hsteps M hM1 (le_max_left _ _)
        have hn'' : n' ≤ (Nat.size (b / 2) + 1) * (6 * Nat.clog 2 M + 21) :=
          le_trans hn' (Nat.mul_le_mul_left _ (by omega))
        rw [hsz]
        nlinarith
      · rw [h'i, h4i, h4j]
        have : b = b % 2 + 2 * (b / 2) := by omega
        conv_rhs => rw [this]
        ring
      · intro m hmi hmj hmk hmt
        rw [h'm m hmi hmj hmk hmt, h4m m hmi hmj hmk hmt]
    · -- exit
      have h₅ : Reaches P ⟨o + 27, regs4⟩ ⟨o + 28, regs4⟩ 1 := Reaches.single (by
        rw [xstep_of_get (c := ⟨o + 27, _⟩) l27]
        simp [XCmd.exec, Cmd.exec, Operand.val, h4k]; omega)
      refine ⟨regs4, n₁ + n₂ + n₃ + 1 + 1, ?_,
        ((h12.trans h₃).trans h₄).trans h₅, ?_, by rw [h4k]; omega, h4m⟩
      · have hs := hsteps (max (regs t) (b + 1)) (le_trans (by omega) (le_max_right _ _))
          (le_max_left _ _)
        nlinarith
      · rw [h4i]
        have : b % 2 = b := by omega
        rw [this]

/-- **The multiplication macro (45)**: `R_i ← R_j · R_k`, in
`O(log R_k · log max(R_t, R_k))` further steps (`R_j` and `R_k` are used destructively). -/
theorem mul_macro {P : XProgram r} {o : ℕ} {i j k t : Fin r} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hit : i ≠ t) (hjt : j ≠ t) (hkt : k ≠ t)
    (hP : Placed P o (mulMacro o i j k t)) (regs : Fin r → ℕ) :
    ∃ regs' : Fin r → ℕ, ∃ n ≤ 3 * Nat.clog 2 (regs i) + 3 +
        (Nat.size (regs k) + 1) * (6 * Nat.clog 2 (max (regs t) (regs k + 1)) + 21),
      Reaches P ⟨o, regs⟩ ⟨o + 28, regs'⟩ n ∧ regs' i = regs j * regs k ∧ regs' k = 0 ∧
        ∀ m, m ≠ i → m ≠ j → m ≠ k → m ≠ t → regs' m = regs m := by
  have hZ : Placed P o (zeroMacro o i) := fun m hm => by
    have hm5 : m < 5 := by simpa [zeroMacro] using hm
    have := hP m (by rw [mulMacro_length]; omega)
    rw [mulMacro_get o i j k t m (by omega), dif_pos hm5] at this
    exact this
  obtain ⟨n₀, hn₀, h₀⟩ := zero_macro hZ regs
  obtain ⟨regs', n, hn, h, hi, hk, hm⟩ := mul_loop hij hik hjk hit hjt hkt hP (regs k)
    (Function.update regs i 0) (by rw [Function.update_of_ne (Ne.symm hik)])
  refine ⟨regs', n₀ + n, ?_, h₀.trans h, ?_, hk, ?_⟩
  · rw [Function.update_of_ne (Ne.symm hit)] at hn; omega
  · rw [hi, Function.update_self, Function.update_of_ne (Ne.symm hij)]; ring
  · intro m hmi hmj hmk hmt
    rw [hm m hmi hmj hmk hmt, Function.update_of_ne hmi]

end RM
end JM1984
