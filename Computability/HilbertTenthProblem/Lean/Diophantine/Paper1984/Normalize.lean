import Diophantine.Paper1984.Theorem

/-!
# Jones–Matijasevič 1984, §3: normalizing a register machine program

The encoding (33)–(37) assumes, as the paper says after (32), that STOP occurs only once, at the
end, and (editorial addition) that no conditional jump targets its own line; a conditional jump
to the next line is a GO TO. `normalize` makes any program satisfy these conventions:

* the original lines `0, …, n−1` keep their positions;
* line `n` is a dead loop `GO TO Ln`, standing for every jump outside the program and for falling
  off its end;
* lines `n+1+i` are trampolines `GO TO Li`, and a conditional jump from line `i` to itself goes to
  its trampoline instead;
* a conditional jump from line `i` to line `i+1` becomes `GO TO L(i+1)`;
* every STOP becomes `GO TO L(2n+1)`, and line `2n+1` is the unique STOP.

For a *raw* program (parallel updates change registers by at most one; nothing else assumed),
`AcceptsStop P x` says that the machine started on `x` reaches a STOP line with all registers
zero. `normalize_wf` and `accepts_normalize_iff` show that `normalize P` is well formed and
accepts exactly the same inputs; `acceptsStop_iff` then applies the arithmetization.
-/

namespace JM1984
namespace RM

variable {r : ℕ}

/-- Acceptance for a raw program: a STOP line is reached with all registers zero. -/
def AcceptsStop (P : Program r) (x : ℕ) : Prop :=
  ∃ s c, run P (init r x) s = some c ∧ P[c.pc]? = some Cmd.stop ∧ c.regs = fun _ => 0

/-- A jump target folded into the program, with the dead line `n` outside it. -/
def fold (n k : ℕ) : ℕ := if k < n then k else n

/-- The normalized form of a conditional jump on line `i` with folded target `k'`. -/
def normCond (n i k' : ℕ) (c : ℕ → Cmd r) : Cmd r :=
  if k' = i then c (n + 1 + i) else if k' = i + 1 then Cmd.goto (i + 1) else c k'

/-- The normalized form of the command on line `i`. -/
def normCmd (n i : ℕ) : Cmd r → Cmd r
  | .goto k => .goto (fold n k)
  | .ifLt a b k => normCond n i (fold n k) (Cmd.ifLt a b)
  | .ifLe a b k => normCond n i (fold n k) (Cmd.ifLe a b)
  | .arith δ => .arith δ
  | .stop => .goto (2 * n + 1)

/-- The normalized program. -/
def normalize (P : Program r) : Program r :=
  P.mapIdx (fun i c => normCmd P.length i c) ++ [Cmd.goto P.length] ++
    (List.range P.length).map Cmd.goto ++ [Cmd.stop]

section Lines

variable (P : Program r)

theorem normalize_length : (normalize P).length = 2 * P.length + 2 := by
  simp [normalize]; ring

theorem normalize_orig {i : ℕ} (hi : i < P.length) :
    (normalize P)[i]? = P[i]?.map (normCmd P.length i) := by
  simp [normalize, List.getElem?_append_left, hi]

theorem normalize_dead : (normalize P)[P.length]? = some (Cmd.goto P.length) := by
  simp [normalize]

theorem normalize_tramp {i : ℕ} (hi : i < P.length) :
    (normalize P)[P.length + 1 + i]? = some (Cmd.goto i) := by
  simp only [normalize, List.append_assoc, List.singleton_append]
  rw [List.getElem?_append_right (by simp; omega), List.length_mapIdx, List.cons_append,
    show P.length + 1 + i - P.length = i + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by simpa using hi), List.getElem?_map, List.getElem?_range hi]
  rfl

theorem normalize_stop : (normalize P)[2 * P.length + 1]? = some Cmd.stop := by
  simp only [normalize, List.append_assoc, List.singleton_append]
  rw [List.getElem?_append_right (by simp; omega), List.length_mapIdx, List.cons_append,
    show 2 * P.length + 1 - P.length = P.length + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp)]
  simp

end Lines

/-- The lines of the normalized program. -/
theorem normalize_get (P : Program r) (i : ℕ) :
    (normalize P)[i]? =
      if i < P.length then P[i]?.map (normCmd P.length i)
      else if i = P.length then some (Cmd.goto P.length)
      else if i < 2 * P.length + 1 then some (Cmd.goto (i - P.length - 1))
      else if i = 2 * P.length + 1 then some Cmd.stop else none := by
  split_ifs with h1 h2 h3 h4
  · exact normalize_orig P h1
  · subst h2; exact normalize_dead P
  · have := normalize_tramp P (i := i - P.length - 1) (by omega)
    rwa [show P.length + 1 + (i - P.length - 1) = i by omega] at this
  · subst h4; exact normalize_stop P
  · rw [List.getElem?_eq_none]; rw [normalize_length]; omega

theorem fold_le (n k : ℕ) : fold n k ≤ n := by unfold fold; split_ifs <;> omega

/-- Raw programs: parallel updates change each register by at most one. -/
def RawOk (P : Program r) : Prop :=
  ∀ (i : ℕ) (δ : Fin r → ℤ), P[i]? = some (Cmd.arith δ) → ∀ j, -1 ≤ δ j ∧ δ j ≤ 1

theorem normCmd_cases (n i : ℕ) (hi : i < n) (c : Cmd r) :
    (∃ k, normCmd n i c = Cmd.goto k ∧ k ≤ 2 * n + 1 ∧ (k = 2 * n + 1 → c = Cmd.stop)) ∨
    (∃ a b k, normCmd n i c = Cmd.ifLt a b k ∧ k < 2 * n + 2 ∧ k ≠ i ∧ k ≠ i + 1) ∨
    (∃ a b k, normCmd n i c = Cmd.ifLe a b k ∧ k < 2 * n + 2 ∧ k ≠ i ∧ k ≠ i + 1) ∨
    (∃ δ, normCmd n i c = Cmd.arith δ ∧ c = Cmd.arith δ) := by
  have hf := fun k => fold_le n k
  cases c with
  | goto k => exact Or.inl ⟨fold n k, rfl, by have := hf k; omega, fun h => by have := hf k; omega⟩
  | ifLt a b k =>
    simp only [normCmd, normCond]
    split_ifs with h1 h2
    · exact Or.inr (Or.inl ⟨a, b, n + 1 + i, rfl, by omega, by omega, by omega⟩)
    · exact Or.inl ⟨i + 1, rfl, by omega, fun h => by omega⟩
    · exact Or.inr (Or.inl ⟨a, b, fold n k, rfl, by have := hf k; omega, h1, h2⟩)
  | ifLe a b k =>
    simp only [normCmd, normCond]
    split_ifs with h1 h2
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, n + 1 + i, rfl, by omega, by omega, by omega⟩))
    · exact Or.inl ⟨i + 1, rfl, by omega, fun h => by omega⟩
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, fold n k, rfl, by have := hf k; omega, h1, h2⟩))
  | arith δ => exact Or.inr (Or.inr (Or.inr ⟨δ, rfl, rfl⟩))
  | stop => exact Or.inl ⟨2 * n + 1, rfl, le_rfl, fun _ => rfl⟩

/-- **The normalized program is well formed.** -/
theorem normalize_wf (P : Program r) (hP : RawOk P) : WF (normalize P) where
  pos := by rw [normalize_length]; omega
  last_stop := by rw [normalize_length, show 2 * P.length + 2 - 1 = 2 * P.length + 1 by omega];
                  exact normalize_stop P
  stop_last := by
    intro i hi
    rw [normalize_length]
    rw [normalize_get] at hi
    split_ifs at hi with h1 h2 h3 h4
    · obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.1 hi
      rcases normCmd_cases P.length i h1 c with ⟨k, hk, -⟩ | ⟨a, b, k, hk, -⟩ | ⟨a, b, k, hk, -⟩ |
        ⟨δ, hk, -⟩ <;> rw [hk] at he <;> cases he
    · cases hi
    · cases hi
    · omega
  goto_lt := by
    intro i k hi
    rw [normalize_length]
    rw [normalize_get] at hi
    split_ifs at hi with h1 h2 h3 h4
    · obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.1 hi
      rcases normCmd_cases P.length i h1 c with ⟨k', hk, hk2, -⟩ | ⟨a, b, k', hk, -⟩ |
        ⟨a, b, k', hk, -⟩ | ⟨δ, hk, -⟩ <;> rw [hk] at he <;> cases he
      omega
    · cases hi; omega
    · cases hi; omega
    · cases hi
  ifLt_ok := by
    intro i a b k hi
    rw [normalize_length]
    rw [normalize_get] at hi
    split_ifs at hi with h1 h2 h3 h4
    · obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.1 hi
      rcases normCmd_cases P.length i h1 c with ⟨k', hk, -⟩ | ⟨a', b', k', hk, hk1, hk2, hk3⟩ |
        ⟨a', b', k', hk, -⟩ | ⟨δ, hk, -⟩ <;> rw [hk] at he <;> cases he
      exact ⟨hk1, hk2, hk3⟩
    · cases hi
    · cases hi
    · cases hi
  ifLe_ok := by
    intro i a b k hi
    rw [normalize_length]
    rw [normalize_get] at hi
    split_ifs at hi with h1 h2 h3 h4
    · obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.1 hi
      rcases normCmd_cases P.length i h1 c with ⟨k', hk, -⟩ | ⟨a', b', k', hk, -⟩ |
        ⟨a', b', k', hk, hk1, hk2, hk3⟩ | ⟨δ, hk, -⟩ <;> rw [hk] at he <;> cases he
      exact ⟨hk1, hk2, hk3⟩
    · cases hi
    · cases hi
    · cases hi
  arith_ok := by
    intro i δ hi
    rw [normalize_get] at hi
    split_ifs at hi with h1 h2 h3 h4
    · obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.1 hi
      rcases normCmd_cases P.length i h1 c with ⟨k', hk, -⟩ | ⟨a', b', k', hk, -⟩ |
        ⟨a', b', k', hk, -⟩ | ⟨δ', hk, hc'⟩ <;> rw [hk] at he <;> cases he
      rw [hc'] at hc
      exact hP i δ hc
    · cases hi
    · cases hi
    · cases hi

/-! ### Simulation -/

/-- Reachability in some number of steps. -/
def Reach (P : Program r) (c d : Config r) : Prop := ∃ s, run P c s = some d

theorem Reach.refl (P : Program r) (c : Config r) : Reach P c c := ⟨0, rfl⟩

theorem Reach.tail {P : Program r} {c d e : Config r} (h : Reach P c d) (he : step P d = some e) :
    Reach P c e := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s + 1, by rw [run_succ_of_eq hs]; exact he⟩

theorem run_add' (P : Program r) (c : Config r) (s t : ℕ) :
    run P c (s + t) = (run P c s).bind (fun d => run P d t) := by
  induction t with
  | zero => cases run P c s <;> rfl
  | succ t ih =>
    rw [← Nat.add_assoc, run_succ, ih]
    cases run P c s with
    | none => rfl
    | some d => rfl

theorem Reach.trans {P : Program r} {c d e : Config r} (h1 : Reach P c d) (h2 : Reach P d e) :
    Reach P c e := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  exact ⟨s + t, by rw [run_add', hs]; exact ht⟩

theorem Reach.ind {P : Program r} {c : Config r} (motive : Config r → Prop) (h0 : motive c)
    (hs : ∀ d e, Reach P c d → motive d → step P d = some e → motive e) :
    ∀ d, Reach P c d → motive d := by
  intro d ⟨s, hsd⟩
  induction s generalizing d with
  | zero => cases hsd; exact h0
  | succ s ih =>
    rw [run_succ] at hsd
    cases hrun : run P c s with
    | none => rw [hrun] at hsd; simp at hsd
    | some d' =>
      rw [hrun] at hsd
      exact hs d' d ⟨s, hrun⟩ (ih d' hrun) hsd

theorem step_of_get {P : Program r} {c : Config r} {cmd : Cmd r} (h : P[c.pc]? = some cmd) :
    step P c = cmd.exec c.pc c.regs := by
  unfold step; rw [h]

theorem fold_of_lt {n k : ℕ} (h : k < n) : fold n k = k := if_pos h
theorem fold_of_ge {n k : ℕ} (h : ¬ k < n) : fold n k = n := if_neg h
theorem fold_succ {n i : ℕ} (h : i < n) : fold n (i + 1) = i + 1 := by
  unfold fold; split_ifs <;> omega

/-- The embedding of original configurations. -/
def emb (n : ℕ) (d : Config r) : Config r := ⟨fold n d.pc, d.regs⟩

theorem forward_step (P : Program r) {d e : Config r} (hs : step P d = some e) :
    Reach (normalize P) (emb P.length d) (emb P.length e) := by
  obtain ⟨hlt, -⟩ := pc_lt_of_step hs
  obtain ⟨cmd, hcmd⟩ := Option.isSome_iff_exists.1 (by
    rw [List.getElem?_eq_getElem hlt]; rfl : (P[d.pc]?).isSome)
  rw [step_of_get hcmd] at hs
  have hemb : emb P.length d = d := by cases d; simp [emb, fold_of_lt hlt]
  rw [hemb]
  have hnew : (normalize P)[d.pc]? = some (normCmd P.length d.pc cmd) := by
    rw [normalize_orig P hlt, hcmd]; rfl
  have one : (normCmd P.length d.pc cmd).exec d.pc d.regs = some (emb P.length e) →
      Reach (normalize P) d (emb P.length e) := fun h1 =>
    (Reach.refl _ _).tail (by rw [step_of_get hnew]; exact h1)
  have hs1 := fold_succ hlt
  cases cmd with
  | goto k =>
    simp only [Cmd.exec, Option.some.injEq] at hs; subst hs
    exact one rfl
  | ifLt a b k =>
    simp only [Cmd.exec, Option.some.injEq] at hs; subst hs
    by_cases h1 : fold P.length k = d.pc
    · by_cases hc : a.val d.regs < b.val d.regs
      · have h2 : Reach (normalize P) d ⟨P.length + 1 + d.pc, d.regs⟩ :=
          (Reach.refl _ _).tail (by rw [step_of_get hnew]; simp [normCmd, normCond, h1, Cmd.exec, hc])
        refine h2.tail ?_
        rw [step_of_get (normalize_tramp P hlt)]
        simp [Cmd.exec, emb, hc, h1]
      · exact one (by simp [normCmd, normCond, h1, Cmd.exec, hc, emb, hs1])
    · by_cases h2 : fold P.length k = d.pc + 1
      · refine one ?_
        by_cases hc : a.val d.regs < b.val d.regs <;>
          simp [normCmd, normCond, h2, Cmd.exec, emb, hc, hs1]
      · by_cases hc : a.val d.regs < b.val d.regs <;>
          exact one (by simp [normCmd, normCond, h1, h2, Cmd.exec, hc, emb, hs1])
  | ifLe a b k =>
    simp only [Cmd.exec, Option.some.injEq] at hs; subst hs
    by_cases h1 : fold P.length k = d.pc
    · by_cases hc : a.val d.regs ≤ b.val d.regs
      · have h2 : Reach (normalize P) d ⟨P.length + 1 + d.pc, d.regs⟩ :=
          (Reach.refl _ _).tail (by rw [step_of_get hnew]; simp [normCmd, normCond, h1, Cmd.exec, hc])
        refine h2.tail ?_
        rw [step_of_get (normalize_tramp P hlt)]
        simp [Cmd.exec, emb, hc, h1]
      · exact one (by simp [normCmd, normCond, h1, Cmd.exec, hc, emb, hs1])
    · by_cases h2 : fold P.length k = d.pc + 1
      · refine one ?_
        by_cases hc : a.val d.regs ≤ b.val d.regs <;>
          simp [normCmd, normCond, h2, Cmd.exec, emb, hc, hs1]
      · by_cases hc : a.val d.regs ≤ b.val d.regs <;>
          exact one (by simp [normCmd, normCond, h1, h2, Cmd.exec, hc, emb, hs1])
  | arith δ =>
    refine one ?_
    simp only [Cmd.exec] at hs
    split_ifs at hs with hδ
    cases hs
    simp [normCmd, Cmd.exec, hδ, emb, hs1]
  | stop => simp [Cmd.exec] at hs

/-- The backward invariant of the normalized run. -/
def Inv (P : Program r) (x : ℕ) (c' : Config r) : Prop :=
  ∃ c, Reach P (init r x) c ∧
    ((c'.pc < P.length ∧ c = c') ∨
     (c'.pc = P.length ∧ P.length ≤ c.pc) ∨
     (P.length < c'.pc ∧ c'.pc < 2 * P.length + 1 ∧ c.pc = c'.pc - P.length - 1 ∧
        c.regs = c'.regs) ∨
     (c'.pc = 2 * P.length + 1 ∧ P[c.pc]? = some Cmd.stop ∧ c.regs = c'.regs))

theorem inv_step (P : Program r) (x : ℕ) {c' e' : Config r} (hinv : Inv P x c')
    (hs : step (normalize P) c' = some e') : Inv P x e' := by
  obtain ⟨c, hc, hcase⟩ := hinv
  have land : ∀ d : Config r, Reach P (init r x) d → e' = emb P.length d → Inv P x e' := by
    intro d hd he
    refine ⟨d, hd, ?_⟩
    by_cases hlt : d.pc < P.length
    · exact Or.inl ⟨by rw [he]; simpa [emb, fold_of_lt hlt] using hlt,
        by rw [he]; cases d; simp [emb, fold_of_lt hlt]⟩
    · exact Or.inr (Or.inl ⟨by rw [he]; simp [emb, fold_of_ge hlt], by omega⟩)
  rcases hcase with ⟨hlt, rfl⟩ | ⟨hpc, hge⟩ | ⟨h1, h2, hpc, hreg⟩ | ⟨hpc, hstop, hreg⟩
  · obtain ⟨cmd, hcmd⟩ := Option.isSome_iff_exists.1 (by
      rw [List.getElem?_eq_getElem hlt]; rfl : (P[c.pc]?).isSome)
    have hnew : (normalize P)[c.pc]? = some (normCmd P.length c.pc cmd) := by
      rw [normalize_orig P hlt, hcmd]; rfl
    rw [step_of_get hnew] at hs
    have hs1 := fold_succ hlt
    have orig : ∀ d, cmd.exec c.pc c.regs = some d → Reach P (init r x) d := fun d hd =>
      hc.tail (by rw [step_of_get hcmd]; exact hd)
    cases cmd with
    | goto k =>
      simp only [normCmd, Cmd.exec, Option.some.injEq] at hs; subst hs
      exact land ⟨k, c.regs⟩ (orig _ rfl) rfl
    | ifLt a b k =>
      have ho := orig _ rfl
      by_cases h1 : fold P.length k = c.pc
      · by_cases hcond : a.val c.regs < b.val c.regs
        · simp [normCmd, normCond, h1, Cmd.exec, hcond] at hs; subst hs
          exact ⟨c, hc, Or.inr (Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, rfl⟩))⟩
        · simp [normCmd, normCond, h1, Cmd.exec, hcond] at hs; subst hs
          exact land _ ho (by simp [emb, hcond, hs1])
      · by_cases h2 : fold P.length k = c.pc + 1
        · simp [normCmd, normCond, h2, Cmd.exec] at hs; subst hs
          exact land _ ho (by
            by_cases hcond : a.val c.regs < b.val c.regs <;> simp [emb, hcond, h2, hs1])
        · by_cases hcond : a.val c.regs < b.val c.regs
          · simp [normCmd, normCond, h1, h2, Cmd.exec, hcond] at hs; subst hs
            exact land _ ho (by simp [emb, hcond])
          · simp [normCmd, normCond, h1, h2, Cmd.exec, hcond] at hs; subst hs
            exact land _ ho (by simp [emb, hcond, hs1])
    | ifLe a b k =>
      have ho := orig _ rfl
      by_cases h1 : fold P.length k = c.pc
      · by_cases hcond : a.val c.regs ≤ b.val c.regs
        · simp [normCmd, normCond, h1, Cmd.exec, hcond] at hs; subst hs
          exact ⟨c, hc, Or.inr (Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, rfl⟩))⟩
        · simp [normCmd, normCond, h1, Cmd.exec, hcond] at hs; subst hs
          exact land _ ho (by simp [emb, hcond, hs1])
      · by_cases h2 : fold P.length k = c.pc + 1
        · simp [normCmd, normCond, h2, Cmd.exec] at hs; subst hs
          exact land _ ho (by
            by_cases hcond : a.val c.regs ≤ b.val c.regs <;> simp [emb, hcond, h2, hs1])
        · by_cases hcond : a.val c.regs ≤ b.val c.regs
          · simp [normCmd, normCond, h1, h2, Cmd.exec, hcond] at hs; subst hs
            exact land _ ho (by simp [emb, hcond])
          · simp [normCmd, normCond, h1, h2, Cmd.exec, hcond] at hs; subst hs
            exact land _ ho (by simp [emb, hcond, hs1])
    | arith δ =>
      have hs' : (Cmd.arith δ : Cmd r).exec c.pc c.regs = some e' := hs
      refine land _ (orig _ hs') ?_
      simp only [Cmd.exec] at hs'
      split_ifs at hs'
      cases hs'
      simp [emb, hs1]
    | stop =>
      simp only [normCmd, Cmd.exec, Option.some.injEq] at hs; subst hs
      exact ⟨c, hc, Or.inr (Or.inr (Or.inr ⟨rfl, hcmd, rfl⟩))⟩
  · have hline : (normalize P)[c'.pc]? = some (Cmd.goto P.length) := by
      rw [hpc]; exact normalize_dead P
    rw [step_of_get hline] at hs
    simp only [Cmd.exec, Option.some.injEq] at hs; subst hs
    exact ⟨c, hc, Or.inr (Or.inl ⟨rfl, hge⟩)⟩
  · have hline : (normalize P)[c'.pc]? = some (Cmd.goto c.pc) := by
      have := normalize_tramp P (i := c.pc) (by omega)
      rwa [show P.length + 1 + c.pc = c'.pc by omega] at this
    rw [step_of_get hline] at hs
    simp only [Cmd.exec, Option.some.injEq] at hs; subst hs
    exact ⟨c, hc, Or.inl ⟨by simp; omega, by cases c; simp_all⟩⟩
  · have hline : (normalize P)[c'.pc]? = some Cmd.stop := by rw [hpc]; exact normalize_stop P
    rw [step_of_get hline] at hs
    simp [Cmd.exec] at hs

/-- **Normalization preserves acceptance.** -/
theorem accepts_normalize_iff (P : Program r) (x : ℕ) :
    Accepts (normalize P) x ↔ AcceptsStop P x := by
  have hfin : final (normalize P) = ⟨2 * P.length + 1, fun _ => 0⟩ := by
    simp [final, normalize_length]
  constructor
  · rintro ⟨s, hs⟩
    have hinv := Reach.ind (P := normalize P) (Inv P x) ⟨init r x, Reach.refl _ _, by
        by_cases h0 : 0 < P.length
        · exact Or.inl ⟨by simp only [init]; omega, rfl⟩
        · exact Or.inr (Or.inl ⟨by simp only [init]; omega, by simp only [init]; omega⟩)⟩
      (fun d e _ hd he => inv_step P x hd he) _ ⟨s, hs⟩
    rw [hfin] at hinv
    obtain ⟨c, ⟨t, ht⟩, hcase⟩ := hinv
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, hstop, hreg⟩
    · simp at h; omega
    · simp at h; omega
    · simp at h
    · exact ⟨t, c, ht, hstop, hreg⟩
  · rintro ⟨s, c, hs, hstop, hreg⟩
    have hfwd := Reach.ind (P := P) (fun d => Reach (normalize P) (init r x) (emb P.length d))
      (by
        have : emb P.length (init r x) = init r x := by
          simp only [emb, init]; congr; unfold fold; split_ifs <;> omega
        rw [this]; exact Reach.refl _ _)
      (fun d e _ hd he => hd.trans (forward_step P he)) c ⟨s, hs⟩
    have hlt : c.pc < P.length := (List.getElem?_eq_some_iff.1 hstop).1
    have hc : emb P.length c = c := by cases c; simp [emb, fold_of_lt hlt]
    rw [hc] at hfwd
    have hfinal := hfwd.tail (e := final (normalize P)) (by
      rw [step_of_get (show (normalize P)[c.pc]? = some (Cmd.goto (2 * P.length + 1)) by
        rw [normalize_orig P hlt, hstop]; rfl), hfin]
      simp [Cmd.exec, hreg])
    exact hfinal

/-- **§3 for raw programs**: a raw program accepts `x` iff the system (24)–(39) of its
normalized form is solvable. -/
theorem acceptsStop_iff (P : Program r) (hP : RawOk P) (x : ℕ) :
    AcceptsStop P x ↔ ∃ s Q I R L, Sys (normalize P) x s Q I R L := by
  rw [← accepts_normalize_iff, accepts_iff _ (normalize_wf P hP)]

end RM
end JM1984
