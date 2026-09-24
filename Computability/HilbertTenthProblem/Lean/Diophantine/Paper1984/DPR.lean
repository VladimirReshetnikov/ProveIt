import Diophantine.Paper1984.ExpSys
import Diophantine.Paper1980.Universal100

/-!
# Jones–Matijasevič 1984: every recursively enumerable set is singlefold unary exponential
Diophantine

The paper's main theorem (the Davis–Putnam–Robinson theorem in its strengthened, singlefold
unary form, via register machines):

* `ofCounter`: a three-counter program (Minsky's machines, the input format of §3) becomes a
  raw register machine program, three lines per instruction; `acceptsStop_ofCounter` shows it
  accepts exactly the inputs the counter program accepts;
* `acceptsStop_sfu`: through `normalize` and `accepts_sfu`, acceptance by any raw program is
  singlefold unary exponential Diophantine;
* `re_sfu`: for every recursively enumerable set, using the compilation of Turing machines into
  counter programs (`TMUniv.re_tm0`, `TMCounter.accepts_iff`);
* `re_single_equation`, `re_exp_diophantine`: the representation as one equation `R = S`, with
  `R, S` built from the input, the unknowns and constants by `+`, `·` and `2^·` (hence by `+`,
  `·` and exponentiation, the paper's (1)), singlefold.
-/

namespace JM1984
namespace RM

open Jones1980 Exp

/-- The signed unit update of one register. -/
def unit (j : Fin 3) (d : ℤ) : Fin 3 → ℤ := fun i => if i = j then d else 0

/-- The three register-machine lines of a counter instruction at location `ℓ`. -/
def counterLines (ℓ : ℕ) : CInstr → List (Cmd 3)
  | .inc j nx => [.arith (unit j 1), .goto (3 * nx), .goto (3 * nx)]
  | .test j z nz => [.ifLe (.reg j) .zero (3 * z), .arith (unit j (-1)), .goto (3 * nz)]
  | .accept => [.stop, .stop, .stop]
  | .stop => [.goto (3 * ℓ), .goto (3 * ℓ), .goto (3 * ℓ)]

/-- The register machine of a three-counter program. -/
def ofCounter (M : CProgram) : Program 3 :=
  (List.range M.len).flatMap (fun ℓ => counterLines ℓ (M.code ℓ))

theorem counterLines_length (ℓ : ℕ) (c : CInstr) : (counterLines ℓ c).length = 3 := by
  cases c <;> rfl

theorem flatMap_three_length (f : ℕ → List (Cmd 3)) (hf : ∀ ℓ, (f ℓ).length = 3) (n : ℕ) :
    ((List.range n).flatMap f).length = 3 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hf]; ring

theorem flatMap_three_get (f : ℕ → List (Cmd 3)) (hf : ∀ ℓ, (f ℓ).length = 3) (n : ℕ) {ℓ o : ℕ}
    (hℓ : ℓ < n) (ho : o < 3) : ((List.range n).flatMap f)[3 * ℓ + o]? = (f ℓ)[o]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge ℓ n with h | h
    · rw [List.getElem?_append_left (by rw [flatMap_three_length f hf]; omega), ih h]
    · have : ℓ = n := by omega
      subst this
      rw [List.getElem?_append_right (by rw [flatMap_three_length f hf]; omega),
        flatMap_three_length f hf]
      simp

theorem ofCounter_length (M : CProgram) : (ofCounter M).length = 3 * M.len :=
  flatMap_three_length _ (fun ℓ => counterLines_length ℓ _) _

theorem ofCounter_get (M : CProgram) {ℓ o : ℕ} (hℓ : ℓ < M.len) (ho : o < 3) :
    (ofCounter M)[3 * ℓ + o]? = (counterLines ℓ (M.code ℓ))[o]? :=
  flatMap_three_get _ (fun ℓ => counterLines_length ℓ _) _ hℓ ho

theorem ofCounter_get_none (M : CProgram) {pc : ℕ} (h : 3 * M.len ≤ pc) :
    (ofCounter M)[pc]? = none := by
  rw [List.getElem?_eq_none]; rw [ofCounter_length]; exact h

theorem rawOk_ofCounter (M : CProgram) : RawOk (ofCounter M) := by
  intro i δ hi j
  have hlt : i < 3 * M.len := by
    rw [← ofCounter_length]; exact (List.getElem?_eq_some_iff.1 hi).1
  rw [show i = 3 * (i / 3) + i % 3 by omega, ofCounter_get M (by omega) (by omega)] at hi
  have ho : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  cases hc : M.code (i / 3) <;> rw [hc] at hi <;>
    rcases ho with ho | ho | ho <;> rw [ho] at hi <;> simp [counterLines] at hi <;>
    (subst hi; simp only [unit]; split_ifs <;> omega)

section sim

variable (M : CProgram) (x : ℕ)

theorem start_eq : CProgram.start x = (init 3 x).regs := by
  funext i
  simp only [CProgram.start, init]
  congr 1
  exact propext ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩

theorem update_unit (v : Fin 3 → ℕ) (j : Fin 3) (d : ℤ) (h : 0 ≤ (v j : ℤ) + d) :
    (fun i => ((v i : ℤ) + unit j d i).toNat) = Function.update v j ((v j : ℤ) + d).toNat := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [unit]
  · simp [unit, hi]

theorem get_line (M : CProgram) {ℓ o : ℕ} (hℓ : ℓ < M.len) (ho : o < 3) {c : Cmd 3}
    (h : (counterLines ℓ (M.code ℓ))[o]? = some c) :
    (ofCounter M)[3 * ℓ + o]? = some c := by
  rw [ofCounter_get M hℓ ho, h]

/-- Forward simulation of a counter step. -/
theorem forward_counter {a b : ℕ × (Fin 3 → ℕ)} (h : M.Step a b) :
    Reach (ofCounter M) ⟨3 * a.1, a.2⟩ ⟨3 * b.1, b.2⟩ := by
  cases h with
  | inc hℓ hc =>
    rename_i ℓ j nx v
    have l0 := get_line M (o := 0) hℓ (by norm_num) (by rw [hc]; rfl)
    have l1 := get_line M (o := 1) hℓ (by norm_num) (by rw [hc]; rfl)
    refine ((Reach.refl _ _).tail (e := ⟨3 * ℓ + 1, Function.update v j (v j + 1)⟩) ?_).tail ?_
    · rw [step_of_get (c := ⟨3 * ℓ, v⟩) (by simpa using l0)]
      simp only [Cmd.exec]
      rw [if_pos (fun i => by by_cases h : i = j <;> simp [unit, h] <;> omega)]
      rw [update_unit v j 1 (by omega)]
      simp
    · rw [step_of_get (c := ⟨3 * ℓ + 1, _⟩) l1]
      rfl
  | zero hℓ hc hv =>
    rename_i ℓ j z nz v
    have l0 := get_line M (o := 0) hℓ (by norm_num) (by rw [hc]; rfl)
    refine (Reach.refl _ _).tail ?_
    rw [step_of_get (c := ⟨3 * ℓ, v⟩) (by simpa using l0)]
    simp [Cmd.exec, Operand.val, hv]
  | dec hℓ hc hv =>
    rename_i ℓ j z nz v
    have l0 := get_line M (o := 0) hℓ (by norm_num) (by rw [hc]; rfl)
    have l1 := get_line M (o := 1) hℓ (by norm_num) (by rw [hc]; rfl)
    have l2 := get_line M (o := 2) hℓ (by norm_num) (by rw [hc]; rfl)
    refine (((Reach.refl _ _).tail (e := ⟨3 * ℓ + 1, v⟩) ?_).tail
      (e := ⟨3 * ℓ + 2, Function.update v j (v j - 1)⟩) ?_).tail ?_
    · rw [step_of_get (c := ⟨3 * ℓ, v⟩) (by simpa using l0)]
      simp [Cmd.exec, Operand.val]
      omega
    · rw [step_of_get (c := ⟨3 * ℓ + 1, v⟩) l1]
      simp only [Cmd.exec]
      rw [if_pos (fun i => by by_cases h : i = j <;> simp [unit, h] <;> omega)]
      rw [update_unit v j (-1) (by omega)]
      simp only [Option.some.injEq, Config.mk.injEq, true_and]
      congr 1; omega
    · rw [step_of_get (c := ⟨3 * ℓ + 2, _⟩) l2]
      rfl

/-- The backward invariant. -/
def CInv (c : Config 3) : Prop :=
  c.pc < 3 * M.len →
    match M.code (c.pc / 3) with
    | .inc _ nx => (c.pc % 3 = 0 ∧ Relation.ReflTransGen M.Step (0, CProgram.start x) (c.pc / 3, c.regs)) ∨
        (c.pc % 3 ≠ 0 ∧ Relation.ReflTransGen M.Step (0, CProgram.start x) (nx, c.regs))
    | .test j _ nz => (c.pc % 3 = 0 ∧ Relation.ReflTransGen M.Step (0, CProgram.start x) (c.pc / 3, c.regs)) ∨
        (c.pc % 3 = 1 ∧ c.regs j ≠ 0 ∧
          Relation.ReflTransGen M.Step (0, CProgram.start x) (c.pc / 3, c.regs)) ∨
        (c.pc % 3 = 2 ∧ Relation.ReflTransGen M.Step (0, CProgram.start x) (nz, c.regs))
    | _ => Relation.ReflTransGen M.Step (0, CProgram.start x) (c.pc / 3, c.regs)


theorem cinv_zero {k : ℕ} {v : Fin 3 → ℕ}
    (h : Relation.ReflTransGen M.Step (0, CProgram.start x) (k, v)) : CInv M x ⟨3 * k, v⟩ := by
  intro _
  have e1 : 3 * k / 3 = k := by omega
  have e2 : 3 * k % 3 = 0 := by omega
  simp only [e1, e2]
  cases M.code k with
  | inc j nx => exact Or.inl ⟨by trivial, h⟩
  | test j z nz => exact Or.inl ⟨by trivial, h⟩
  | accept => exact h
  | stop => exact h

theorem inv_counter_step {c e : Config 3} (hinv : CInv M x c)
    (hs : step (ofCounter M) c = some e) : CInv M x e := by
  have hlt : c.pc < 3 * M.len := by
    have := (pc_lt_of_step hs).1; rwa [ofCounter_length] at this
  obtain ⟨pc, v⟩ := c
  simp only at hlt
  set ℓ := pc / 3 with hℓdef
  have hℓ : ℓ < M.len := by omega
  have hpc : pc = 3 * ℓ + pc % 3 := by omega
  have hinv' := hinv hlt
  simp only at hinv'
  have hget := ofCounter_get M hℓ (o := pc % 3) (by omega)
  rw [← hpc] at hget
  rw [step_of_get (c := ⟨pc, v⟩) (cmd := ((counterLines ℓ (M.code ℓ))[pc % 3]'(by
    rw [counterLines_length]; omega))) (by rw [hget, List.getElem?_eq_getElem])] at hs
  have ho : pc % 3 = 0 ∨ pc % 3 = 1 ∨ pc % 3 = 2 := by omega
  cases hcode : M.code ℓ with
  | inc j nx =>
    rw [hcode] at hinv'
    simp only [hcode] at hs
    rcases ho with ho | ho | ho
    · simp only [ho] at hs
      obtain ⟨-, hr⟩ := hinv'.resolve_right (by omega)
      simp only [counterLines, List.getElem_cons_zero, Cmd.exec] at hs
      rw [if_pos (fun i => by by_cases h : i = j <;> simp [unit, h] <;> omega)] at hs
      cases hs
      rw [update_unit v j 1 (by omega)]
      intro _
      have e1 : (pc + 1) / 3 = ℓ := by omega
      have e2 : (pc + 1) % 3 = 1 := by omega
      simp only [e1, e2, hcode]
      exact Or.inr ⟨by norm_num, hr.tail (CProgram.Step.inc hℓ hcode)⟩
    · simp only [ho] at hs
      obtain ⟨-, hr⟩ := hinv'.resolve_left (by omega)
      simp only [counterLines, List.getElem_cons_succ, List.getElem_cons_zero, Cmd.exec] at hs
      cases hs
      exact cinv_zero M x (by simpa using hr)
    · simp only [ho] at hs
      obtain ⟨-, hr⟩ := hinv'.resolve_left (by omega)
      simp only [counterLines, List.getElem_cons_succ, List.getElem_cons_zero, Cmd.exec] at hs
      cases hs
      exact cinv_zero M x (by simpa using hr)
  | test j z nz =>
    rw [hcode] at hinv'
    simp only [hcode] at hs
    rcases ho with ho | ho | ho
    · simp only [ho] at hs
      obtain ⟨-, hr⟩ := hinv'.resolve_right (by omega)
      simp only [counterLines, List.getElem_cons_zero, Cmd.exec, Operand.val] at hs
      by_cases hv : v j ≤ 0
      · rw [if_pos hv] at hs
        cases hs
        exact cinv_zero M x (hr.tail (CProgram.Step.zero hℓ hcode (by omega)))
      · rw [if_neg hv] at hs
        cases hs
        intro _
        have e1 : (pc + 1) / 3 = ℓ := by omega
        have e2 : (pc + 1) % 3 = 1 := by omega
        simp only [e1, e2, hcode]
        exact Or.inr (Or.inl ⟨by trivial, by omega, hr⟩)
    · simp only [ho] at hs
      obtain ⟨-, hv, hr⟩ := (hinv'.resolve_left (by omega)).resolve_right (by omega)
      simp only [counterLines, List.getElem_cons_succ, List.getElem_cons_zero, Cmd.exec] at hs
      rw [if_pos (fun i => by by_cases h : i = j <;> simp [unit, h] <;> omega)] at hs
      cases hs
      rw [update_unit v j (-1) (by omega)]
      intro _
      have e1 : (pc + 1) / 3 = ℓ := by omega
      have e2 : (pc + 1) % 3 = 2 := by omega
      simp only [e1, e2, hcode]
      refine Or.inr (Or.inr ⟨by trivial, ?_⟩)
      have := hr.tail (CProgram.Step.dec hℓ hcode hv)
      have hu : ((v j : ℤ) + -1).toNat = v j - 1 := by omega
      rw [hu]; exact this
    · simp only [ho] at hs
      obtain ⟨-, hr⟩ := (hinv'.resolve_left (by omega)).resolve_left (by omega)
      simp only [counterLines, List.getElem_cons_succ, List.getElem_cons_zero, Cmd.exec] at hs
      cases hs
      exact cinv_zero M x (by simpa using hr)
  | accept =>
    simp only [hcode] at hs
    rcases ho with ho | ho | ho <;> simp [ho, counterLines, Cmd.exec] at hs
  | stop =>
    rw [hcode] at hinv'
    simp only [hcode] at hs
    rcases ho with ho | ho | ho <;> simp only [ho, counterLines, Cmd.exec] at hs <;>
      (cases hs; exact cinv_zero M x (by simpa using hinv'))

/-- **The register machine of a counter program accepts the same inputs.** -/
theorem acceptsStop_ofCounter : AcceptsStop (ofCounter M) x ↔ M.Accepts x := by
  constructor
  · rintro ⟨s, c, hs, hstop, hreg⟩
    have hinv := Reach.ind (P := ofCounter M) (CInv M x)
      (by
        have : init 3 x = ⟨3 * 0, CProgram.start x⟩ := by rw [start_eq]; rfl
        rw [this]; exact cinv_zero M x Relation.ReflTransGen.refl)
      (fun d e _ hd he => inv_counter_step M x hd he) c ⟨s, hs⟩
    have hlt : c.pc < 3 * M.len := by
      rw [← ofCounter_length]; exact (List.getElem?_eq_some_iff.1 hstop).1
    have hℓ : c.pc / 3 < M.len := by omega
    have hget := ofCounter_get M hℓ (o := c.pc % 3) (by omega)
    rw [show 3 * (c.pc / 3) + c.pc % 3 = c.pc by omega, hstop] at hget
    have hinv' := hinv hlt
    have ho : c.pc % 3 = 0 ∨ c.pc % 3 = 1 ∨ c.pc % 3 = 2 := by omega
    cases hcode : M.code (c.pc / 3) with
    | inc j nx => rw [hcode] at hget; rcases ho with ho | ho | ho <;> simp [ho, counterLines] at hget
    | test j z nz => rw [hcode] at hget; rcases ho with ho | ho | ho <;> simp [ho, counterLines] at hget
    | stop => rw [hcode] at hget; rcases ho with ho | ho | ho <;> simp [ho, counterLines] at hget
    | accept =>
      rw [hcode] at hinv'
      refine ⟨c.pc / 3, hℓ, hcode, ?_⟩
      rw [← hreg]; exact hinv'
  · rintro ⟨ℓ, hℓ, hc, hr⟩
    have hfwd : ∀ b, Relation.ReflTransGen M.Step (0, CProgram.start x) b →
        Reach (ofCounter M) (init 3 x) ⟨3 * b.1, b.2⟩ := by
      intro b hb
      induction hb with
      | refl => rw [show (3 * 0 : ℕ) = 0 from rfl, start_eq]; exact Reach.refl _ _
      | tail _ hs ih => exact ih.trans (forward_counter M hs)
    obtain ⟨s, hs⟩ := hfwd _ hr
    refine ⟨s, _, hs, ?_, rfl⟩
    have := ofCounter_get M hℓ (o := 0) (by norm_num)
    simpa [hc, counterLines] using this

end sim

/-- Acceptance by a raw program is singlefold unary exponential Diophantine. -/
theorem acceptsStop_sfu {r : ℕ} (P : Program r) (hP : RawOk P) :
    Exp.SFU (fun a : Unit → ℕ => AcceptsStop P (a ())) :=
  (accepts_sfu (normalize P) (normalize_wf P hP)).congr (fun _ => accepts_normalize_iff P _)

/-- **Jones–Matijasevič 1984: every recursively enumerable set is singlefold unary exponential
Diophantine.** -/
theorem re_sfu {S : Set ℕ} (hS : REPred S) : Exp.SFU (fun a : Unit → ℕ => a () ∈ S) := by
  obtain ⟨Γ, Λ, iΓ, fΓ, iΛ, fΛ, TM, enc, pre, hM⟩ := TMUniv.re_tm0 hS
  let M := TMCounter.prog TM enc pre
  refine (acceptsStop_sfu (ofCounter M) (rawOk_ofCounter M)).congr (fun a => ?_)
  rw [acceptsStop_ofCounter, TMCounter.accepts_iff, ← hM]

/-- **The single equation**: for every recursively enumerable set `S` there are unary
exponential terms `R, S'` in the input and `m` unknowns with `x ∈ S ↔ ∃ y, R = S'`, the `y`
being unique. -/
theorem re_single_equation {S : Set ℕ} (hS : REPred S) :
    ∃ (m : ℕ) (L R : UTerm (Unit ⊕ Fin m)), ∀ x : ℕ,
      (x ∈ S ↔ ∃ y, L.eval (join (fun _ => x) y) = R.eval (join (fun _ => x) y)) ∧
      ∀ y z, L.eval (join (fun _ => x) y) = R.eval (join (fun _ => x) y) →
        L.eval (join (fun _ => x) z) = R.eval (join (fun _ => x) z) → y = z := by
  obtain ⟨m, L, R, h⟩ := (re_sfu hS).single_equation
  exact ⟨m, L, R, fun x => h (fun _ => x)⟩

/-- **The Davis–Putnam–Robinson theorem**, in the form (1): every recursively enumerable set is
exponential Diophantine (and the representation is singlefold). -/
theorem re_exp_diophantine {S : Set ℕ} (hS : REPred S) :
    ∃ (m : ℕ) (L R : ETerm (Unit ⊕ Fin m)), ∀ x : ℕ,
      (x ∈ S ↔ ∃ y, L.eval (join (fun _ => x) y) = R.eval (join (fun _ => x) y)) ∧
      ∀ y z, L.eval (join (fun _ => x) y) = R.eval (join (fun _ => x) y) →
        L.eval (join (fun _ => x) z) = R.eval (join (fun _ => x) z) → y = z := by
  obtain ⟨m, L, R, h⟩ := re_single_equation hS
  exact ⟨m, L.toE, R.toE, fun x => by simpa only [ETerm.eval_toE] using h x⟩

end RM
end JM1984
