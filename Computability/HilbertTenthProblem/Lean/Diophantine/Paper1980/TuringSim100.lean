import Diophantine.Paper1980.TuringCounter100

/-!
# The simulating program is correct

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §3: *"The routines of Section 1 preserve
the other stack and restore C=0 at every call boundary.  Consequently each simulated Turing
step terminates after finitely many counter instructions and has exactly the intended tape
effect. ...  If the Turing machine runs forever, its faithful simulation never reaches
acceptance."*

`Dsp c p` says that the program configuration `p` sits at the dispatch block of the state of
`c` and a digit whose symbol is the scanned one, with `A` and `B` representing the left and
right halves of the tape and `C = 0`.  `step_sim` shows that one machine step is followed by
at least one program step to a dispatch configuration of the next machine configuration, and
`halt_sim` that a halting configuration leads to the accepting halt with empty registers.
Mathlib's `StateTransition.Respects` then transfers termination both ways (`accepts_iff`).
-/

namespace Jones1980

open Turing TMStack StateTransition

namespace TMCounter

variable {Γ Λ : Type} [Inhabited Γ] [Fintype Γ] [Inhabited Λ] [Fintype Λ]
variable (TM : TM0.Machine Γ Λ) (enc : Bool → Γ) (pre : List Γ)

theorem CProgram.Placed.shift {M : CProgram} {ℓ size k size' : ℕ} {f g : ℕ → CInstr}
    (h : M.Placed ℓ size f) (hk : k + size' ≤ size) (hg : ∀ o, o < size' → f (k + o) = g o) :
    M.Placed (ℓ + k) size' g := fun o ho => by
  have := h (k + o) (by omega)
  rw [Nat.add_assoc, ← hg o ho]
  exact this

theorem transGen_of_ne {M : CProgram} {a b : ℕ × (Fin 3 → ℕ)} (h : M.Reach a b) (hne : a.1 ≠ b.1) :
    Relation.TransGen M.Step a b := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hac, hcb⟩
  · exact absurd (by rw [h]) hne
  · exact Relation.TransGen.head' hac hcb

/-! ### The blocks -/

theorem base_le_S : 3 * base Γ + 1 ≤ S Γ := by unfold S; omega

theorem nBlocks_gt {i : ℕ} (hi : i < 4) : i < nBlocks Γ Λ := by unfold nBlocks; omega

theorem loop_lt (q : Λ) : 4 + qi q < nBlocks Γ Λ := by
  have := qi_lt q; unfold nBlocks; omega

theorem disp_bounds (q : Λ) {j : ℕ} (hj : j < base Γ) :
    4 + nQ Λ ≤ dispId Γ (Λ := Λ) (qi q) j ∧ dispId Γ (Λ := Λ) (qi q) j < 4 + nQ Λ + nQ Λ * base Γ := by
  have := qi_lt q
  have h : (qi q + 1) * base Γ ≤ nQ Λ * base Γ := Nat.mul_le_mul_right _ this
  unfold dispId
  constructor
  · omega
  · rw [Nat.add_mul, one_mul] at h; omega

theorem left_bounds (q : Λ) {j j' : ℕ} (hj : j < base Γ) (hj' : j' < base Γ) :
    4 + nQ Λ + nQ Λ * base Γ ≤ leftId Γ Λ (qi q) j j' ∧ leftId Γ Λ (qi q) j j' < nBlocks Γ Λ := by
  have := qi_lt q
  have h1 : (qi q + 1) * base Γ ≤ nQ Λ * base Γ := Nat.mul_le_mul_right _ this
  have h2 : (qi q * base Γ + j + 1) * base Γ ≤ nQ Λ * base Γ * base Γ :=
    Nat.mul_le_mul_right _ (by rw [Nat.add_mul, one_mul] at h1; omega)
  unfold leftId nBlocks
  constructor
  · omega
  · rw [Nat.add_mul, one_mul] at h2; omega

theorem block_loop (q : Λ) (o : ℕ) :
    blockCode TM enc pre (4 + qi q) o = CProgram.popM 1 2 (base Γ) (S Γ * (4 + qi q))
      (fun j => S Γ * dispId Γ (Λ := Λ) (qi q) j) o := by
  have := qi_lt q
  unfold blockCode
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by unfold nQ at *; omega),
    Nat.add_sub_cancel_left]

theorem block_disp (q : Λ) {j : ℕ} (hj : j < base Γ) (o : ℕ) :
    blockCode TM enc pre (dispId Γ (Λ := Λ) (qi q) j) o = dispCode TM q j (S Γ * dispId Γ (Λ := Λ) (qi q) j) o := by
  have hb := base_pos (Γ := Γ)
  obtain ⟨h1, h2⟩ := disp_bounds (Γ := Γ) q hj
  obtain ⟨hd, hm⟩ := div_mod_id (i := qi q) hb hj
  unfold blockCode
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2,
    show dispId Γ (Λ := Λ) (qi q) j - 4 - nQ Λ = qi q * base Γ + j by unfold dispId; omega, hd, hm, qs_qi]

theorem block_left (q : Λ) {j j' : ℕ} (hj : j < base Γ) (hj' : j' < base Γ) (o : ℕ) :
    blockCode TM enc pre (leftId Γ Λ (qi q) j j') o
      = leftCode TM q j j' (S Γ * leftId Γ Λ (qi q) j j') o := by
  have hb := base_pos (Γ := Γ)
  obtain ⟨h1, h2⟩ := left_bounds (Γ := Γ) q hj hj'
  obtain ⟨hd, hm⟩ := div_mod_id (i := qi q * base Γ + j) hb hj'
  obtain ⟨hd', hm'⟩ := div_mod_id (i := qi q) hb hj
  unfold blockCode
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos h2, show leftId Γ Λ (qi q) j j' - 4 - nQ Λ - nQ Λ * base Γ
      = (qi q * base Γ + j) * base Γ + j' by unfold leftId; omega, hd, hm, hd', hm', qs_qi]

/-! ### The loader, the loop and the cleanup -/

theorem load_spec : ∀ a n, Good Γ n →
    (prog TM enc pre).Reach (0, ![a, n, 0]) (startAddr (Λ := Λ) pre, ![0, TMStack.loadB enc a n, 0]) := by
  have hb2 := two_le_base Γ
  have hS := base_le_S (Γ := Γ)
  have hP0 : (prog TM enc pre).Placed (S Γ * 0) 9 (blockCode TM enc pre 0) :=
    placed TM enc pre (lt_of_lt_of_le (nBlocks_gt (by norm_num)) (Nat.le_add_right _ _)) (by unfold S; omega) (fun _ _ => rfl)
  rw [Nat.mul_zero] at hP0
  have c0 := hP0.get (prog TM enc pre) (o := 0) (by norm_num)
  have c1 := hP0.get (prog TM enc pre) (o := 1) (by norm_num)
  simp only [Nat.add_zero, blockCode, if_true, one_ne_zero, if_false, zero_add] at c0 c1
  have hpop : (prog TM enc pre).Placed 2 7 (CProgram.popM 0 2 2 2 (fun j => S Γ * (1 + j))) := by
    have := CProgram.Placed.shift (k := 2) (size' := 7)
      (g := CProgram.popM 0 2 2 2 (fun j => S Γ * (1 + j))) hP0 (by norm_num) (fun o _ => by
      simp only [blockCode, if_true, show 2 + o ≠ 0 by omega, show 2 + o ≠ 1 by omega, if_false,
        show 2 + o - 2 = o by omega])
    simpa using this
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro n hn
    by_cases ha : a = 0
    · subst ha
      rw [TMStack.loadB, dif_pos rfl]
      exact Relation.ReflTransGen.single (CProgram.Step.zero c0.1 c0.2 (by simp))
    · rw [TMStack.loadB, dif_neg ha]
      have s1 := CProgram.Step.dec (v := ![a, n, 0]) c0.1 c0.2 (by simpa using ha)
      have s2 := CProgram.Step.inc (v := Function.update ![a, n, 0] 0 (![a, n, 0] 0 - 1)) c1.1 c1.2
      have e2 : Function.update (Function.update ![a, n, 0] 0 (![a, n, 0] 0 - 1)) 0
          (Function.update ![a, n, 0] 0 (![a, n, 0] 0 - 1) 0 + 1) = ![a, n, 0] := by
        apply reg_ext <;> simp; omega
      rw [e2] at s2
      obtain ⟨w, hw, hw0, hw2, hwi⟩ := CProgram.pop_spec (prog TM enc pre) (by decide) (k := 2)
        (by norm_num) hpop ![a, n, 0] (by simp)
      have hw1 : w 1 = n := by rw [hwi 1 (by decide) (by decide)]; simp
      simp only [Matrix.cons_val_zero] at hw0
      rw [reg_ext hw0 hw1 hw2] at hw
      -- the bit push
      have hi : 1 + a % 2 < nBlocks Γ Λ := nBlocks_gt (by omega)
      have hcode := code_lt (enc (decide (a % 2 = 1)))
      have hpush : (prog TM enc pre).Placed (S Γ * (1 + a % 2)) (base Γ + 3 + code (enc (decide (a % 2 = 1))))
          (CProgram.pushM 1 2 (base Γ) (code (enc (decide (a % 2 = 1)))) (S Γ * (1 + a % 2)) 0) :=
        placed TM enc pre (lt_of_lt_of_le hi (Nat.le_add_right _ _)) (by omega) (fun o _ => by
          unfold blockCode
          rw [if_neg (by omega), if_pos (by omega), show 1 + a % 2 - 1 = a % 2 by omega])
      obtain ⟨u, hu, hu1, hu2, hui⟩ := CProgram.push_spec (prog TM enc pre) (by decide) (by omega)
        (code_pos _) hpush ![a / 2, n, 0] (by simp)
      have hu0 : u 0 = a / 2 := by rw [hui 0 (by decide) (by decide)]; simp
      simp only [Matrix.cons_val_one, Matrix.head_cons] at hu1
      rw [reg_ext hu0 hu1 hu2] at hu
      have hrest := ih (a / 2) (by omega) (base Γ * n + code (enc (decide (a % 2 = 1))))
        (good_push hn (code_pos _) (code_lt _))
      exact (Relation.ReflTransGen.single s1).trans ((Relation.ReflTransGen.single s2).trans
        (hw.trans (hu.trans hrest)))

theorem loop_spec (q : Λ) (nA nB : ℕ) :
    (prog TM enc pre).Reach (S Γ * (4 + qi q), ![nA, nB, 0])
      (S Γ * dispId Γ (Λ := Λ) (qi q) (nB % base Γ), ![nA, nB / base Γ, 0]) := by
  have hP : (prog TM enc pre).Placed (S Γ * (4 + qi q)) (3 * base Γ + 1)
      (CProgram.popM 1 2 (base Γ) (S Γ * (4 + qi q)) (fun j => S Γ * dispId Γ (Λ := Λ) (qi q) j)) :=
    placed TM enc pre (lt_of_lt_of_le (loop_lt q) (Nat.le_add_right _ _)) base_le_S (fun o _ => block_loop TM enc pre q o)
  obtain ⟨w, hw, hw1, hw2, hwi⟩ := CProgram.pop_spec (prog TM enc pre) (by decide)
    (by have := two_le_base Γ; omega) hP ![nA, nB, 0] (by simp)
  have hw0 : w 0 = nA := by rw [hwi 0 (by decide) (by decide)]; simp
  simp only [Matrix.cons_val_one, Matrix.head_cons] at hw hw1
  rw [reg_ext hw0 hw1 hw2] at hw
  exact hw

theorem clear_spec {M : CProgram} {r : Fin 3} {ℓ ℓ' : ℕ} (hℓ : ℓ < M.len)
    (hc : M.code ℓ = .test r ℓ' ℓ) :
    ∀ n (v : Fin 3 → ℕ), v r = n → M.Reach (ℓ, v) (ℓ', Function.update v r 0) := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have e : Function.update v r 0 = v := by rw [← hv]; exact Function.update_eq_self r v
    rw [e]
    exact Relation.ReflTransGen.single (CProgram.Step.zero hℓ hc hv)
  | succ n ih =>
    intro v hv
    have s1 := CProgram.Step.dec (v := v) hℓ hc (by omega)
    have h := ih (Function.update v r (v r - 1)) (by rw [Function.update_self]; omega)
    rw [Function.update_idem] at h
    exact (Relation.ReflTransGen.single s1).trans h

/-- The accepting configuration. -/
def acc : ℕ × (Fin 3 → ℕ) := (S Γ * 3 + 3, fun _ => 0)

theorem clean_code (o : ℕ) (ho : o < 4) :
    (S Γ * 3 + o < (prog TM enc pre).len) ∧ (prog TM enc pre).code (S Γ * 3 + o) = cleanCode Γ o := by
  have hP : (prog TM enc pre).Placed (S Γ * 3) 4 (cleanCode Γ) :=
    placed TM enc pre (lt_of_lt_of_le (nBlocks_gt (by norm_num)) (Nat.le_add_right _ _)) (by unfold S; omega) (fun o _ => by
      unfold blockCode; rw [if_neg (by omega), if_neg (by omega), if_pos rfl])
  exact hP o ho

theorem clean_spec (a b c : ℕ) :
    (prog TM enc pre).Reach (S Γ * 3, ![a, b, c]) (acc (Γ := Γ)) := by
  have c0 := clean_code TM enc pre 0 (by norm_num)
  have c1 := clean_code TM enc pre 1 (by norm_num)
  have c2 := clean_code TM enc pre 2 (by norm_num)
  simp only [Nat.add_zero, cleanCode, if_true, one_ne_zero, if_false,
    show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega] at c0 c1 c2
  have h0 := clear_spec c0.1 c0.2 a ![a, b, c] rfl
  have h1 := clear_spec c1.1 c1.2 _ (Function.update ![a, b, c] 0 0) rfl
  have h2 := clear_spec c2.1 c2.2 _ (Function.update (Function.update ![a, b, c] 0 0) 1 0) rfl
  have e : Function.update (Function.update (Function.update ![a, b, c] 0 0) 1 0) 2 0
      = fun _ => 0 := by
    funext i; fin_cases i <;> simp
  rw [e] at h2
  exact h0.trans (h1.trans h2)

/-- A dispatch configuration of a machine configuration. -/
def Dsp (c : TM0.Cfg Γ Λ) (p : ℕ × (Fin 3 → ℕ)) : Prop :=
  ∃ j nA nB, j < base Γ ∧ Good Γ nA ∧ Good Γ nB ∧ sym j = c.Tape.head ∧
    c.Tape.left = ListBlank.mk (stk nA) ∧ c.Tape.right = ListBlank.mk (stk nB) ∧
    p = (S Γ * dispId Γ (Λ := Λ) (qi c.q) j, ![nA, nB, 0])

/-- From a loop block with the tape halves on the stacks, the pop reaches a dispatch
configuration. -/
theorem loop_dsp (q : Λ) (T : Tape Γ) {nA nB : ℕ} (hA : Good Γ nA) (hB : Good Γ nB)
    (hL : T.left = ListBlank.mk (stk nA)) (hR : T.right.cons T.head = ListBlank.mk (stk nB)) :
    ∃ p, Dsp ⟨q, T⟩ p ∧ (prog TM enc pre).Reach (S Γ * (4 + qi q), ![nA, nB, 0]) p := by
  refine ⟨_, ⟨nB % base Γ, nA, nB / base Γ, Nat.mod_lt _ base_pos, hA, good_div hB, ?_, hL, ?_,
    rfl⟩, loop_spec TM enc pre q nA nB⟩
  · have := congrArg ListBlank.head hR
    rw [ListBlank.head_cons, head_stk hB] at this
    exact this.symm
  · have := congrArg ListBlank.tail hR
    rw [ListBlank.tail_cons, tail_stk] at this
    exact this

theorem loop_ne (q : Λ) {j : ℕ} (hj : j < base Γ) (q' : Λ) :
    S Γ * dispId Γ (Λ := Λ) (qi q) j ≠ S Γ * (4 + qi q') := by
  have h1 := (disp_bounds (Γ := Γ) q hj).1
  have h2 := qi_lt q'
  have : S Γ * (4 + qi q') < S Γ * dispId Γ (Λ := Λ) (qi q) j :=
    Nat.mul_lt_mul_of_pos_left (by omega) S_pos
  omega

set_option maxHeartbeats 4000000 in
/-- **One machine step.** -/
theorem step_sim {c c' : TM0.Cfg Γ Λ} {p : ℕ × (Fin 3 → ℕ)} (hD : Dsp c p)
    (hs : TM0.step TM c = some c') :
    ∃ p', Dsp c' p' ∧ Relation.TransGen (prog TM enc pre).Step p p' := by
  obtain ⟨q, ⟨h, L, R⟩⟩ := c
  obtain ⟨j, nA, nB, hj, hA, hB, hsym, hL, hR, rfl⟩ := hD
  simp only at hsym hL hR
  have hb2 := two_le_base Γ
  have hSb := base_le_S (Γ := Γ)
  unfold TM0.step at hs
  simp only at hs
  cases hM : TM q h with
  | none => rw [hM] at hs; simp at hs
  | some qa =>
    obtain ⟨q', st⟩ := qa
    rw [hM] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst hs
    have hMj : TM q (sym j) = some (q', st) := by rw [hsym]; exact hM
    have hdisp : ∀ o, blockCode TM enc pre (dispId Γ (Λ := Λ) (qi q) j) o
        = dispCode TM q j (S Γ * dispId Γ (Λ := Λ) (qi q) j) o := block_disp TM enc pre q hj
    obtain ⟨hlo, hhi⟩ := disp_bounds (Γ := Γ) q hj
    have hdl : dispId Γ (Λ := Λ) (qi q) j < nBlocks Γ Λ := by unfold nBlocks; omega
    cases st with
    | write a =>
      have hP : (prog TM enc pre).Placed (S Γ * dispId Γ (Λ := Λ) (qi q) j) (base Γ + 3 + code a)
          (CProgram.pushM 1 2 (base Γ) (code a) (S Γ * dispId Γ (Λ := Λ) (qi q) j)
            (S Γ * (4 + qi q'))) :=
        placed TM enc pre (lt_of_lt_of_le hdl (Nat.le_add_right _ _)) (by have := code_lt a; unfold S; omega) (fun o _ => by
          rw [hdisp]; unfold dispCode; rw [hMj])
      obtain ⟨w, hw, hw1, hw2, hwi⟩ := CProgram.push_spec (prog TM enc pre) (by decide) (by omega)
        (code_pos a) hP ![nA, nB, 0] (by simp)
      have hw0 : w 0 = nA := by rw [hwi 0 (by decide) (by decide)]; simp
      simp only [Matrix.cons_val_one, Matrix.head_cons] at hw1
      rw [reg_ext hw0 hw1 hw2] at hw
      obtain ⟨p', hp', hr⟩ := loop_dsp TM enc pre q' ⟨a, L, R⟩ hA
        (good_push hB (code_pos a) (code_lt a)) hL (by
          show R.cons a = _
          rw [hR, cons_stk])
      exact ⟨p', hp', Relation.TransGen.trans_left
        (transGen_of_ne hw (loop_ne q hj q')) hr⟩
    | move d =>
      cases d with
      | right =>
        have hP : (prog TM enc pre).Placed (S Γ * dispId Γ (Λ := Λ) (qi q) j)
            (base Γ + 3 + code (sym (Γ := Γ) j))
            (CProgram.pushM 0 2 (base Γ) (code (sym (Γ := Γ) j))
              (S Γ * dispId Γ (Λ := Λ) (qi q) j) (S Γ * (4 + qi q'))) :=
          placed TM enc pre (lt_of_lt_of_le hdl (Nat.le_add_right _ _)) (by have := code_lt (sym (Γ := Γ) j); unfold S; omega) (fun o _ => by
            rw [hdisp]; unfold dispCode; rw [hMj])
        obtain ⟨w, hw, hw0, hw2, hwi⟩ := CProgram.push_spec (prog TM enc pre) (by decide) (by omega)
          (code_pos _) hP ![nA, nB, 0] (by simp)
        have hw1 : w 1 = nB := by rw [hwi 1 (by decide) (by decide)]; simp
        simp only [Matrix.cons_val_zero] at hw0
        rw [reg_ext hw0 hw1 hw2] at hw
        obtain ⟨p', hp', hr⟩ := loop_dsp TM enc pre q' ⟨R.head, L.cons h, R.tail⟩
          (good_push hA (code_pos _) (code_lt _)) hB
          (by show L.cons h = _; rw [hL, ← hsym, cons_stk])
          (by show R.tail.cons R.head = _; rw [ListBlank.cons_head_tail, hR])
        exact ⟨p', hp', Relation.TransGen.trans_left
          (transGen_of_ne hw (loop_ne q hj q')) hr⟩
      | left =>
        -- the pop of `A`
        have hP : (prog TM enc pre).Placed (S Γ * dispId Γ (Λ := Λ) (qi q) j) (3 * base Γ + 1)
            (CProgram.popM 0 2 (base Γ) (S Γ * dispId Γ (Λ := Λ) (qi q) j)
              (fun j' => S Γ * leftId Γ Λ (qi q) j j')) :=
          placed TM enc pre (lt_of_lt_of_le hdl (Nat.le_add_right _ _)) hSb (fun o _ => by rw [hdisp]; unfold dispCode; rw [hMj])
        obtain ⟨w, hw, hw0, hw2, hwi⟩ := CProgram.pop_spec (prog TM enc pre) (by decide)
          (by omega) hP ![nA, nB, 0] (by simp)
        have hw1 : w 1 = nB := by rw [hwi 1 (by decide) (by decide)]; simp
        simp only [Matrix.cons_val_zero] at hw hw0
        rw [reg_ext hw0 hw1 hw2] at hw
        -- the left-move block
        set j'' := nA % base Γ with hj''
        have hj''lt : j'' < base Γ := Nat.mod_lt _ base_pos
        obtain ⟨_, hll⟩ := left_bounds (Γ := Γ) q hj hj''lt
        set ℓ := S Γ * leftId Γ Λ (qi q) j j'' with hℓ
        have hleft : ∀ o, blockCode TM enc pre (leftId Γ Λ (qi q) j j'') o
            = leftCode TM q j j'' ℓ o := block_left TM enc pre q hj hj''lt
        have hc1 := code_lt (sym (Γ := Γ) j)
        have hc2 := code_lt (sym (Γ := Γ) j'')
        have hPS : P Γ + (base Γ + 3 + code (sym (Γ := Γ) j'')) ≤ S Γ := by unfold P S; omega
        have hPall : (prog TM enc pre).Placed ℓ (P Γ + (base Γ + 3 + code (sym (Γ := Γ) j'')))
            (leftCode TM q j j'' ℓ) := placed TM enc pre (lt_of_lt_of_le hll (Nat.le_add_right _ _)) hPS (fun o _ => hleft o)
        have hP1 : (prog TM enc pre).Placed ℓ (base Γ + 3 + code (sym (Γ := Γ) j))
            (CProgram.pushM 1 2 (base Γ) (code (sym (Γ := Γ) j)) ℓ (ℓ + P Γ)) := by
          have := CProgram.Placed.shift (k := 0) (size' := base Γ + 3 + code (sym (Γ := Γ) j))
            (g := CProgram.pushM 1 2 (base Γ) (code (sym (Γ := Γ) j)) ℓ (ℓ + P Γ)) hPall
            (by unfold P at hPS ⊢; omega) (fun o ho => by
              rw [Nat.zero_add]; unfold leftCode; rw [hMj]
              simp only [if_pos (show o < P Γ by unfold P; omega)])
          simpa using this
        have hP2 : (prog TM enc pre).Placed (ℓ + P Γ) (base Γ + 3 + code (sym (Γ := Γ) j''))
            (CProgram.pushM 1 2 (base Γ) (code (sym (Γ := Γ) j'')) (ℓ + P Γ)
              (S Γ * (4 + qi q'))) :=
          CProgram.Placed.shift hPall le_rfl (fun o _ => by
            unfold leftCode; rw [hMj]
            simp only [if_neg (show ¬ (P Γ + o < P Γ) by omega), Nat.add_sub_cancel_left])
        obtain ⟨u, hu, hu1, hu2, hui⟩ := CProgram.push_spec (prog TM enc pre) (by decide) (by omega)
          (code_pos _) hP1 ![nA / base Γ, nB, 0] (by simp)
        have hu0 : u 0 = nA / base Γ := by rw [hui 0 (by decide) (by decide)]; simp
        simp only [Matrix.cons_val_one, Matrix.head_cons] at hu1
        rw [reg_ext hu0 hu1 hu2] at hu
        obtain ⟨u', hu', hu'1, hu'2, hu'i⟩ := CProgram.push_spec (prog TM enc pre) (by decide)
          (by omega) (code_pos _) hP2
          ![nA / base Γ, base Γ * nB + code (sym (Γ := Γ) j), 0] (by simp)
        have hu'0 : u' 0 = nA / base Γ := by rw [hu'i 0 (by decide) (by decide)]; simp
        simp only [Matrix.cons_val_one, Matrix.head_cons] at hu'1
        rw [reg_ext hu'0 hu'1 hu'2] at hu'
        obtain ⟨p', hp', hr⟩ := loop_dsp TM enc pre q' ⟨L.head, L.tail, R.cons h⟩ (good_div hA)
          (good_push (good_push hB (code_pos _) (code_lt _)) (code_pos _) (code_lt _))
          (by show L.tail = _; rw [hL, tail_stk])
          (by
            show (R.cons h).cons L.head = _
            rw [hR, ← hsym, cons_stk, hL, head_stk hA, cons_stk])
        exact ⟨p', hp', Relation.TransGen.trans_left
          (transGen_of_ne (hw.trans (hu.trans hu')) (loop_ne q hj q')) hr⟩

/-- **A halting configuration** leads to the accepting halt. -/
theorem halt_sim {c : TM0.Cfg Γ Λ} {p : ℕ × (Fin 3 → ℕ)} (hD : Dsp c p)
    (hs : TM0.step TM c = none) : (prog TM enc pre).Reach p (acc (Γ := Γ)) := by
  obtain ⟨q, ⟨h, L, R⟩⟩ := c
  obtain ⟨j, nA, nB, hj, hA, hB, hsym, hL, hR, rfl⟩ := hD
  simp only at hsym
  unfold TM0.step at hs
  simp only [Option.map_eq_none_iff] at hs
  have hMj : TM q (sym j) = none := by rw [hsym]; exact hs
  obtain ⟨hlo, hhi⟩ := disp_bounds (Γ := Γ) q hj
  have hdl : dispId Γ (Λ := Λ) (qi q) j < nBlocks Γ Λ := by unfold nBlocks; omega
  have hP : (prog TM enc pre).Placed (S Γ * dispId Γ (Λ := Λ) (qi q) j) 1
      (fun _ => CInstr.test 2 (S Γ * 3) (S Γ * 3)) :=
    placed TM enc pre (lt_of_lt_of_le hdl (Nat.le_add_right _ _)) (by unfold S; omega) (fun o _ => by
      rw [block_disp TM enc pre q hj]; unfold dispCode; rw [hMj])
  have c0 := hP.get (prog TM enc pre) (o := 0) (by norm_num)
  rw [Nat.add_zero] at c0
  have s1 := CProgram.Step.zero (v := ![nA, nB, 0]) c0.1 c0.2 (by simp)
  exact (Relation.ReflTransGen.single s1).trans (clean_spec TM enc pre nA nB 0)

/-- The configuration relation. -/
def Tr (c : TM0.Cfg Γ Λ) (p : ℕ × (Fin 3 → ℕ)) : Prop :=
  (TM0.step TM c = none ∧ p = acc (Γ := Γ)) ∨ (TM0.step TM c ≠ none ∧ Dsp c p)

theorem to_tr {c : TM0.Cfg Γ Λ} {p : ℕ × (Fin 3 → ℕ)} (hD : Dsp c p) :
    ∃ p', Tr TM c p' ∧ (prog TM enc pre).Reach p p' := by
  by_cases hs : TM0.step TM c = none
  · exact ⟨_, Or.inl ⟨hs, rfl⟩, halt_sim TM enc pre hD hs⟩
  · exact ⟨p, Or.inr ⟨hs, hD⟩, Relation.ReflTransGen.refl⟩

theorem next_acc : (prog TM enc pre).next (acc (Γ := Γ)) = none := by
  have c3 := clean_code TM enc pre 3 (by norm_num)
  simp only [cleanCode, show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
    show (3 : ℕ) ≠ 2 by omega, if_false] at c3
  show (prog TM enc pre).next (S Γ * 3 + 3, fun _ => 0) = none
  simp [CProgram.next, c3.1, c3.2]

theorem reach_iff {M : CProgram} {a b : ℕ × (Fin 3 → ℕ)} :
    M.Reach a b ↔ StateTransition.Reaches M.next a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      exact ih.tail (by rw [Option.mem_def]; exact (M.step_iff_next).1 hst)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      exact ih.tail ((M.step_iff_next).2 (by rw [Option.mem_def] at hst; exact hst))

theorem respects : Respects (TM0.step TM) (prog TM enc pre).next (Tr TM (Γ := Γ)) := by
  intro a₁ a₂ h
  cases hs : TM0.step TM a₁ with
  | none =>
    rcases h with ⟨_, rfl⟩ | ⟨hne, _⟩
    · exact next_acc TM enc pre
    · exact absurd hs hne
  | some b₁ =>
    rcases h with ⟨hn, _⟩ | ⟨_, hD⟩
    · rw [hs] at hn; exact absurd hn (by simp)
    obtain ⟨p', hp', htr⟩ := step_sim TM enc pre hD hs
    obtain ⟨p'', hp'', hr⟩ := to_tr TM enc pre hp'
    refine ⟨p'', hp'', ?_⟩
    have ht : Relation.TransGen (prog TM enc pre).Step a₂ p'' := Relation.TransGen.trans_left htr hr
    clear hp'' hr htr hp' hD
    induction ht with
    | single hst =>
      exact Relation.TransGen.single (by rw [Option.mem_def]; exact ((prog TM enc pre).step_iff_next).1 hst)
    | tail _ hst ih =>
      exact ih.tail (by rw [Option.mem_def]; exact ((prog TM enc pre).step_iff_next).1 hst)

/-- Pushing a list of symbols, first element first. -/
noncomputable def pushList (n : ℕ) : List Γ → ℕ
  | [] => n
  | a :: as => pushList (base Γ * n + code a) as

theorem pushList_spec : ∀ (l : List Γ) (n : ℕ), Good Γ n →
    Good Γ (pushList n l) ∧ stk (pushList n l) = l.reverse ++ stk n := by
  intro l
  induction l with
  | nil => intro n hn; exact ⟨hn, by simp [pushList]⟩
  | cons a as ih =>
    intro n hn
    obtain ⟨h1, h2⟩ := ih (base Γ * n + code a) (good_push hn (code_pos a) (code_lt a))
    refine ⟨h1, ?_⟩
    rw [pushList, h2, stk_push]
    simp

theorem block_pre {s : ℕ} (hs : s < pre.length) (o : ℕ) :
    blockCode TM enc pre (nBlocks Γ Λ + s) o
      = CProgram.pushM 1 2 (base Γ) (code (pre.reverse.getD s default))
          (S Γ * (nBlocks Γ Λ + s))
          (if s + 1 < pre.length then S Γ * (nBlocks Γ Λ + s + 1)
            else S Γ * (4 + qi (default : Λ))) o := by
  have h4 : 4 ≤ nBlocks Γ Λ := by unfold nBlocks; omega
  have hnb : 4 + nQ Λ + nQ Λ * base Γ ≤ nBlocks Γ Λ := by unfold nBlocks; omega
  unfold blockCode
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show nBlocks Γ Λ + s - nBlocks Γ Λ = s by omega]
  by_cases h : s + 1 < pre.length
  · rw [if_pos (by omega), if_pos h, Nat.add_assoc]
  · rw [if_neg (by omega), if_neg h]

/-- The prefix pushes. -/
theorem pre_spec (n : ℕ) (hn : Good Γ n) :
    (prog TM enc pre).Reach (startAddr (Λ := Λ) pre, ![0, n, 0])
      (S Γ * (4 + qi (default : Λ)), ![0, pushList n pre.reverse, 0]) := by
  have hb2 := two_le_base Γ
  -- the chain from push `s` on
  have chain : ∀ t, ∀ s m, s + t + 1 = pre.length → Good Γ m →
      (prog TM enc pre).Reach (S Γ * (nBlocks Γ Λ + s), ![0, m, 0])
        (S Γ * (4 + qi (default : Λ)), ![0, pushList m (pre.reverse.drop s), 0]) := by
    intro t
    induction t with
    | zero =>
      intro s m hs hm
      have hsl : s < pre.length := by omega
      have hcode := code_lt (pre.reverse.getD s default)
      have hP : (prog TM enc pre).Placed (S Γ * (nBlocks Γ Λ + s))
          (base Γ + 3 + code (pre.reverse.getD s default))
          (CProgram.pushM 1 2 (base Γ) (code (pre.reverse.getD s default))
            (S Γ * (nBlocks Γ Λ + s)) (S Γ * (4 + qi (default : Λ)))) :=
        placed TM enc pre (by omega) (by unfold S; omega) (fun o _ => by
          rw [block_pre TM enc pre hsl, if_neg (by omega)])
      obtain ⟨w, hw, hw1, hw2, hwi⟩ := CProgram.push_spec (prog TM enc pre) (by decide)
        (by omega) (code_pos _) hP ![0, m, 0] (by simp)
      have hw0 : w 0 = 0 := by rw [hwi 0 (by decide) (by decide)]; simp
      simp only [Matrix.cons_val_one, Matrix.head_cons] at hw1
      rw [reg_ext hw0 hw1 hw2] at hw
      have hdrop : pre.reverse.drop s = [pre.reverse.getD s default] := by
        have hlen : s < pre.reverse.length := by rw [List.length_reverse]; omega
        rw [List.drop_eq_getElem_cons hlen, List.getD_eq_getElem _ _ hlen,
          List.drop_eq_nil_of_le (by rw [List.length_reverse]; omega)]
      rw [hdrop]
      exact hw
    | succ t ih =>
      intro s m hs hm
      have hsl : s < pre.length := by omega
      have hcode := code_lt (pre.reverse.getD s default)
      have hP : (prog TM enc pre).Placed (S Γ * (nBlocks Γ Λ + s))
          (base Γ + 3 + code (pre.reverse.getD s default))
          (CProgram.pushM 1 2 (base Γ) (code (pre.reverse.getD s default))
            (S Γ * (nBlocks Γ Λ + s)) (S Γ * (nBlocks Γ Λ + s + 1))) :=
        placed TM enc pre (by omega) (by unfold S; omega) (fun o _ => by
          rw [block_pre TM enc pre hsl, if_pos (by omega)])
      obtain ⟨w, hw, hw1, hw2, hwi⟩ := CProgram.push_spec (prog TM enc pre) (by decide)
        (by omega) (code_pos _) hP ![0, m, 0] (by simp)
      have hw0 : w 0 = 0 := by rw [hwi 0 (by decide) (by decide)]; simp
      simp only [Matrix.cons_val_one, Matrix.head_cons] at hw1
      rw [reg_ext hw0 hw1 hw2] at hw
      have hrest := ih (s + 1) (base Γ * m + code (pre.reverse.getD s default)) (by omega)
        (good_push hm (code_pos _) (code_lt _))
      have hdrop : pre.reverse.drop s = pre.reverse.getD s default :: pre.reverse.drop (s + 1) := by
        have hlen : s < pre.reverse.length := by rw [List.length_reverse]; omega
        rw [List.drop_eq_getElem_cons hlen, List.getD_eq_getElem _ _ hlen]
      rw [hdrop, pushList]
      rw [show nBlocks Γ Λ + (s + 1) = nBlocks Γ Λ + s + 1 by ring] at hrest
      exact hw.trans hrest
  by_cases hL : pre.length = 0
  · have hnil : pre = [] := List.length_eq_zero_iff.1 hL
    unfold startAddr
    rw [if_pos hL, hnil]
    exact Relation.ReflTransGen.refl
  · unfold startAddr
    rw [if_neg hL]
    have := chain (pre.length - 1) 0 n (by omega) hn
    simpa using this

/-- **§3.**  The program accepts `x` exactly when the machine halts on the prefix followed by
the binary digits of `x`, most significant first. -/
theorem accepts_iff (x : ℕ) :
    (prog TM enc pre).Accepts x ↔ (TM0.eval TM (pre ++ (lsbBits x).reverse.map enc)).Dom := by
  set l := pre ++ (lsbBits x).reverse.map enc with hl
  -- the start reaches a related configuration
  have hstart : CProgram.start x = ![x, 0, 0] := by
    apply reg_ext <;> simp [CProgram.start]
  obtain ⟨hG0, hstk0⟩ := loadB_spec enc x 0 good_zero
  rw [stk_zero, List.append_nil] at hstk0
  obtain ⟨hG, hstk⟩ := pushList_spec pre.reverse (TMStack.loadB enc x 0) hG0
  rw [hstk0, List.reverse_reverse, ← hl] at hstk
  have hload := load_spec TM enc pre x 0 good_zero
  have hpre := pre_spec TM enc pre (TMStack.loadB enc x 0) hG0
  obtain ⟨p1, hp1, hr1⟩ := loop_dsp TM enc pre (default : Λ) (Tape.mk₁ l) good_zero hG
    (by show ListBlank.mk [] = _; rw [stk_zero])
    (by
      show ((ListBlank.mk l).tail).cons (ListBlank.mk l).head = _
      rw [ListBlank.cons_head_tail, hstk])
  obtain ⟨p0, hp0, hr0⟩ := to_tr TM enc pre hp1
  have hreach : (prog TM enc pre).Reach (0, CProgram.start x) p0 := by
    rw [hstart]; exact hload.trans (hpre.trans (hr1.trans hr0))
  have hTr : Tr TM (TM0.init l) p0 := hp0
  have heval : StateTransition.eval (prog TM enc pre).next (0, CProgram.start x)
      = StateTransition.eval (prog TM enc pre).next p0 := reaches_eval (reach_iff.1 hreach)
  have hdom := tr_eval_dom (respects TM enc pre) hTr
  show _ ↔ (StateTransition.eval (TM0.step TM) (TM0.init l)).Dom
  rw [← hdom, ← heval]
  constructor
  · rintro ⟨ℓ, hℓ, hc, hr⟩
    refine Part.dom_iff_mem.2 ⟨(ℓ, fun _ => 0), mem_eval.2 ⟨reach_iff.1 hr, ?_⟩⟩
    simp [CProgram.next, hℓ, hc]
  · intro hd
    obtain ⟨b₁, hb₁⟩ := Part.dom_iff_mem.1 (hdom.1 (by rw [heval] at hd; exact hd))
    obtain ⟨b₂, hb₂, hb₂mem⟩ := tr_eval (respects TM enc pre) hTr hb₁
    have hhalt := (mem_eval.1 hb₁).2
    rcases hb₂ with ⟨_, rfl⟩ | ⟨hne, _⟩
    · have hr := reach_iff.2 (mem_eval.1 hb₂mem).1
      have c3 := clean_code TM enc pre 3 (by norm_num)
      simp only [cleanCode, show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
        show (3 : ℕ) ≠ 2 by omega, if_false] at c3
      exact ⟨S Γ * 3 + 3, c3.1, c3.2, (hreach.trans hr)⟩
    · exact absurd hhalt hne


end TMCounter

end Jones1980
