import DiophantineConsistency.ArithmeticCommandCompositionPerm222

/-! Literal all-internal command blocks for the actual permuted C222 machine.
Finite lists/counts only describe fixed pushes and pops. AX reads y then x
and uses the old counter for rho8's fourth parameter and the GEN label.
No arbitrary proof compiler or unrestricted rho8 block is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticCommandBlockPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticTemplates254
open ArithmeticCommandWordPerm222 ArithmeticCommandStepPerm222
open ArithmeticCommandAppendPerm222 ArithmeticCommandRunPerm222
open ArithmeticCommandEvaluationPerm222 ArithmeticCommandCompositionPerm222
attribute [local irreducible] Code254.P
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def nipWord (rest : V) : V := cantor 0 rest + 1
noncomputable def dropWord (rest : V) : V := cantor 1 rest + 1
noncomputable def mpWord (x rest : V) : V := cantor 2 (cantor x rest) + 1
/-- API order c,x,y; physical fields y,x. No fourth payload. -/
noncomputable def axWord (c x y rest : V) : V :=
  cantor (c+3) (cantor y (cantor x rest)) + 1

theorem eval_nip (rest t S d h : V) :
    evalValue (nipWord rest) (stateValue t S d h) =
      if h=1 then 0 else evalValue rest (stateValue t (second S) d (first S)) := by
  rw [nipWord, eval_succ, stepValue_nip]
  by_cases hh : h=1 <;> simp [hh, someState, tail_nip]

theorem eval_drop (rest t S d h : V) :
    evalValue (dropWord rest) (stateValue t S d h) =
      evalValue rest (stateValue h (cantor t S) d h) := by
  rw [dropWord, eval_succ, stepValue_drop]
  simp [someState, tail_drop]

theorem eval_mp (x rest t S d h : V) :
    evalValue (mpWord x rest) (stateValue t S d h) =
      if wim t (d+x)=h then
        evalValue rest (stateValue (d+x) (cantor 0 S) (d+x) 0)
      else evalValue rest (stateValue 0 S (d+x) 0) := by
  rw [mpWord, eval_succ, stepValue_mp]
  by_cases hh : wim t (d+x)=h <;> simp [hh, someState, tail_mp]

theorem eval_ax (c x y rest t S d h : V) :
    evalValue (axWord c x y rest) (stateValue t S d h) =
      evalValue rest (stateValue (gateValue (d+x) (h+y) c)
        (axStackValue (d+x) h (h+y) c d t S) 0 0) := by
  rw [axWord, eval_succ, stepValue_ax]
  simp [someState, tail_ax]

noncomputable def nipsWord : Nat → V
  | 0 => 0
  | k+1 => nipWord (nipsWord k)

noncomputable def pushL : List V → V → V
  | [], S => S
  | x::xs, S => cantor x (pushL xs S)

theorem pushL_append (xs ys : List V) (S : V) :
    pushL (xs++ys) S = pushL xs (pushL ys S) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, pushL, ih]

/-- The last entry may be false1: the final pop loads it without testing it. -/
theorem eval_nips (t S d : V) : ∀ (xs : List V) (h last : V),
    h≠1 → (∀ x, x∈xs → x≠1) →
      evalValue (nipsWord (xs.length+1))
        (stateValue t (pushL (xs++[last]) S) d h) = someState t S d last
  | [], h, last, hh, _ => by
      simp only [List.nil_append, List.length_nil, Nat.zero_add, pushL]
      rw [nipsWord, eval_nip, if_neg hh]
      simp [nipsWord, someState]
  | x::xs, h, last, hh, hx => by
      simp only [List.cons_append, pushL, List.length_cons]
      rw [nipsWord, eval_nip, if_neg hh]
      simp only [first_cantor, second_cantor]
      exact eval_nips t S d xs x last (hx x (List.mem_cons_self ..))
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem eval_nips_cont (t S d : V) (xs : List V) (h last rest : V)
    (hh : h≠1) (hx : ∀ x, x∈xs → x≠1) :
    evalValue (appendValue (nipsWord (xs.length+1)) rest)
      (stateValue t (pushL (xs++[last]) S) d h) =
        evalValue rest (stateValue t S d last) :=
  eval_append_success _ _ _ _ (eval_nips t S d xs h last hh hx)

theorem wim_ne_one (a b : V) : wim a b ≠ 1 := by
  intro he
  have hm := congrArg (fun x : V => x % 4) he
  simp [wim, tagged] at hm

theorem wal_ne_one (a b : V) : wal a b ≠ 1 := by
  intro he
  have h23 : (2 : V) < 3 := by
    simpa only [two_add_one_eq_three] using (lt_succ_iff_le.mpr (le_rfl : (2 : V) ≤ 2))
  have h34 : (3 : V) < 4 := by
    simpa only [three_add_one_eq_four] using (lt_succ_iff_le.mpr (le_rfl : (3 : V) ≤ 3))
  have hm := congrArg (fun x : V => x % 4) he
  simp [wal, tagged, mod_eq_self_of_lt (lt_trans h23 h34)] at hm

theorem wim_right_ne_zero (a b : V) (hb : b≠0) : wim a b ≠ 0 := by
  intro he
  have hle : b ≤ wim a b := (tagged_components 0 a b).2
  rw [he] at hle
  exact hb (le_antisymm hle (by simp))

theorem gate_ne_one (a b c : V) : gateValue a b c ≠ 1 := by
  classical
  unfold gateValue
  split
  · simp
  · exact wim_ne_one _ _

@[simp] theorem gate_self (a b : V) : gateValue a b a = 0 := by
  simp [gateValue]

noncomputable def axList (a h b c u : V) : List V :=
  [rho1 a b, rho2 a b c, rho3 a b c, rho4 a b c, rho5 a b c,
    rho6 a c, ArithmeticTemplates222.growG a b c, rho8 a b c u, wal u h]

theorem axStack_eq (a h b c u t S : V) :
    axStackValue a h b c u t S = pushL (axList a h b c u ++ [t]) S := rfl

theorem axList_ne_one (a h b c u : V) : ∀ x, x∈axList a h b c u → x≠1 := by
  intro x hx
  simp only [axList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact wim_ne_one _ _ | exact wal_ne_one _ _

noncomputable def discardWord : V := mpWord 1 (axWord 1 0 0 (nipsWord 10))

/-- After MP1, AX's old counter is 1, including its rho8/GEN parameters. -/
theorem eval_discard (t S : V) :
    evalValue discardWord (stateValue t S 0 0) = someState 0 S 0 0 := by
  rw [discardWord, eval_mp]
  simp only [zero_add, wim_right_ne_zero t 1 (by simp), if_false]
  rw [eval_ax]
  simp only [add_zero, gate_self, axStack_eq]
  exact eval_nips 0 S 0 (axList 1 0 0 1 1) 0 0 (by simp) (axList_ne_one _ _ _ _ _)

/-- Empty at zero. MP0 would succeed and push an unwanted zero. -/
noncomputable def Jword (u : V) : V := if u=0 then 0 else mpWord u 0

def JwordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out u. (u = 0 ∧ out = 0) ∨ (u ≠ 0 ∧
    ∃ p, !ArithmeticCantor.pairDef p u 0 ∧
    ∃ q, !ArithmeticCantor.pairDef q 2 p ∧ out = q + 1)”

instance Jword_defined : 𝚺₁-Function₁[V] Jword via JwordDef := .mk fun e => by
  classical
  by_cases hu : e 1=0 <;> simp [JwordDef, Jword, mpWord, hu]

@[simp] theorem Jword_zero : Jword (0 : V) = 0 := by simp [Jword]

theorem eval_J (u S rest : V) :
    evalValue (appendValue (Jword u) rest) (stateValue 0 S 0 0) =
      evalValue rest (stateValue 0 S u 0) := by
  by_cases hu : u=0
  · subst u
    rw [Jword_zero, appendValue_zero]
  · have he : evalValue (Jword u) (stateValue 0 S 0 0) = someState 0 S u 0 := by
      rw [Jword, if_neg hu, eval_mp]
      simp [wim_right_ne_zero 0 u hu, someState]
    exact eval_append_success _ _ _ _ he

/-- Exact actual stack setup, from arbitrary top and saved stack. Only the
physical subtraction guard u≤a is needed; collisions and zero labels remain. -/
theorem eval_discard_ax (t S a b c u rest : V) (hu : u≤a) :
    evalValue (appendValue discardWord
      (appendValue (Jword u) (axWord c (a-u) b rest))) (stateValue t S 0 0) =
        evalValue rest (stateValue (gateValue a b c) (axStackValue a 0 b c u 0 S) 0 0) := by
  rw [eval_append_success _ _ _ _ (eval_discard t S), eval_J, eval_ax]
  have ha : u+(a-u)=a := by
    simpa only [add_comm] using (Arithmetic.sub_spec_of_ge hu).symm
  simp only [ha, zero_add]

end DiophantineConsistency.ArithmeticCommandBlockPerm222
