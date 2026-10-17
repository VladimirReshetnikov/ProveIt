import BusyBeaver.ZFC.ArithmeticCommandExecution254
import BusyBeaver.ZFC.ArithmeticProofWordContract254

/-!
Exact command-cons execution, finite stack popping and the actual discard block.
All numerical operands and saved registers range over an arbitrary IΣ1 model.
Lists used to organize the fixed AX pushes and NIP counts are external finite
proof notation, not an interpretation of arbitrary internal words as lists.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle)
open ArithmeticCommandWord254 ArithmeticCommandAppend254 ArithmeticCommandStep254
open ArithmeticCommandRun254 ArithmeticCommandExecution254 ArithmeticProofWordContract254
open ArithmeticCommandBlocks254 (Circuit)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def mpWord (x rest : V) : V := cantor 0 (cantor x rest) + 1
noncomputable def dropWord (x rest : V) : V := cantor 1 (cantor x rest) + 1
noncomputable def nipWord (x rest : V) : V := cantor 2 (cantor x rest) + 1
noncomputable def axWord (c x y u rest : V) : V :=
  cantor (c+3) (cantor x (cantor y (cantor u rest))) + 1

/-- These are actual arithmetic words, evaluated by the checked interpreter. -/
theorem eval_mp (x rest t s d h : V) :
    evalValue (mpWord x rest) (stateValue t s d h) =
      if wim t (d+x) = h then evalValue rest (stateValue (d+x) (cantor 0 s) (d+x) 0)
      else evalValue rest (stateValue 0 s (d+x) 0) := by
  rw [mpWord, eval_succ, stepValue_mp]
  by_cases he : wim t (d+x) = h <;> simp [he, someState, tailValue]

theorem eval_drop (x rest t s d h : V) :
    evalValue (dropWord x rest) (stateValue t s d h) =
      evalValue rest (stateValue h (cantor t s) (d+x) h) := by
  rw [dropWord, eval_succ, stepValue_drop]
  simp [someState, tailValue]

theorem eval_nip (x rest t s d h : V) :
    evalValue (nipWord x rest) (stateValue t s d h) =
      if h = 1 then 0 else evalValue rest (stateValue t (second s) (d+x) (first s)) := by
  rw [nipWord, eval_succ, stepValue_nip]
  have h23 : (2 : V) < 3 := by
    simpa only [two_add_one_eq_three] using (lt_succ_iff_le.mpr (le_rfl : (2 : V) ≤ 2))
  by_cases he : h = 1 <;> simp [he, someState, tailValue, h23]

theorem eval_ax (c x y u rest t s d h : V) :
    evalValue (axWord c x y u rest) (stateValue t s d h) =
      evalValue rest (stateValue (gateValue (d+x) (h+y) c)
        (axStackValue (d+x) h (h+y) c u t s) 0 0) := by
  rw [axWord, eval_succ, stepValue_ax]
  have hc : ¬ c+3 < (3 : V) := not_lt_of_ge le_add_self
  simp [someState, tailValue, hc]

@[simp] theorem eval_append_halt (left right w : V) (h : evalValue left w = 0) :
    evalValue (appendValue left right) w = 0 := by simp [eval_append, h]

theorem eval_append_success (left right w w' : V) (h : evalValue left w = w'+1) :
    evalValue (appendValue left right) w = evalValue right w' := by
  simp [eval_append, h]

noncomputable def nipsWord : Nat → V
  | 0 => 0
  | k+1 => nipWord 0 (nipsWord k)

noncomputable def pushL : List V → V → V
  | [], s => s
  | x::xs, s => cantor x (pushL xs s)

lemma pushL_append (xs ys : List V) (s : V) :
    pushL (xs++ys) s = pushL xs (pushL ys s) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, pushL, ih]

/-- The finite counter counts the explicitly displayed pushes, while each
entry and every state component may be an arbitrary internal model element. -/
theorem eval_nips (t s d : V) : ∀ (xs : List V) (h last : V),
    h ≠ 1 → (∀ x, x ∈ xs → x ≠ 1) →
      evalValue (nipsWord (xs.length+1)) (stateValue t (pushL (xs++[last]) s) d h) =
        someState t s d last
  | [], h, last, hh, _ => by
      simp only [List.nil_append, List.length_nil, Nat.zero_add, pushL]
      rw [nipsWord, eval_nip, if_neg hh]
      simp [nipsWord, someState]
  | x::xs, h, last, hh, hx => by
      simp only [List.cons_append, pushL, List.length_cons]
      rw [nipsWord, eval_nip, if_neg hh]
      simp only [first_cantor, second_cantor, add_zero]
      exact eval_nips t s d xs x last (hx x (List.mem_cons_self ..))
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))

lemma wim_ne_one (a b : V) : wim a b ≠ 1 := by
  intro he
  have hm := congrArg (fun x : V => x % 4) he
  simp [wim, tagged] at hm

lemma wal_ne_one (a b : V) : wal a b ≠ 1 := by
  intro he
  have h23 : (2 : V) < 3 := by
    simpa only [two_add_one_eq_three] using (lt_succ_iff_le.mpr (le_rfl : (2 : V) ≤ 2))
  have h34 : (3 : V) < 4 := by
    simpa only [three_add_one_eq_four] using (lt_succ_iff_le.mpr (le_rfl : (3 : V) ≤ 3))
  have hm := congrArg (fun x : V => x % 4) he
  simp [wal, tagged, mod_eq_self_of_lt (lt_trans h23 h34)] at hm

lemma wim_one_ne_zero (a : V) : wim a 1 ≠ 0 := by
  intro he
  have hle : (1 : V) ≤ wim a 1 := (tagged_components 0 a 1).2
  simp [he] at hle

lemma gate_ne_one (a b c : V) : gateValue a b c ≠ 1 := by
  classical
  unfold gateValue
  split
  · simp
  · exact wim_ne_one _ _

@[simp] lemma gate_self (a b : V) : gateValue a b a = 0 := by
  simp [gateValue]

noncomputable def axList (a h b c u : V) : List V :=
  [rho1 a b, rho2 a b c, rho3 a b c, rho4 a b c, rho5 a b c,
    rho6 a b, rho7 a b c, rho8 a b c u, wal a h]

lemma axStack_eq (a h b c u t s : V) :
    axStackValue a h b c u t s = pushL (axList a h b c u ++ [t]) s := rfl

lemma axList_ne_one (a h b c u : V) : ∀ x, x ∈ axList a h b c u → x ≠ 1 := by
  intro x hx
  simp only [axList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact wim_ne_one _ _ | exact wal_ne_one _ _

lemma circuit_consMp (x rest : Circuit) (a b c u : V) :
    (Circuit.consMp x rest).eval a b c u = mpWord (x.eval a b c u) (rest.eval a b c u) := rfl
lemma circuit_consDrop (x rest : Circuit) (a b c u : V) :
    (Circuit.consDrop x rest).eval a b c u = dropWord (x.eval a b c u) (rest.eval a b c u) := rfl
lemma circuit_consNip (x rest : Circuit) (a b c u : V) :
    (Circuit.consNip x rest).eval a b c u = nipWord (x.eval a b c u) (rest.eval a b c u) := by
  simp [Circuit.consNip, Circuit.eval, Circuit.two, nipWord, one_add_one_eq_two]
lemma circuit_consAx (c x y z rest : Circuit) (a b d u : V) :
    (Circuit.consAx c x y z rest).eval a b d u =
      axWord (c.eval a b d u) (x.eval a b d u) (y.eval a b d u) (z.eval a b d u)
        (rest.eval a b d u) := by
  have h3 : (1 : V) + (1+1) = 3 := by
    rw [one_add_one_eq_two, add_comm 1 2, two_add_one_eq_three]
  simp only [Circuit.consAx, Circuit.eval, Circuit.three, Circuit.two, axWord, h3]
lemma circuit_append (x y : Circuit) (a b c u : V) :
    (Circuit.append x y).eval a b c u = appendValue (x.eval a b c u) (y.eval a b c u) := rfl
lemma circuit_nips (k : Nat) (a b c u : V) :
    (Circuit.nips k).eval a b c u = nipsWord k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Circuit.nips, circuit_consNip, ih]; rfl

/-- The actual discard block clears the current formula without consuming
any saved stack; its internal MP cannot succeed with zero cache. -/
theorem eval_discard (a b c u t s : V) :
    evalValue (Circuit.discard.eval a b c u) (stateValue t s 0 0) = someState 0 s 0 0 := by
  rw [Circuit.discard, circuit_consMp, circuit_consAx, circuit_nips]
  simp only [Circuit.eval_one, Circuit.eval_zero]
  rw [eval_mp]
  simp only [zero_add, wim_one_ne_zero, if_false]
  rw [eval_ax]
  simp only [add_zero, gate_self, axStack_eq]
  exact eval_nips 0 s 0 (axList 1 0 0 1 0) 0 0 (by simp) (axList_ne_one _ _ _ _ _)

theorem discard_contract (a b c u : V) : Contract (Circuit.discard.eval a b c u) 0 :=
  fun t s => Or.inr (eval_discard a b c u t s)

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254
