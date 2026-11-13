import BusyBeaver.ZFC.ArithmeticRow254
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
A single fixed represented history evaluator for the exact C254 proof code.
The fixed row and the actual twelve-rule code are imported unchanged.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticHistory254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticRow254

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Compute the positive-code row, using actual total sequence lookups. -/
noncomputable def positiveStep (s z : V) : V :=
  let k := z % 12
  let p := z / 12
  let t := second p
  rowKernel k p (if k = 2 then znth s t else znth s (first t))
    (znth s (second t))

def positiveStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s z. ∃ k, !remDef k z 12 ∧ ∃ p, !divDef p z 12 ∧
    ∃ t, !ArithmeticCantor.secondDef t p ∧
    ∃ b, !ArithmeticCantor.firstDef b t ∧
    ∃ c, !ArithmeticCantor.secondDef c t ∧
    ∃ u, ((k = 2 ∧ !znthDef u s t) ∨ (k ≠ 2 ∧ !znthDef u s b)) ∧
    ∃ v, !znthDef v s c ∧ !ArithmeticRow254.rowDef r k p u v”

instance positiveStep_defined : 𝚺₁-Function₂[V] positiveStep via positiveStepDef :=
  .mk fun e => by
    classical
    by_cases h : e 2 % 12 = 2 <;> simp [positiveStepDef, positiveStep, numeral_eq_natCast, h]

/-- Code zero is invalid; every positive code uses its predecessor's base12
remainder and quotient. -/
noncomputable def stepValue (s code : V) : V := by
  classical
  exact if code = 0 then 0 else positiveStep s (code - 1)

def stepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s code. (code = 0 ∧ r = 0) ∨
    (∃ z <⁺ code, code = z + 1 ∧ !positiveStepDef r s z)”

instance step_defined : 𝚺₁-Function₂[V] stepValue via stepDef := .mk fun e => by
  classical
  simp [stepDef]
  rw [predecessor_witness]
  by_cases h : e 2 = 0 <;> simp [stepValue, h]

@[simp] theorem stepValue_zero (s : V) : stepValue s 0 = 0 := by
  simp [stepValue]

@[simp] theorem stepValue_succ (s z : V) : stepValue s (z + 1) = positiveStep s z := by
  simp [stepValue]

def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “s. !mkSeq₁Def s 0”

def succDef : 𝚺₁.Semisentence 3 := .mkSigma
  “s previous index. ∃ value, !stepDef value previous (index + 1) ∧
    !seqConsDef s previous value”

def blueprint : PR.Blueprint 0 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := seqCons ∅ 0
  succ _ index previous := seqCons previous (stepValue previous (index + 1))
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

noncomputable def history (code : V) : V := construction.result ![] code

def historyDef : 𝚺₁.Semisentence 2 := blueprint.resultDef

def historyDeltaDef : 𝚫₁.Semisentence 2 := blueprint.resultDeltaDef

instance history_defined : 𝚺₁-Function₁[V] history via historyDef :=
  .mk fun e => by
    have he : (fun i : Fin 0 => e i.succ.succ) = ![] := Subsingleton.elim _ _
    have h := (construction (V := V)).result_defined.df e
    change blueprint.resultDef.val.Evalb e ↔
      e 0 = construction.result (fun i : Fin 0 => e i.succ.succ) (e 1) at h
    rw [he] at h
    change blueprint.resultDef.val.Evalb e ↔ e 0 = construction.result ![] (e 1)
    exact h

instance history_defined_delta : 𝚫₁-Function₁[V] history via historyDeltaDef :=
  history_defined.graph_delta

instance history_definable : 𝚺₁-Function₁[V] history := history_defined.to_definable

@[simp] theorem history_zero : history (0 : V) = seqCons ∅ 0 := by
  simp [history, construction]

@[simp] theorem history_succ (code : V) :
    history (code + 1) = seqCons (history code) (stepValue (history code) (code + 1)) := by
  simp [history, PR.Construction.result_succ, construction]

/-- Sequence validity holds even at nonstandard model indices, by definable
Sigma1 induction, not by an external Nat recursion. -/
theorem history_seq (code : V) : Seq (history code) := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih =>
    rw [history_succ]
    exact ih.seqCons _

theorem history_length (code : V) : lh (history code) = code + 1 := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih =>
    rw [history_succ, (history_seq code).lh_seqCons, ih]

noncomputable def value (code : V) : V := znth (history code) code

def valueDef : 𝚺₁.Semisentence 2 := .mkSigma
  “r code. ∃ s, !historyDef s code ∧ !znthDef r s code”

instance value_defined : 𝚺₁-Function₁[V] value via valueDef :=
  .mk fun e => by simp [valueDef, value]

def valueDeltaDef : 𝚫₁.Semisentence 2 := valueDef.graphDelta

instance value_defined_delta : 𝚫₁-Function₁[V] value via valueDeltaDef :=
  value_defined.graph_delta

/-- One fixed acceptance formula, with actual child lookups and history
iteration included. -/
def checkDef : 𝚺₁.Semisentence 2 := .mkSigma
  “code conclusion. ∃ r, !valueDef r code ∧ r = conclusion + 1”

instance check_defined : 𝚺₁-Relation[V] (fun code conclusion => value code = conclusion + 1)
    via checkDef := .mk fun e => by simp [checkDef]

noncomputable def checkValue (code conclusion : V) : V := by
  classical
  exact if value code = conclusion + 1 then 1 else 0

def checkValueDef : 𝚺₁.Semisentence 3 := .mkSigma
  “b code conclusion. ∃ r, !valueDef r code ∧
    ((r = conclusion + 1 ∧ b = 1) ∨ (r ≠ conclusion + 1 ∧ b = 0))”

instance checkValue_defined : 𝚺₁-Function₂[V] checkValue via checkValueDef :=
  .mk fun e => by
    classical
    by_cases h : value (e 1) = e 2 + 1 <;> simp [checkValueDef, checkValue, h]

def checkValueDeltaDef : 𝚫₁.Semisentence 3 := checkValueDef.graphDelta

instance checkValue_defined_delta : 𝚫₁-Function₂[V] checkValue via checkValueDeltaDef :=
  checkValue_defined.graph_delta

/-- Total unique evaluation at EVERY element of every IΣ1 model. -/
theorem value_total (code : V) : ∃! r, valueDef.val.Evalb ![r, code] := by
  simp

/-- Boolean-valued total graph at arbitrary, possibly nonstandard codes. -/
theorem checkValue_total (code conclusion : V) :
    ∃! b, checkValueDef.val.Evalb ![b, code, conclusion] := by
  simp

theorem checkValue_range (code conclusion : V) :
    checkValue code conclusion = 0 ∨ checkValue code conclusion = 1 := by
  classical
  by_cases h : value code = conclusion + 1 <;> simp [checkValue, h]

/-- Foundation's choice-defined division agrees with the usual Nat quotient,
including divisor zero. -/
@[simp] theorem foundation_div_nat (a b : Nat) :
    @Div.div Nat (Arithmetic.instDiv_foundation) a b = a / b := by
  symm
  apply Arithmetic.div_graph.mpr
  constructor
  · intro hb
    constructor
    · have hq : b * (a / b) ≤ a := by
        simpa only [Nat.mul_comm] using Nat.div_mul_le_self a b
      rw [Arithmetic.le_def]
      omega
    · exact Nat.lt_mul_div_succ a hb
  · intro hb
    simp [hb]

@[simp] theorem foundation_rem_nat (a b : Nat) :
    @Mod.mod Nat Arithmetic.instMod_foundation a b = a % b := by
  change Arithmetic.sub a (b * (@Div.div Nat Arithmetic.instDiv_foundation a b)) = a % b
  rw [foundation_sub_nat, foundation_div_nat, Nat.mod_eq_sub_mul_div]

lemma numeral_twelve_eq_twelve : (ORingStructure.numeral 12 : V) = 12 := by
  simp [numeral_eq_natCast]

/-- The positive selector agrees with the actual numeric row, not just the
constructor quotation cases. -/
theorem positiveStep_nat (s z : Nat) :
    positiveStep s z = Code254History.row (znth s) (z % 12) (z / 12) := by
  unfold positiveStep
  rw [← numeral_twelve_eq_twelve, ← numeral_two_eq_two]
  simp only [Nat.numeral_eq, HMod.hMod, HDiv.hDiv]
  rw [foundation_rem_nat, foundation_div_nat]
  by_cases h : z % 12 = 2 <;>
    simpa [second_nat, first_nat, HMod.hMod, HDiv.hDiv, h] using
      rowKernel_nat (znth s) (z % 12) (z / 12)

theorem stepValue_nat (s code : Nat) :
    stepValue s code = Code254History.step (znth s) code := by
  cases code with
  | zero => simp [Code254History.step]
  | succ code =>
      rw [show code + 1 = Nat.succ code from rfl]
      simpa only [Nat.succ_eq_add_one, stepValue_succ, Code254History.step] using
        positiveStep_nat s code
/-- Appending a value keeps every older lookup exactly. -/
theorem znth_append_old {s : V} (hs : Seq s) (x i : V) (hi : i < lh s) :
    znth (seqCons s x) i = znth s i := by
  apply (hs.seqCons x).znth_eq_of_mem
  exact Seq.subset_seqCons s x (hs.znth hi)

/-- Appending places its value at exactly the old length. -/
theorem znth_append_last {s : V} (hs : Seq s) (x : V) :
    znth (seqCons s x) (lh s) = x :=
  (hs.seqCons x).znth_eq_of_mem (Seq.mem_seqCons s x)

/-- Full append semantics, including every index outside the new sequence. -/
theorem znth_append {s : V} (hs : Seq s) (x i : V) :
    znth (seqCons s x) i =
      if i < lh s then znth s i else if i = lh s then x else 0 := by
  classical
  by_cases hi : i < lh s
  · simp only [hi, if_pos]
    exact znth_append_old hs x i hi
  · by_cases he : i = lh s
    · simpa [he] using znth_append_last hs x
    · simp only [hi, he, if_false]
      apply znth_prop_not
      right
      rw [hs.lh_seqCons]
      exact lt_iff_succ_le.mp (lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm he))

private theorem lookup_append (xs : List Nat) (x i : Nat) :
    Code254History.lookup (xs ++ [x]) i =
      if i < xs.length then Code254History.lookup xs i else
      if i = xs.length then x else 0 := by
  by_cases hi : i < xs.length
  · simp [Code254History.lookup, List.getElem?_append_left hi, hi]
  · by_cases he : i = xs.length
    · simp [he, Code254History.lookup]
    · have hgt : xs.length < i := by omega
      have hd : i - xs.length ≠ 0 := by omega
      simp [Code254History.lookup, List.getElem?_append_right (by omega : xs.length ≤ i),
        hi, he, hd]

/-- ALL-index compatibility: out-of-range lookups are zero on both sides.
This is not restricted to child indices of valid proof quotations. -/
theorem history_lookup_nat (n i : Nat) :
    znth (history n) i = Code254History.lookup (Code254History.history n) i := by
  induction n generalizing i with
  | zero =>
      rw [history_zero, znth_append (seq_empty (V := Nat))]
      simp only [lh_empty]
      cases i <;> simp [Code254History.history, Code254History.lookup]
  | succ n ih =>
      rw [history_succ,
        znth_append (history_seq n), history_length, stepValue_nat]
      have hrec : znth (history n) = Code254History.lookup (Code254History.history n) :=
        funext ih
      rw [hrec, Code254History.history, lookup_append, Code254History.history_length]
      by_cases hi : i < n + 1 <;> by_cases he : i = n + 1 <;> simp [hi, he]

/-- Exact full evaluator agreement on EVERY Nat input, invalid codes included. -/
theorem value_nat (code : Nat) : value code = Code254History.value code :=
  history_lookup_nat code code

theorem checkDef_nat (code conclusion : Nat) :
    checkDef.val.Evalb ![code, conclusion] ↔
      Code254Proof.check code conclusion = true := by
  have h := (check_defined (V := Nat)).df ![code, conclusion]
  change checkDef.val.Evalb ![code, conclusion] ↔ value code = conclusion + 1 at h
  rw [value_nat] at h
  exact h.trans ((by simp only [Code254History.accepts, decide_eq_true_eq] :
    Code254History.value code = conclusion + 1 ↔
      Code254History.accepts code conclusion = true).trans
    (Code254History.accepts_iff_check code conclusion))

/-- External witness interface for the SAME fixed represented predicate. -/
theorem c254_iff_represented (conclusion : Nat) :
    Code254.C254 conclusion ↔ ∃ code, checkDef.val.Evalb ![code, conclusion] := by
  rw [Code254Proof.c254_iff_checked]
  exact exists_congr fun code => (checkDef_nat code conclusion).symm


theorem history_total (code : V) : ∃! s, historyDef.val.Evalb ![s, code] := by
  simp

@[simp] theorem value_zero : value (0 : V) = 0 := by
  rw [value, history_zero]
  simpa only [lh_empty] using znth_append_last (seq_empty (V := V)) (0 : V)

@[simp] theorem checkValue_zero (conclusion : V) : checkValue 0 conclusion = 0 := by
  simp [checkValue]

/-- The represented Boolean result matches the actual all-code checker. -/
theorem checkValue_nat (code conclusion : Nat) :
    checkValue code conclusion =
      if Code254Proof.check code conclusion = true then 1 else 0 := by
  classical
  have h : (value code = conclusion + 1) ↔ Code254Proof.check code conclusion = true := by
    have hd := (check_defined (V := Nat)).df ![code, conclusion]
    change checkDef.val.Evalb ![code, conclusion] ↔ value code = conclusion + 1 at hd
    exact hd.symm.trans (checkDef_nat code conclusion)
  simp only [checkValue, h]

/-- The literal fixed object-language sentence asserting unique Boolean
evaluation for all proof codes and requested conclusions. -/
def totalitySentence : ArithmeticSentence :=
  “∀ code, ∀ conclusion, ∃ b,
    !checkValueDef b code conclusion ∧ (b = 0 ∨ b = 1) ∧
    ∀ other, !checkValueDef other code conclusion → other = b”

theorem totalitySentence_true : totalitySentence.Evalb (M := V) ![] := by
  simp [totalitySentence, checkValue_range]

/-- This is actual arithmetic derivability of the SAME fixed totality
sentence. It is not the internal native/ZFC or machine proof translation. -/
theorem isigma1_proves_totality : 𝗜𝚺₁ ⊢ totalitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (totalitySentence_true (V := M))

theorem peano_proves_totality : Peano ⊢ totalitySentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_totality

end SetTheory.BusyBeaver.ZFC.ArithmeticHistory254
