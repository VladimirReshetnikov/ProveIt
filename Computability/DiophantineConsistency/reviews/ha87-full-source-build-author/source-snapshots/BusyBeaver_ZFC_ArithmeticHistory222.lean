import BusyBeaver.ZFC.ArithmeticRow222
import BusyBeaver.ZFC.ArithmeticSequenceHistory

set_option autoImplicit false
set_option Elab.async false

/-! The fixed represented evaluator for the actual C222 row. The generic
append-history supplies primitive recursion; only the actual row selection
and its child lookups are instantiated here. All indices range over an
arbitrary IΣ1 model. No seed validity or machine runtime is assumed. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticHistory222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive code `raw + 1` uses the predecessor's base-12 tag and payload.
GEN reads the whole tail; MP reads its two components. -/
noncomputable def positiveStep (s raw : V) : V :=
  let k := raw % 12
  let p := raw / 12
  let t := second p
  ArithmeticRow222.rowKernel k p
    (if k = 2 then znth s t else znth s (first t)) (znth s (second t))

/-- One fixed syntactic graph, independent of the ambient model. -/
def positiveStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s raw. ∃ k, !remDef k raw 12 ∧ ∃ p, !divDef p raw 12 ∧
    ∃ t, !ArithmeticCantor.secondDef t p ∧
    ∃ b, !ArithmeticCantor.firstDef b t ∧
    ∃ c, !ArithmeticCantor.secondDef c t ∧
    ∃ u, ((k = 2 ∧ !znthDef u s t) ∨ (k ≠ 2 ∧ !znthDef u s b)) ∧
    ∃ v, !znthDef v s c ∧ !ArithmeticRow222.rowDef r k p u v”

instance positiveStep_defined : 𝚺₁-Function₂[V] positiveStep via positiveStepDef :=
  .mk fun e => by
    classical
    by_cases h : e 2 % 12 = 2 <;>
      simp [positiveStepDef, positiveStep, numeral_eq_natCast, h]

noncomputable def stepValue (s code : V) : V := by
  classical
  exact if code = 0 then 0 else positiveStep s (code - 1)

def stepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s code. (code = 0 ∧ r = 0) ∨
    (∃ raw <⁺ code, code = raw + 1 ∧ !positiveStepDef r s raw)”

instance step_defined : 𝚺₁-Function₂[V] stepValue via stepDef := .mk fun e => by
  classical
  simp [stepDef]
  rw [ArithmeticRow254.predecessor_witness]
  by_cases h : e 2 = 0 <;> simp [stepValue, h]

@[simp] theorem stepValue_zero (s : V) : stepValue s 0 = 0 := by
  simp [stepValue]

@[simp] theorem stepValue_succ (s raw : V) : stepValue s (raw + 1) = positiveStep s raw := by
  simp [stepValue]

/-- The actual evaluator delegates to the already checked generic history;
it does not reuse the old C254 history or its semantic theorems. -/
noncomputable def history : V → V := ArithmeticSequenceHistory.history stepDef stepValue

def historyDef : 𝚺₁.Semisentence 2 := ArithmeticSequenceHistory.historyDef stepDef
def historyDeltaDef : 𝚫₁.Semisentence 2 := ArithmeticSequenceHistory.historyDeltaDef stepDef

instance history_defined : 𝚺₁-Function₁[V] history via historyDef :=
  ArithmeticSequenceHistory.history_defined stepDef stepValue

instance history_defined_delta : 𝚫₁-Function₁[V] history via historyDeltaDef :=
  ArithmeticSequenceHistory.history_defined_delta stepDef stepValue

instance history_definable : 𝚺₁-Function₁[V] history := history_defined.to_definable

noncomputable def value : V → V := ArithmeticSequenceHistory.value stepDef stepValue

def valueDef : 𝚺₁.Semisentence 2 := ArithmeticSequenceHistory.valueDef stepDef
def valueDeltaDef : 𝚫₁.Semisentence 2 := ArithmeticSequenceHistory.valueDeltaDef stepDef

instance value_defined : 𝚺₁-Function₁[V] value via valueDef :=
  ArithmeticSequenceHistory.value_defined stepDef stepValue

instance value_defined_delta : 𝚫₁-Function₁[V] value via valueDeltaDef :=
  ArithmeticSequenceHistory.value_defined_delta stepDef stepValue

instance value_definable : 𝚺₁-Function₁[V] value := value_defined.to_definable

@[simp] theorem history_zero : history (0 : V) = seqCons ∅ 0 :=
  ArithmeticSequenceHistory.history_zero stepDef stepValue

theorem history_succ (raw : V) :
    history (raw + 1) = seqCons (history raw) (positiveStep (history raw) raw) := by
  exact (ArithmeticSequenceHistory.history_succ stepDef stepValue raw).trans
    (congrArg (seqCons (history raw)) (stepValue_succ (history raw) raw))

theorem history_seq (code : V) : Seq (history code) :=
  ArithmeticSequenceHistory.history_seq stepDef stepValue code

theorem history_length (code : V) : lh (history code) = code + 1 :=
  ArithmeticSequenceHistory.history_length stepDef stepValue code

theorem history_total (code : V) : ∃! s, historyDef.val.Evalb ![s, code] :=
  ArithmeticSequenceHistory.history_total stepDef stepValue code

theorem value_total (code : V) : ∃! r, valueDef.val.Evalb ![r, code] :=
  ArithmeticSequenceHistory.value_total stepDef stepValue code

theorem value_mem (code : V) : ⟪code, value code⟫ ∈ history code :=
  ArithmeticSequenceHistory.value_mem stepDef stepValue code

theorem value_lt_history (code : V) : value code < history code :=
  ArithmeticSequenceHistory.value_lt_history stepDef stepValue code

@[simp] theorem value_zero : value (0 : V) = 0 :=
  ArithmeticSequenceHistory.value_zero stepDef stepValue

theorem history_lookup_le (code i : V) (hi : i ≤ code) :
    znth (history code) i = value i :=
  ArithmeticSequenceHistory.history_lookup_le stepDef stepValue code i hi

theorem history_lookup (code i : V) :
    znth (history code) i = if i ≤ code then value i else 0 :=
  ArithmeticSequenceHistory.history_lookup stepDef stepValue code i

/-- All child positions precede the positive parent code, including when
the predecessor or payload is zero. -/
theorem quotient_le (raw : V) : raw / 12 ≤ raw := Arithmetic.div_le raw 12

theorem tail_le (raw : V) : second (raw / 12) ≤ raw :=
  le_trans (projections_spec (raw / 12)).2.1 (quotient_le raw)

theorem minor_le (raw : V) : first (second (raw / 12)) ≤ raw :=
  le_trans (projections_spec (second (raw / 12))).1 (tail_le raw)

theorem major_le (raw : V) : second (second (raw / 12)) ≤ raw :=
  le_trans (projections_spec (second (raw / 12))).2.1 (tail_le raw)

theorem value_succ_step (raw : V) :
    value (raw + 1) = positiveStep (history raw) raw :=
  (ArithmeticSequenceHistory.value_succ stepDef stepValue raw).trans
    (stepValue_succ (history raw) raw)

/-- The full actual C222 recurrence at every internal code: child results
are the values of this evaluator, not supplied proof-validity premises. -/
theorem value_succ (raw : V) :
    value (raw + 1) = ArithmeticRow222.rowKernel (raw % 12) (raw / 12)
      (if raw % 12 = 2 then value (second (raw / 12))
       else value (first (second (raw / 12))))
      (value (second (second (raw / 12)))) := by
  rw [value_succ_step]
  unfold positiveStep
  dsimp only
  rw [history_lookup_le raw _ (tail_le raw),
      history_lookup_le raw _ (minor_le raw), history_lookup_le raw _ (major_le raw)]

/-- Acceptance is a fixed graph relation. No soundness or validity assertion
for C222 seeds is used to represent it. -/
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

theorem checkValue_total (code conclusion : V) :
    ∃! b, checkValueDef.val.Evalb ![b, code, conclusion] := by
  simp

theorem checkValue_range (code conclusion : V) :
    checkValue code conclusion = 0 ∨ checkValue code conclusion = 1 := by
  classical
  by_cases h : value code = conclusion + 1 <;> simp [checkValue, h]

/-- A closed IΣ1 theorem about total unique Boolean evaluation, not an
assertion that any accepted seed is internally valid or that a machine runs. -/
def totalitySentence : ArithmeticSentence :=
  “∀ code, ∀ conclusion, ∃ b, !checkValueDef b code conclusion ∧ (b = 0 ∨ b = 1) ∧
    ∀ other, !checkValueDef other code conclusion → other = b”

theorem totalitySentence_true : totalitySentence.Evalb (M := V) ![] := by
  simp [totalitySentence, checkValue_range]

theorem isigma1_proves_totality : 𝗜𝚺₁ ⊢ totalitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (totalitySentence_true (V := M))

end SetTheory.BusyBeaver.ZFC.ArithmeticHistory222
