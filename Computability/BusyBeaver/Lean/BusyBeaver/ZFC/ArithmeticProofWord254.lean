import BusyBeaver.ZFC.ArithmeticProofWordRow254
import BusyBeaver.ZFC.ArithmeticHistoryRecurrence254

/-!
Independent unconditional raw-word history followed by ONE public gate from
the unchanged actual C254 validator. Word0 is empty, raw command0 is MP0,
and proof code0 is invalid: the three conventions remain distinct.

The graph and internal recurrence are data operations; a later
validity-conditional execution induction and PA consistency transport remain
separate. This module does not inspect a Prop-valued derivation or decode a
finite proof tree to define its internal-model functions.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticProofWordRow254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Raw proof predecessor selects tag/payload; tag2 reads its WHOLE-tail
child. MP reads the two components of that tail. -/
noncomputable def positiveStep (previous raw : V) : V :=
  let tag := raw % 12
  let payload := raw / 12
  let t := second payload
  rowValue tag payload (if tag = 2 then znth previous t else znth previous (first t))
    (znth previous (second t))

def positiveStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out previous raw. ∃ tag, !remDef tag raw 12 ∧
    ∃ payload, !divDef payload raw 12 ∧
    ∃ t, !ArithmeticCantor.secondDef t payload ∧
    ∃ b, !ArithmeticCantor.firstDef b t ∧
    ∃ c, !ArithmeticCantor.secondDef c t ∧
    ∃ u, ((tag = 2 ∧ !znthDef u previous t) ∨ (tag ≠ 2 ∧ !znthDef u previous b)) ∧
    ∃ v, !znthDef v previous c ∧ !ArithmeticProofWordRow254.rowDef out tag payload u v”

instance positiveStep_defined : 𝚺₁-Function₂[V] positiveStep via positiveStepDef :=
  .mk fun e => by
    classical
    by_cases h : e 2 % 12 = 2 <;> simp [positiveStepDef, positiveStep, numeral_eq_natCast, h]

def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “s. !mkSeq₁Def s 0”

/-- The PR index already is raw=proofCode-1. The positive step must not
subtract again, and it is not the shifted command-word append index. -/
def succDef : 𝚺₁.Semisentence 3 := .mkSigma
  “s previous index. ∃ word, !positiveStepDef word previous index ∧ !seqConsDef s previous word”

def blueprint : PR.Blueprint 0 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := seqCons ∅ 0
  succ _ index previous := seqCons previous (positiveStep previous index)
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

noncomputable def history (code : V) : V := construction.result ![] code

def historyDef : 𝚺₁.Semisentence 2 := blueprint.resultDef

def historyDeltaDef : 𝚫₁.Semisentence 2 := blueprint.resultDeltaDef

instance history_defined : 𝚺₁-Function₁[V] history via historyDef := .mk fun e => by
  have he : (fun i : Fin 0 => e i.succ.succ) = ![] := Subsingleton.elim _ _
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0 = construction.result (fun i : Fin 0 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change blueprint.resultDef.val.Evalb e ↔ e 0 = construction.result ![] (e 1)
  exact h

instance history_defined_delta : 𝚫₁-Function₁[V] history via historyDeltaDef := history_defined.graph_delta
instance history_definable : 𝚺₁-Function₁[V] history := history_defined.to_definable

@[simp] theorem history_zero : history (0 : V) = seqCons ∅ 0 := by
  simp [history, construction]

@[simp] theorem history_succ (code : V) :
    history (code+1) = seqCons (history code) (positiveStep (history code) code) := by
  simp [history, PR.Construction.result_succ, construction]

theorem history_seq (code : V) : Seq (history code) := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih => rw [history_succ]; exact ih.seqCons _

theorem history_length (code : V) : lh (history code) = code+1 := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih => rw [history_succ, (history_seq code).lh_seqCons, ih]

noncomputable def rawWord (code : V) : V := znth (history code) code

def rawWordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out code. ∃ s, !historyDef s code ∧ !znthDef out s code”

instance rawWord_defined : 𝚺₁-Function₁[V] rawWord via rawWordDef :=
  .mk fun e => by simp [rawWordDef, rawWord]

def rawWordDeltaDef : 𝚫₁.Semisentence 2 := rawWordDef.graphDelta
instance rawWord_defined_delta : 𝚫₁-Function₁[V] rawWord via rawWordDeltaDef := rawWord_defined.graph_delta
instance rawWord_definable : 𝚺₁-Function₁[V] rawWord := rawWord_defined.to_definable

@[simp] theorem rawWord_zero : rawWord (0 : V) = 0 := by
  rw [rawWord, history_zero]
  simpa only [lh_empty] using
    ArithmeticCommandAppend254.znth_append_last (seq_empty (V := V)) (0 : V)

/-- The induction quantifier is bounded; no unbounded contract hypothesis
has been smuggled into Sigma1 induction. -/
theorem history_lookup_le (code : V) :
    ∀ i ≤ code, znth (history code) i = rawWord i := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro i hi
    have hi0 : i = 0 := le_antisymm hi (by simp)
    subst i
    rfl
  case succ code ih =>
    intro i hi
    by_cases he : i = code+1
    · subst i; rfl
    · have hilt : i < code+1 := lt_of_le_of_ne hi he
      have hile : i ≤ code := lt_succ_iff_le.mp hilt
      rw [history_succ, ArithmeticCommandAppend254.znth_append_old (history_seq code) _ i
        (by simpa only [history_length] using hilt)]
      exact ih i hile

theorem history_lookup (code i : V) :
    znth (history code) i = if i ≤ code then rawWord i else 0 := by
  classical
  by_cases hi : i ≤ code
  · simp only [hi, if_pos]; exact history_lookup_le code i hi
  · simp only [hi, if_false]
    apply znth_prop_not
    right
    rw [history_length]
    exact lt_iff_succ_le.mp (lt_of_not_ge hi)

/-- Exact course-of-values recurrence, with all source child indices retained. -/
theorem rawWord_succ (raw : V) :
    rawWord (raw+1) = rowValue (raw % 12) (raw / 12)
      (if raw % 12 = 2 then rawWord (second (raw / 12))
       else rawWord (first (second (raw / 12))))
      (rawWord (second (second (raw / 12)))) := by
  have hs : rawWord (raw+1) = positiveStep (history raw) raw := by
    unfold rawWord
    rw [history_succ]
    simpa only [history_length] using
      ArithmeticCommandAppend254.znth_append_last (history_seq raw) (positiveStep (history raw) raw)
  rw [hs]
  unfold positiveStep
  dsimp only
  rw [history_lookup_le raw _ (ArithmeticHistoryRecurrence254.tail_le raw),
      history_lookup_le raw _ (ArithmeticHistoryRecurrence254.minor_le raw),
      history_lookup_le raw _ (ArithmeticHistoryRecurrence254.major_le raw)]

/-- The single PUBLIC validity gate uses the existing twelve-case validator.
Unconditional words at rejected nodes have no execution contract. -/
noncomputable def compiledWord (code : V) : V := by
  classical
  exact if ArithmeticHistory254.value code = 0 then 0 else rawWord code

def compiledWordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out code. ∃ valid, !ArithmeticHistory254.valueDef valid code ∧
    ((valid = 0 ∧ out = 0) ∨ (valid ≠ 0 ∧ !rawWordDef out code))”

instance compiledWord_defined : 𝚺₁-Function₁[V] compiledWord via compiledWordDef :=
  .mk fun e => by
    classical
    by_cases h : ArithmeticHistory254.value (e 1) = 0 <;> simp [compiledWordDef, compiledWord, h]

def compiledWordDeltaDef : 𝚫₁.Semisentence 2 := compiledWordDef.graphDelta
instance compiledWord_defined_delta : 𝚫₁-Function₁[V] compiledWord via compiledWordDeltaDef := compiledWord_defined.graph_delta

theorem compiledWord_invalid (code : V) (h : ArithmeticHistory254.value code = 0) :
    compiledWord code = 0 := by simp [compiledWord, h]

theorem compiledWord_valid (code : V) (h : ArithmeticHistory254.value code ≠ 0) :
    compiledWord code = rawWord code := by simp [compiledWord, h]

@[simp] theorem compiledWord_zero : compiledWord (0 : V) = 0 := by simp [compiledWord]

theorem history_total (code : V) : ∃! s, historyDef.val.Evalb ![s,code] := by simp

theorem rawWord_total (code : V) : ∃! word, rawWordDef.val.Evalb ![word,code] := by simp

theorem compiledWord_total (code : V) : ∃! word, compiledWordDef.val.Evalb ![word,code] := by simp

/-- This standard-Nat adapter covers the validity gate only; it does not
replace the separate rawWord-versus-structural-compiler proof. -/
theorem compiledWord_nat_gate (code : Nat) :
    compiledWord code = if Code254History.value code = 0 then 0 else rawWord code := by
  classical
  simp only [compiledWord, ArithmeticHistory254.value_nat]

def totalitySentence : ArithmeticSentence :=
  “∀ code, ∃ word, !compiledWordDef word code ∧
    ∀ other, !compiledWordDef other code → other = word”

theorem totalitySentence_true : totalitySentence.Evalb (M := V) ![] := by simp [totalitySentence]

theorem isigma1_proves_totality : 𝗜𝚺₁ ⊢ totalitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (totalitySentence_true (V := M))

theorem peano_proves_totality : Peano ⊢ totalitySentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_totality

end SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254
