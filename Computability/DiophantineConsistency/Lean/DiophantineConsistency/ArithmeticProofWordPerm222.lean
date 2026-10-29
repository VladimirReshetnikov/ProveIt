import DiophantineConsistency.ArithmeticProofWordRowPerm222
import BusyBeaver.ZFC.ArithmeticHistory222

/-! Represented C222 proof-word history and validity-conditional correctness.
Generic sequence recursion supplies all internal codes; a Pi1 prefix
induction supplies the execution contract over Type0 models. There is no
assumed source-calculus calibration or standard-Nat proof-tree induction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticProofWordPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor

section Graph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive code `raw + 1` uses the predecessor's base-12 tag and payload.
GEN reads the whole tail; MP reads its two components. -/
noncomputable def positiveStep (s raw : V) : V :=
  let k := raw % 12
  let p := raw / 12
  let t := second p
  ArithmeticProofWordRowPerm222.rowValue k p
    (if k = 2 then znth s t else znth s (first t)) (znth s (second t))

/-- One fixed syntactic graph, independent of the ambient model. -/
noncomputable def positiveStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s raw. ∃ k, !remDef k raw 12 ∧ ∃ p, !divDef p raw 12 ∧
    ∃ t, !ArithmeticCantor.secondDef t p ∧
    ∃ b, !ArithmeticCantor.firstDef b t ∧
    ∃ c, !ArithmeticCantor.secondDef c t ∧
    ∃ u, ((k = 2 ∧ !znthDef u s t) ∨ (k ≠ 2 ∧ !znthDef u s b)) ∧
    ∃ v, !znthDef v s c ∧ !ArithmeticProofWordRowPerm222.rowDef r k p u v”

instance positiveStep_defined : 𝚺₁-Function₂[V] positiveStep via positiveStepDef :=
  .mk fun e => by
    classical
    by_cases h : e 2 % 12 = 2 <;>
      simp [positiveStepDef, positiveStep, numeral_eq_natCast, h]

noncomputable def stepValue (s code : V) : V := by
  classical
  exact if code = 0 then 0 else positiveStep s (code - 1)

noncomputable def stepDef : 𝚺₁.Semisentence 3 := .mkSigma
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

noncomputable def historyDef : 𝚺₁.Semisentence 2 := ArithmeticSequenceHistory.historyDef stepDef
noncomputable def historyDeltaDef : 𝚫₁.Semisentence 2 := ArithmeticSequenceHistory.historyDeltaDef stepDef

instance history_defined : 𝚺₁-Function₁[V] history via historyDef :=
  ArithmeticSequenceHistory.history_defined stepDef stepValue

instance history_defined_delta : 𝚫₁-Function₁[V] history via historyDeltaDef :=
  ArithmeticSequenceHistory.history_defined_delta stepDef stepValue

instance history_definable : 𝚺₁-Function₁[V] history := history_defined.to_definable

noncomputable def rawWord : V → V := ArithmeticSequenceHistory.value stepDef stepValue

noncomputable def rawWordDef : 𝚺₁.Semisentence 2 := ArithmeticSequenceHistory.valueDef stepDef
noncomputable def rawWordDeltaDef : 𝚫₁.Semisentence 2 := ArithmeticSequenceHistory.valueDeltaDef stepDef

instance rawWord_defined : 𝚺₁-Function₁[V] rawWord via rawWordDef :=
  ArithmeticSequenceHistory.value_defined stepDef stepValue

instance rawWord_defined_delta : 𝚫₁-Function₁[V] rawWord via rawWordDeltaDef :=
  ArithmeticSequenceHistory.value_defined_delta stepDef stepValue

instance rawWord_definable : 𝚺₁-Function₁[V] rawWord := rawWord_defined.to_definable

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

theorem rawWord_total (code : V) : ∃! r, rawWordDef.val.Evalb ![r, code] :=
  ArithmeticSequenceHistory.value_total stepDef stepValue code

theorem rawWord_mem (code : V) : ⟪code, rawWord code⟫ ∈ history code :=
  ArithmeticSequenceHistory.value_mem stepDef stepValue code

theorem rawWord_lt_history (code : V) : rawWord code < history code :=
  ArithmeticSequenceHistory.value_lt_history stepDef stepValue code

@[simp] theorem rawWord_zero : rawWord (0 : V) = 0 :=
  ArithmeticSequenceHistory.value_zero stepDef stepValue

theorem history_lookup_le (code i : V) (hi : i ≤ code) :
    znth (history code) i = rawWord i :=
  ArithmeticSequenceHistory.history_lookup_le stepDef stepValue code i hi

theorem history_lookup (code i : V) :
    znth (history code) i = if i ≤ code then rawWord i else 0 :=
  ArithmeticSequenceHistory.history_lookup stepDef stepValue code i

theorem rawWord_succ_step (raw : V) :
    rawWord (raw + 1) = positiveStep (history raw) raw :=
  (ArithmeticSequenceHistory.value_succ stepDef stepValue raw).trans
    (stepValue_succ (history raw) raw)

/-- The full actual C222 recurrence at every internal code: child results
are the values of this evaluator, not supplied proof-validity premises. -/
theorem rawWord_succ (raw : V) :
    rawWord (raw + 1) = ArithmeticProofWordRowPerm222.rowValue (raw % 12) (raw / 12)
      (if raw % 12 = 2 then rawWord (second (raw / 12))
       else rawWord (first (second (raw / 12))))
      (rawWord (second (second (raw / 12)))) := by
  rw [rawWord_succ_step]
  unfold positiveStep
  dsimp only
  rw [history_lookup_le raw _ (ArithmeticHistory222.tail_le raw),
      history_lookup_le raw _ (ArithmeticHistory222.minor_le raw), history_lookup_le raw _ (ArithmeticHistory222.major_le raw)]

end Graph

section Correctness
open ArithmeticCommandLeafPerm222 ArithmeticCommandStepPerm222
open ArithmeticCommandAppendPerm222 ArithmeticCommandRunPerm222
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance checker_delta : 𝚫₁-Function₁[V] ArithmeticHistory222.value :=
  ArithmeticHistory222.value_defined_delta.to_definable
private instance rawWord_delta : 𝚫₁-Function₁[V] rawWord := rawWord_defined_delta.to_definable

/-- Invalid codes are vacuous; accepted codes retain the exact conclusion. -/
def Good (code : V) : Prop := ArithmeticHistory222.value code=0 ∨
  Contract (rawWord code) (ArithmeticHistory222.value code-1)
def PrefixGood (code : V) : Prop := ∀ i≤code, Good i

instance good_definable : 𝚷₁-Predicate (Good (V := V)) := by
  unfold Good
  definability
instance prefixGood_definable : 𝚷₁-Predicate (PrefixGood (V := V)) := by
  unfold PrefixGood
  definability

theorem good_zero : Good (0 : V) := Or.inl (by simp)

theorem contract_of_good {code : V} (h : Good code)
    (hv : ArithmeticHistory222.value code≠0) :
    Contract (rawWord code) (ArithmeticHistory222.value code-1) := h.resolve_left hv

/-- Both exact recurrences share the actual child indices. -/
theorem good_succ (raw : V) (hp : PrefixGood raw) : Good (raw+1) := by
  classical
  by_cases hv : ArithmeticHistory222.value (raw+1)=0
  · exact Or.inl hv
  · apply Or.inr
    rw [rawWord_succ,ArithmeticHistory222.value_succ]
    apply ArithmeticProofWordRowPerm222.row_contract
    · intro hu
      by_cases ht : raw%12=2
      · simpa only [if_pos ht] using
          contract_of_good (hp _ (ArithmeticHistory222.tail_le raw))
            (by simpa only [if_pos ht] using hu)
      · simpa only [if_neg ht] using
          contract_of_good (hp _ (ArithmeticHistory222.minor_le raw))
            (by simpa only [if_neg ht] using hu)
    · exact fun hu => contract_of_good (hp _ (ArithmeticHistory222.major_le raw)) hu
    · simpa only [ArithmeticHistory222.value_succ] using hv

/-- Genuine definable internal induction, including nonstandard proof codes. -/
theorem good_all (code : V) : Good code := by
  have hp : PrefixGood code := by
    induction code using ISigma1.pi1_succ_induction
    · exact prefixGood_definable
    case zero =>
      intro i hi
      have hi0 : i=0 := le_antisymm hi (by simp)
      subst i
      exact good_zero
    case succ raw ih =>
      intro i hi
      by_cases he : i=raw+1
      · subst i
        exact good_succ raw ih
      · exact ih i (lt_succ_iff_le.mp (lt_of_le_of_ne hi he))
  exact hp code le_rfl

theorem accepted_contract (code : V) (hv : ArithmeticHistory222.value code≠0) :
    Contract (rawWord code) (ArithmeticHistory222.value code-1) :=
  contract_of_good (good_all code) hv

theorem check_contract {code A : V}
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,A]) : Contract (rawWord code) A := by
  have hv : ArithmeticHistory222.value code=A+1 := by simpa using h
  have hn : ArithmeticHistory222.value code≠0 := by rw [hv]; simp
  simpa [hv] using accepted_contract code hn

/-- Append the actual conditional false1 terminator, not a false axiom. -/
noncomputable def refutationWord (code : V) : V :=
  appendValue (rawWord code) terminatorWord

noncomputable def refutationWordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “word code. ∃ raw, !rawWordDef raw code ∧ ∃ last,
    !(ArithmeticCommandCircuitPerm222.Circuit.terminator.graph) last 0 0 0 0 ∧
    !ArithmeticCommandAppendPerm222.appendDef word raw last”

instance refutationWord_defined : 𝚺₁-Function₁[V] refutationWord via refutationWordDef :=
  .mk fun e => by
    simp [refutationWordDef,refutationWord,ArithmeticCommandCircuitPerm222.Circuit.eval_terminator]

theorem refutationWord_halts (code : V)
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,1]) (top S : V) :
    evalValue (refutationWord code) (stateValue top S 0 0)=0 :=
  false_target_halts (rawWord code) (check_contract h) top S
end Correctness
end DiophantineConsistency.ArithmeticProofWordPerm222
