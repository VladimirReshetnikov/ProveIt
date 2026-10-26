import BusyBeaver.ZFC.ArithmeticHistory222

set_option autoImplicit false
set_option Elab.async false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticHistory222Checks

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticHistory222 ArithmeticCantor

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚺₁-Function₂[V] positiveStep via positiveStepDef := inferInstance
example : 𝚺₁-Function₂[V] stepValue via stepDef := inferInstance
example : 𝚫₁-Function₁[V] history via historyDeltaDef := inferInstance
example : 𝚫₁-Function₁[V] value via valueDeltaDef := inferInstance
example : 𝚫₁-Function₂[V] checkValue via checkValueDeltaDef := inferInstance

example (s : V) : stepValue s 0 = 0 := stepValue_zero s
example (s raw : V) : stepValue s (raw + 1) = positiveStep s raw := stepValue_succ s raw
example : value (0 : V) = 0 := value_zero
example (code : V) : ∃! r, valueDef.val.Evalb ![r, code] := value_total code
example (code : V) : Seq (history code) ∧ lh (history code) = code + 1 :=
  ⟨history_seq code, history_length code⟩
example (code i : V) (hi : code < i) : znth (history code) i = 0 := by
  rw [history_lookup, if_neg (not_le_of_gt hi)]
example (raw : V) : second (raw / 12) < raw + 1 ∧
    first (second (raw / 12)) < raw + 1 ∧ second (second (raw / 12)) < raw + 1 :=
  ⟨lt_succ_iff_le.mpr (tail_le raw), lt_succ_iff_le.mpr (minor_le raw),
    lt_succ_iff_le.mpr (major_le raw)⟩
example (raw : V) : value (raw + 1) = ArithmeticRow222.rowKernel (raw % 12) (raw / 12)
    (if raw % 12 = 2 then value (second (raw / 12))
      else value (first (second (raw / 12))))
    (value (second (second (raw / 12)))) := value_succ raw
example (code conclusion : V) : ∃! b, checkValueDef.val.Evalb ![b, code, conclusion] :=
  checkValue_total code conclusion
example : 𝗜𝚺₁ ⊢ totalitySentence := isigma1_proves_totality

#print axioms positiveStep_defined
#print axioms step_defined
#print axioms history_defined_delta
#print axioms value_defined_delta
#print axioms history_total
#print axioms value_total
#print axioms history_seq
#print axioms history_length
#print axioms history_lookup
#print axioms value_succ
#print axioms checkValue_defined_delta
#print axioms checkValue_total
#print axioms totalitySentence_true
#print axioms isigma1_proves_totality

end SetTheory.BusyBeaver.ZFC.ArithmeticHistory222Checks
