import BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254
import BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254

/-!
A fixed arithmetic equivalence between an accepted falsity proof for the
literal C254 validator and halting of its represented scheduler from scalar1.
Both directions hold at arbitrary internal inputs in every IΣ1 model, so
arithmetic completeness gives derivations in IΣ1 and PA of this one sentence.
The sentence does not mention ZFC proof codes or binary machine execution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
open ArithmeticHistory254 (value)
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
open ArithmeticEnumeratorSoundness254 ArithmeticEnumeratorRefutation254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual empty scheduler encoding, in every arithmetic model. -/
lemma blank_live : liveValue (0 : V) 0 0 = 1 := by
  simp [liveValue, cantor, triangle]

/-- All witnesses and run times are internal model elements. -/
theorem accepted_iff_blank_halts :
    (∃ code : V, value code = 2) ↔ (∃ time : V, run time 1 = 0) := by
  constructor
  · rintro ⟨code, hv⟩
    obtain ⟨time, ht⟩ := halts_of_accepted code (0 : V) hv
    exact ⟨time, by simpa only [blank_live] using ht⟩
  · rintro ⟨time, ht⟩
    apply accepted_of_zero_work_run_zero time (0 : V) 0
    simpa only [blank_live] using ht

/-- The fixed graphs are chosen before the model, including the value2
success marker and scalar1 start. -/
def equivalenceSentence : ArithmeticSentence :=
  “(∃ code, !ArithmeticHistory254.valueDef 2 code) ↔
    (∃ time, !ArithmeticEnumeratorRun254.runDef 0 time 1)”

theorem equivalenceSentence_true : equivalenceSentence.Evalb (M := V) ![] := by
  simp [equivalenceSentence]
  constructor
  · rintro ⟨code, hc⟩
    obtain ⟨time, ht⟩ := accepted_iff_blank_halts.mp ⟨code, hc.symm⟩
    exact ⟨time, ht.symm⟩
  · rintro ⟨time, ht⟩
    obtain ⟨code, hc⟩ := accepted_iff_blank_halts.mpr ⟨time, ht.symm⟩
    exact ⟨code, hc.symm⟩

theorem isigma1_proves_equivalence : 𝗜𝚺₁ ⊢ equivalenceSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (equivalenceSentence_true (V := M))

theorem peano_proves_equivalence : Peano ⊢ equivalenceSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_equivalence

end SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254
