import BusyBeaver.ZFC.ArithmeticEnumeratorRun254
import BusyBeaver.ZFC.ArithmeticRefutationWord254

/-!
The forward internal compiler/scheduler direction. In every IΣ1 model,
validator value2 supplies a literal halting word, and the actual arithmetic
scheduler reaches that word or has already halted. Every initial working
state code is allowed; the scheduler starts at pl=np=0.
The one fixed arithmetic sentence below is proved in IΣ1 and hence PA.
It concerns this represented validator and scheduler, not ZFC proof codes,
the binary Turing-machine run, or a PA consistency equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticEnumeratorStep254
open ArithmeticEnumeratorRun254 ArithmeticRefutationWord254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal represented falsity proof, with no standard-code premise. -/
theorem halts_of_accepted (code initialWork : V)
    (hv : ArithmeticHistory254.value code = 2) :
    ∃ time, run time (liveValue 0 0 initialWork) = 0 :=
  halts_of_word (refutationWord code) initialWork (refutationWord_ne_zero code)
    (fun w => eval_refutationWord code w hv)

/-- The full fixed run/start graphs remain explicit in this conclusion. -/
theorem represented_halt (code initialWork : V)
    (hv : ArithmeticHistory254.value code = 2) :
    ∃ initial, liveDef.val.Evalb ![initial,0,0,initialWork] ∧
      ∃ time, runDef.val.Evalb ![0,time,initial] := by
  obtain ⟨time, ht⟩ := halts_of_accepted code initialWork hv
  exact ⟨liveValue 0 0 initialWork, by simp, time, by simpa using ht.symm⟩

/-- The sentence and its graph definitions are fixed before the model is chosen. -/
def forwardSentence : ArithmeticSentence :=
  “∀ code, ∀ w, !ArithmeticHistory254.valueDef 2 code →
    ∃ initial, !ArithmeticEnumeratorStep254.liveDef initial 0 0 w ∧
      ∃ time, !ArithmeticEnumeratorRun254.runDef 0 time initial”

theorem forwardSentence_true : forwardSentence.Evalb (M := V) ![] := by
  simp [forwardSentence]
  intro code w hv
  obtain ⟨time, ht⟩ := halts_of_accepted code w hv.symm
  exact ⟨time, ht.symm⟩

theorem isigma1_proves_forward : 𝗜𝚺₁ ⊢ forwardSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (forwardSentence_true (V := M))

theorem peano_proves_forward : Peano ⊢ forwardSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_forward

end SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254
