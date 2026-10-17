import BusyBeaver.ZFC.ArithmeticProofWordCorrect254

/-!
A represented halting word for every internal accepted proof of code1.
The initial AX command resets D/H before the compiler's all-input contract;
the literal terminator halts after a successful falsity conclusion. Every
initial working-state code is covered by the exact Cantor projections.
No scheduler, binary execution, or PA consistency equivalence is claimed.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandRun254
open ArithmeticCommandAppend254 ArithmeticCommandExecution254
open ArithmeticCommandBlockExecution254 ArithmeticCommandRuleExecution254
open ArithmeticProofWord254 ArithmeticProofWordContract254 ArithmeticProofWordCorrect254
open ArithmeticCommandBlocks254 (Circuit)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- This is exactly AX(0,1,1,0), followed by the compiled proof and the
original DROP0,NIP0,NIP0 terminator. It has no validity-dependent branch. -/
noncomputable def refutationWord (code : V) : V :=
  axWord 0 1 1 0 (appendValue (rawWord code) terminatorWord)

def resetCircuit : Circuit := Circuit.consAx .zero .one .one .zero .input0

lemma resetCircuit_eval (rest : V) :
    resetCircuit.eval rest 0 0 0 = axWord 0 1 1 0 rest := by
  simp only [resetCircuit, circuit_consAx, Circuit.eval_zero, Circuit.eval_one,
    Circuit.eval_input0]

/-- One fixed Sigma1 graph; the circuit graphs are fixed finite syntax.
Intermediate word witnesses are unbounded, including for invalid proof codes. -/
def refutationWordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out code. ∃ proofWord, !rawWordDef proofWord code ∧
    ∃ last, !(Circuit.terminator.graph) last 0 0 0 0 ∧
    ∃ suffix, !appendDef suffix proofWord last ∧
    !(resetCircuit.graph) out suffix 0 0 0”

instance refutationWord_defined : 𝚺₁-Function₁[V] refutationWord via refutationWordDef :=
  .mk fun e => by
    simp [refutationWordDef, refutationWord, circuit_terminator, resetCircuit_eval]

instance refutationWord_definable : 𝚺₁-Function₁[V] refutationWord :=
  refutationWord_defined.to_definable

theorem refutationWord_total (code : V) :
    ∃! word, refutationWordDef.val.Evalb ![word,code] := by simp

lemma refutationWord_ne_zero (code : V) : refutationWord code ≠ 0 := by
  simp [refutationWord, axWord]

/-- The first NIP loads code1, and the second tests that exact cache value. -/
theorem eval_terminator_falsity (stack : V) :
    evalValue terminatorWord (stateValue 1 stack 0 0) = 0 := by
  simp [terminatorWord, eval_drop, eval_nip]

/-- Accepted result2 is exactly conclusion1 plus the validity marker. -/
theorem proof_then_terminator (code top stack : V)
    (hv : ArithmeticHistory254.value code = 2) :
    evalValue (appendValue (rawWord code) terminatorWord)
      (stateValue top stack 0 0) = 0 := by
  have hn : ArithmeticHistory254.value code ≠ 0 := by rw [hv]; simp
  have hc := accepted_contract code hn
  have ht : ArithmeticHistory254.value code - 1 = (1 : V) := by
    rw [hv, ← one_add_one_eq_two]
    simp
  rw [ht] at hc
  rcases hc top stack with hh | hs
  · exact eval_append_halt _ _ _ hh
  · rw [eval_append_success _ _ _ _ hs]
    exact eval_terminator_falsity stack

/-- The actual AX prefix clears D/H while retaining arbitrary internal data
as its new top and stack. The subsequent contract accepts all such values. -/
theorem eval_refutationWord_state (code top stack d h : V)
    (hv : ArithmeticHistory254.value code = 2) :
    evalValue (refutationWord code) (stateValue top stack d h) = 0 := by
  rw [refutationWord, eval_ax]
  exact proof_then_terminator code _ _ hv

lemma stateValue_projections (w : V) :
    stateValue (first w) (first (second w))
      (first (second (second w))) (second (second (second w))) = w := by
  simp only [stateValue, cantor_projections]

/-- Every internal working-state code, including nonstandard ones, is covered. -/
theorem eval_refutationWord (code w : V)
    (hv : ArithmeticHistory254.value code = 2) :
    evalValue (refutationWord code) w = 0 := by
  rw [← stateValue_projections w]
  exact eval_refutationWord_state code _ _ _ _ hv

/-- An explicit closed word witness, with its represented graph retained. -/
theorem represented_refutation (code : V)
    (hv : ArithmeticHistory254.value code = 2) :
    ∃ word, refutationWordDef.val.Evalb ![word,code] ∧ word ≠ 0 ∧
      ∀ w, evalValue word w = 0 :=
  ⟨refutationWord code, by simp, refutationWord_ne_zero code,
    fun w => eval_refutationWord code w hv⟩

theorem refutation_exists (code : V)
    (hv : ArithmeticHistory254.value code = 2) :
    ∃ word : V, ∀ w : V, evalValue word w = 0 :=
  ⟨refutationWord code, fun w => eval_refutationWord code w hv⟩

end SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254
