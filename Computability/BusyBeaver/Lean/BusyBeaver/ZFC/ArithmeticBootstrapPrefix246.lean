import BusyBeaver.ZFC.ArithmeticMachineRunPrefix246
import BusyBeaver.ZFC.ArithmeticBootstrapPerm252
import BusyBeaver.ZFC.BootPrefix246Chunk008

/-!
Transport the exact checked 410,735-step contextual-fold246 startup into
all IΣ1 models through the fixed represented exact246 run graph. Reuse only
the generic numeric zipper uniqueness lemma from the earlier252 transport;
the concrete table, startup target and run function here are the246 ones.
This proves the finite arithmetic startup sentence, not the remaining
unbounded register simulation or internal consistency equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252
open ArithmeticMachineStepPerm252 (encodeConfig)
open ArithmeticBootstrapPerm252 (numericRun_of_zipRep)
open ArithmeticMachineRunPrefix246

/-- The complete numeric boot tape is inherited from the literal target. -/
def bootCode : Nat := encodeConfig (encodeZip BootPrefix246Probe16384.finish)

theorem standard_boot : run (410735 : Nat) = bootCode := by
  rw [run_nat, numericRun_of_zipRep machinePrefix246 410735
    BootPrefix246Probe16384.finish BootPrefix246Chunk008.bootstrap410735]
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For each external natural time, the same fixed graph gives the same
numeral result in every model. This does not cover arbitrary internal times. -/
theorem run_cast (time : Nat) : run (time : V) = ((run time : Nat) : V) := by
  have h := DefinedFunction.shigmaOne_absolute_func V
    (run_defined (V := Nat)) (run_defined (V := V)) ![time]
  simpa only [Function.comp_apply, Matrix.cons_val_zero] using h.symm

/-- The exact checked finite prefix, lifted to every arithmetic model. -/
theorem internal_boot : run (410735 : V) = (bootCode : V) := by
  simpa only [Nat.cast_ofNat, standard_boot] using run_cast (V := V) 410735

/-- Keep numeral evaluation generic before specializing the large tape code. -/
def runEquationSentence (out time : Nat) : 𝚺₁.Sentence := .mkSigma
  “!ArithmeticMachineRunPrefix246.runDef
    !!(Semiterm.Operator.numeral ℒₒᵣ out)
    !!(Semiterm.Operator.numeral ℒₒᵣ time)”

theorem runEquationSentence_eval (out time : Nat) :
    (runEquationSentence out time).val.Evalb (M := V) ![] ↔
      (out : V) = run (time : V) := by
  simp [runEquationSentence, numeral_eq_natCast]

def bootstrapSentence : 𝚺₁.Sentence := runEquationSentence bootCode 410735

theorem bootstrapSentence_true : bootstrapSentence.val.Evalb (M := V) ![] :=
  (runEquationSentence_eval bootCode 410735).mpr (internal_boot (V := V)).symm

theorem isigma1_proves_bootstrap : 𝗜𝚺₁ ⊢ bootstrapSentence.val := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (bootstrapSentence_true (V := M))

theorem peano_proves_bootstrap : Peano ⊢ bootstrapSentence.val :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_bootstrap

end SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPrefix246
