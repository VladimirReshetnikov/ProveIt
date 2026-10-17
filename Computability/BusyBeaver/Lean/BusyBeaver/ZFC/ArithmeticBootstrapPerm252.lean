import BusyBeaver.ZFC.ArithmeticMachineRunPerm252
import BusyBeaver.ZFC.BootPerm252
import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness

/-!
Transport the already checked full 82,552-step bootstrap into every IΣ1
model. Numeric tape codes are unique for a whole Core configuration, despite
irrelevant trailing zero cells in finite zipper lists. The fixed run graph
then transfers the standard finite result by Sigma1 upward absoluteness.
No bootstrap simulation is recomputed and no unbounded runtime is inferred.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open FiniteZipper ArithmeticMachinePerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

lemma bitsCode_zero_of_blank (xs : List Bool)
    (h : ∀ i, xs.getD i false = false) : bitsCode xs = 0 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have hb : b = false := h 0
    have ht : ∀ i, xs.getD i false = false := fun i => h (i+1)
    simp only [bitsCode, hb, Bool.toNat_false, ih ht, Nat.mul_zero, Nat.add_zero]

/-- Zero exterior, rather than list length, determines the numeric tape. -/
lemma bitsCode_ext (xs ys : List Bool)
    (h : ∀ i, xs.getD i false = ys.getD i false) : bitsCode xs = bitsCode ys := by
  induction xs generalizing ys with
  | nil =>
    exact (bitsCode_zero_of_blank ys (fun i => (h i).symm)).symm
  | cons b xs ih =>
    cases ys with
    | nil => exact bitsCode_zero_of_blank (b::xs) h
    | cons c ys =>
      have hb : b = c := h 0
      have ht : ∀ i, xs.getD i false = ys.getD i false := fun i => h (i+1)
      simp only [bitsCode, hb, ih ys ht]

lemma encodeZip_unique {n : Nat} {c : Config n} {z z' : ZipConfig n}
    (hz : ZipRep c z) (hz' : ZipRep c z') : encodeZip z = encodeZip z' := by
  have hs : z.state = z'.state := hz.1.symm.trans hz'.1
  have hh : z.head = z'.head := hz.2.1.symm.trans hz'.2.1
  have hl : bitsCode z.left = bitsCode z'.left := bitsCode_ext _ _ (by
    intro i
    rw [← hz.2.2.1 i, ← hz'.2.2.1 i, hh])
  have hr : bitsCode z.right = bitsCode z'.right := bitsCode_ext _ _ (by
    intro i
    rw [← hz.2.2.2 i, ← hz'.2.2.2 i, hh])
  simp only [encodeZip, hs, hl, hr]

lemma numericRun_of_zipRep {n : Nat} (M : Machine n) (time : Nat)
    (z : ZipConfig n) (hz : ZipRep (M.run time) z) : numericRun M time = encodeZip z := by
  obtain ⟨z', hz', hu, _⟩ := numericRun_sound M time
  exact hu.symm.trans (encodeZip_unique hz' hz)

/-- The complete numeric boot tape is inherited from the literal target. -/
def bootCode : Nat := encodeConfig (encodeZip BootPerm252.bootTargetPerm252)

theorem standard_boot : run (82552 : Nat) = bootCode := by
  rw [run_nat, numericRun_of_zipRep machinePerm252 82552
    BootPerm252.bootTargetPerm252 BootPerm252.fullBootstrapPerm252]
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For each external natural time, the same fixed graph gives the same
numeral result in every model. This does not cover arbitrary internal times. -/
theorem run_cast (time : Nat) : run (time : V) = ((run time : Nat) : V) := by
  have h := DefinedFunction.shigmaOne_absolute_func V
    (run_defined (V := Nat)) (run_defined (V := V)) ![time]
  simpa only [Function.comp_apply, Matrix.cons_val_zero] using h.symm

/-- The exact checked finite prefix, lifted to every arithmetic model. -/
theorem internal_boot : run (82552 : V) = (bootCode : V) := by
  simpa only [Nat.cast_ofNat, standard_boot] using run_cast (V := V) 82552

/-- Keep numeral evaluation generic before specializing the large tape code. -/
def runEquationSentence (out time : Nat) : 𝚺₁.Sentence := .mkSigma
  “!ArithmeticMachineRunPerm252.runDef
    !!(Semiterm.Operator.numeral ℒₒᵣ out)
    !!(Semiterm.Operator.numeral ℒₒᵣ time)”

theorem runEquationSentence_eval (out time : Nat) :
    (runEquationSentence out time).val.Evalb (M := V) ![] ↔
      (out : V) = run (time : V) := by
  simp [runEquationSentence, numeral_eq_natCast]

def bootstrapSentence : 𝚺₁.Sentence := runEquationSentence bootCode 82552

theorem bootstrapSentence_true : bootstrapSentence.val.Evalb (M := V) ![] :=
  (runEquationSentence_eval bootCode 82552).mpr (internal_boot (V := V)).symm

theorem isigma1_proves_bootstrap : 𝗜𝚺₁ ⊢ bootstrapSentence.val := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (bootstrapSentence_true (V := M))

theorem peano_proves_bootstrap : Peano ⊢ bootstrapSentence.val :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_bootstrap

end SetTheory.BusyBeaver.ZFC.ArithmeticBootstrapPerm252
