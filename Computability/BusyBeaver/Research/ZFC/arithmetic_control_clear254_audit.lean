import BusyBeaver.ZFC.ArithmeticControlClear254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlClear254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFrame254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.write_overwrite
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.clear_cycle
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.clear_exit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.clear_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.literal_test_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.literal_again_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.literal_exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.literalClear
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254.literal_clear_run

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (file x y : V) (p : Fin 9) :
    writeValue (p.val : V) y (writeValue (p.val : V) x file)=writeValue (p.val : V) y file :=
  write_overwrite file x y p
example (c : ClearShape) (file : V)
    (hn : regValue file (SitePerm252.physical c.register.val c.register.isLt)≠0) :
    ArithmeticControlStep254.stepValue
      (ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file))=
      liveValue (number c.test : V)
        (writeValue ((Permutation252Frame.physOf c.register.val : Nat) : V)
          (regValue file (SitePerm252.physical c.register.val c.register.isLt)-1) file) :=
  clear_cycle c file hn
example (c : ClearShape) (file : V)
    (hz : regValue file (SitePerm252.physical c.register.val c.register.isLt)=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) file := clear_exit c file hz
example (c : ClearShape) (file : V) :
    controlRun (2*regValue file (SitePerm252.physical c.register.val c.register.isLt)+1)
      (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V)
        (writeValue ((Permutation252Frame.physOf c.register.val : Nat) : V) 0 file) :=
  clear_run c file
example : source literalTest=(literalParent++[false],.decnz 5) := literal_test_source
example : source literalAgain=(literalParent++[true],.cont 1) := literal_again_source
example : source literalExit=([true,true,true,true,true,false,true,true,true],.brk 1) :=
  literal_exit_source
example : literalClear.test=literalTest ∧ literalClear.again=literalAgain ∧
    literalClear.exit=literalExit := ⟨rfl,rfl,rfl⟩
example (file : V) :
    controlRun (2*regValue file (7 : Fin 9)+1) (liveValue (number literalTest : V) file)=
      liveValue (number literalExit : V) (writeValue (7 : V) 0 file) := literal_clear_run file
example : controlRun (1 : V) (liveValue (number literalTest : V) 0)=
    liveValue (number literalExit : V) 0 := by
  have hz : regValue (0 : V) (7 : Fin 9)=0 := projection_zero 8 7
  have h := literal_clear_run (0 : V)
  rw [hz,mul_zero,zero_add] at h
  have hw := write_same (0 : V) (7 : Fin 9)
  rw [hz] at hw
  change writeValue ((7 : Nat) : V) 0 0=0 at hw
  simp only [Nat.cast_ofNat] at hw
  rw [hw] at h
  exact h
example (file : V) (hvalue : regValue file (7 : Fin 9)=1) :
    controlRun (3 : V) (liveValue (number literalTest : V) file)=
      liveValue (number literalExit : V) (writeValue (7 : V) 0 file) := by
  have h := literal_clear_run file
  rw [hvalue,show 2*(1 : V)+1=3 by ring] at h
  exact h
