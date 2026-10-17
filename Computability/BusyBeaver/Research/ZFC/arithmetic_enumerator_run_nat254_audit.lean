import BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254 ArithmeticEnumeratorRunNat254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.encodeSt_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.encodeResult_eq_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.run_succ_first
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.run_encode_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.runDef_encode_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.run_zero_iff_native_none
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.haltsFrom_of_run_none
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.run_none_of_haltsFrom
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.halts_iff_native
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.encodeSt_s0
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254.blank_halts_iff
example (s : Enum254.St) : encodeSt s ≠ 0 := encodeSt_ne_zero s
example (s : Option Enum254.St) :
    ArithmeticEnumeratorStep254.encodeResult s = 0 ↔ s = none := encodeResult_eq_zero s
example (time initial : Nat) : run (time+1) initial = run time (step initial) :=
  run_succ_first time initial
example (time : Nat) (s : Enum254.St) :
    run time (encodeSt s) = ArithmeticEnumeratorStep254.encodeResult (Enum254.run time s) :=
  run_encode_nat time s
example (time pl np tw ws d h : Nat) :
    run time (encodeSt ⟨pl,np,tw,ws,d,h⟩) =
      ArithmeticEnumeratorStep254.encodeResult (Enum254.run time ⟨pl,np,tw,ws,d,h⟩) :=
  run_encode_nat time _
example (out time : Nat) (s : Enum254.St) :
    runDef.val.Evalb ![out,time,encodeSt s] ↔
      out = ArithmeticEnumeratorStep254.encodeResult (Enum254.run time s) :=
  runDef_encode_nat out time s
example (time : Nat) (s : Enum254.St) :
    run time (encodeSt s) = 0 ↔ Enum254.run time s = none :=
  run_zero_iff_native_none time s
example (time : Nat) (s : Enum254.St) (h : Enum254.run time s = none) :
    EnumSafeStart254.HaltsFrom s := haltsFrom_of_run_none time s h
example (s : Enum254.St) (h : EnumSafeStart254.HaltsFrom s) :
    ∃ time, Enum254.run time s = none := run_none_of_haltsFrom s h
example (s : Enum254.St) :
    (∃ time : Nat, run time (encodeSt s) = 0) ↔ EnumSafeStart254.HaltsFrom s :=
  halts_iff_native s
example : encodeSt Enum254.s0 = 1 := encodeSt_s0
example : (∃ time : Nat, run time 1 = 0) ↔ Enum254.Halts := blank_halts_iff
example : run 0 1 = 1 := run_zero 1
example : run 0 (encodeSt Enum254.s0) ≠ 0 := by simp
