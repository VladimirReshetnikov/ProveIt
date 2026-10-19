import BusyBeaver.ZFC.ArithmeticL2Lib254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.lreg_enc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.lupd_enc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.pair162
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.loop116

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (st : AS V) (r : Nat) (hr : r < 9) : lreg (enc st) r = field st r :=
  ArithmeticL2.lreg_enc st r hr

example (st : AS V) (r : Nat) (hr : r < 9) (v : V) :
    lupd (enc st) r v = enc (updAS st r v) :=
  ArithmeticL2.lupd_enc st r hr v

example (st : AS V) :
    Rn (.node 162) st { st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } :=
  ArithmeticL2.pair162 st

example (st : AS V) :
    Rn (.node 116) st (unpairAS st (cantor st.s1 st.s2 + st.ws)).withWSZero :=
  ArithmeticL2.loop116 st

