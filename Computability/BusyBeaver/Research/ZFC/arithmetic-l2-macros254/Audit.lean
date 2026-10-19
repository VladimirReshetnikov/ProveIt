import BusyBeaver.ZFC.ArithmeticL2Macros254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun
open ArithmeticCode254 (wim)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.pop110
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.cons
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.read108
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.read_p2

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (st : AS V) (hc : Clean st) :
    Rn (.node 160) st { st with ws := second st.ws, s1 := first st.ws } :=
  ArithmeticL2.pop110 st hc

example (st : AS V) (hc : Clean st) :
    Rn (.node 119) st { st with tw := wim (first st.ws) st.tw, ws := second st.ws } :=
  ArithmeticL2.cons st hc

example (st : AS V) (hc : Clean st) :
    Rn (.node 158) st { st with pl := second st.pl, s1 := first st.pl } :=
  ArithmeticL2.read108 st hc

example (st : AS V) (hc : Clean st) :
    Rn (.node 176) st { st with pl := second st.pl, p2 := st.p2 + first st.pl } :=
  ArithmeticL2.read_p2 st hc

