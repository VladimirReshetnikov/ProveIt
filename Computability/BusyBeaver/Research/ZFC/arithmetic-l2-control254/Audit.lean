import BusyBeaver.ZFC.ArithmeticL2Control254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun
open ArithmeticCode254 (wim)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.ifeq_eq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.ifeq_ne
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.fetch_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.mp_branch
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.nip_branch
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.nip_halt

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (st : AS V) (h : st.s1 = st.p2) :
    IR (.node 123) (enc st) .normal (enc { st with s1 := 0, p2 := 0 }) :=
  ArithmeticL2.ifeq_eq st h

example (st : AS V) (h : st.s1 ≠ st.p2) :
    IR (.node 123) (enc st) (.brk 1) (enc { st with s1 := 0, p2 := 0 }) :=
  ArithmeticL2.ifeq_ne st h

example (st : AS V) (hpl : st.pl = 0) (h1 : st.s1 = 0) :
    Rn (.node 133) st { st with pl := st.np, np := st.np + 1 } :=
  ArithmeticL2.fetch_zero st hpl h1

example (st : AS V) (hc : Clean st) :
    Rn (.node 150) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := cantor 0 st.ws, p2 := 0 }
      else { st with tw := 0, p2 := 0 }) :=
  ArithmeticL2.mp_branch st hc

example (st : AS V) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 152) st { st with p2 := first st.ws, ws := second st.ws } :=
  ArithmeticL2.nip_branch st hc hh

example (st : AS V) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ y, IR (.node 152) (enc st) .halt y :=
  ArithmeticL2.nip_halt st hc hh

