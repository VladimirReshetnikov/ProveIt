import BusyBeaver.ZFC.ArithmeticL2Axioms254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.l71
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.l1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.c1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (st : AS V) (hc : Clean st) : Rn (.node 71) st (gateF st) :=
  ArithmeticL2.l71 st hc

example (st : AS V) (hc : Clean st) : Rn (.node 1) st (f1 st) :=
  ArithmeticL2.l1 st hc

example (st : AS V) (hc : Clean st) : Clean (f1 st) :=
  ArithmeticL2.c1 st hc

