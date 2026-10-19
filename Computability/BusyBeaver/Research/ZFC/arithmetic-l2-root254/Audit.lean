import BusyBeaver.ZFC.ArithmeticL2Root254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.ax_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.dispatch_nip_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.fetch_run_pos
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.fetch_run_zero

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (np t S c a h pl : V) :
    f1 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, ArithmeticCommandStep254.gateValue a (h + first pl) c,
        ArithmeticCommandStep254.axStackValue a h (h + first pl) c (first (second pl)) t S,
        0, 0, 0, 0, 0, second (second pl)⟩ :=
  ArithmeticL2.ax_eval np t S c a h pl

example (st : AS V) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ y, IR (.node 141) (enc { st with ac := 2 }) .halt y :=
  ArithmeticL2.dispatch_nip_halt st hc hh

example (pl np t s d h : V) (hp : pl ≠ 0) :
    Rn (.node 133) (toAS pl np t s d h) (toAS (pl - 1) np t s d h) :=
  ArithmeticL2.fetch_run_pos pl np t s d h hp

example (np t s d h : V) :
    Rn (.node 133) (toAS 0 np t s d h) (toAS np (np + 1) t s d h) :=
  ArithmeticL2.fetch_run_zero np t s d h

