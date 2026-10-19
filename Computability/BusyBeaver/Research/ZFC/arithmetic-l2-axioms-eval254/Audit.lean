import BusyBeaver.ZFC.ArithmeticL2AxiomsEval254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun
open ArithmeticCode254 (wal)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.e95
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.e1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (st : AS V) : f95 st = ⟨st.np, wal st.p1 st.p2, cantor st.tw st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ :=
  ArithmeticL2.e95 st

-- Consume the final full closed form without duplicating its large literal expression.
example (st : AS V) : (f1 st).np = st.np := by
  have h := congrArg AS.np (e1 st)
  exact h
example (st : AS V) : (f1 st).s2 = st.s2 := by
  have h := congrArg AS.s2 (e1 st)
  exact h
