import BusyBeaver.ZFC.ArithmeticControlTable

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlTable ArithmeticControlFile

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.compact_lookup_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.compact_lookup_supported
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.spec_get
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.spec
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.step_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.controlRun_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.controlRun_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.controlRun_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.controlRun_halted
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlTable.controlRun_defined

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (xs : List (Nat × Nat)) (start i : Nat) (hi : i < xs.length) (b : V) :
    lookupValue (compactRows start xs) ((start+i+1 : Nat) : V) b =
      if b = 0 then ((xs[i]'hi).1 : V) else ((xs[i]'hi).2 : V) :=
  compact_lookup_at xs start i hi b
example (xs : List (Nat × Nat)) (start : Nat) (q b : V)
    (h : lookupValue (compactRows start xs) q b ≠ 0) :
    ∃ i, i < xs.length ∧ q = ((start+i+1 : Nat) : V) :=
  compact_lookup_supported xs start q b h
example (rl : List ArithmeticControlBisim.Row) (c : Nat) (row : ArithmeticControlBisim.Row)
    (x : V) (hc : c ≠ 0) (h : rl[c-1]? = some row) :
    stepValue rl (liveValue (c : V) x) =
      ArithmeticControlBisim.sem regValue ArithmeticControlTable.write liveValue row x :=
  spec_get rl c row x hc h
example (rl : List ArithmeticControlBisim.Row) (c : Nat) (row : ArithmeticControlBisim.Row)
    (x : V) (h : rows rl c = some row) :
    stepValue rl (liveValue (c : V) x) =
      ArithmeticControlBisim.sem regValue ArithmeticControlTable.write liveValue row x :=
  spec rl c row x h
example (rl : List ArithmeticControlBisim.Row) : stepValue rl (0 : V) = 0 := step_zero rl
example (rl : List ArithmeticControlBisim.Row) (x : V) : controlRun rl 0 x = x :=
  controlRun_zero rl x
example (rl : List ArithmeticControlBisim.Row) (n x : V) :
    controlRun rl (n+1) x = stepValue rl (controlRun rl n x) := controlRun_succ rl n x
example (rl : List ArithmeticControlBisim.Row) (t u x : V) :
    controlRun rl (t+u) x = controlRun rl u (controlRun rl t x) := controlRun_add rl t u x
example (rl : List ArithmeticControlBisim.Row) (t : V) : controlRun rl t 0 = 0 :=
  controlRun_halted rl t
example (rl : List ArithmeticControlBisim.Row) :
    𝚺₁-Function₂[V] (controlRun rl) via controlRunDef rl := controlRun_defined rl
example (p q : Fin 9) (v x : V) (h : p ≠ q) :
    regValue (ArithmeticControlTable.write p v x) q = regValue x q :=
  ArithmeticControlTable.reg_write_other p q v x h
example (x y : V) (h : ∀ i, regValue x i = regValue y i) : x = y := file_ext x y h
