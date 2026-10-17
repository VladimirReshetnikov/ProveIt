import BusyBeaver.ZFC.ArithmeticCommandBlockExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticCommandStep254 ArithmeticCommandRun254
open ArithmeticCommandAppend254 ArithmeticProofWordContract254 ArithmeticCommandBlockExecution254
open ArithmeticCommandBlocks254 (Circuit)
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_mp
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_drop
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_nip
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_ax
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_append_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_append_success
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_nips
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.wim_ne_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.wal_ne_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.wim_one_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.gate_ne_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.axList_ne_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.circuit_consMp
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.circuit_consDrop
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.circuit_consNip
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.circuit_consAx
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.circuit_nips
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.eval_discard
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlockExecution254.discard_contract
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (x rest t s d h : V) :
    evalValue (mpWord x rest) (stateValue t s d h) =
      if wim t (d+x) = h then evalValue rest (stateValue (d+x) (cantor 0 s) (d+x) 0)
      else evalValue rest (stateValue 0 s (d+x) 0) := eval_mp x rest t s d h
example (x rest t s d h : V) :
    evalValue (dropWord x rest) (stateValue t s d h) =
      evalValue rest (stateValue h (cantor t s) (d+x) h) := eval_drop x rest t s d h
example (x rest t s d h : V) :
    evalValue (nipWord x rest) (stateValue t s d h) =
      if h = 1 then 0 else evalValue rest (stateValue t (second s) (d+x) (first s)) :=
  eval_nip x rest t s d h
example (x rest t s d : V) : evalValue (nipWord x rest) (stateValue t s d 1) = 0 := by
  simp [eval_nip]
example (c x y u rest t s d h : V) :
    evalValue (axWord c x y u rest) (stateValue t s d h) =
      evalValue rest (stateValue (gateValue (d+x) (h+y) c)
        (axStackValue (d+x) h (h+y) c u t s) 0 0) := eval_ax c x y u rest t s d h
example (left right w : V) (h : evalValue left w = 0) :
    evalValue (appendValue left right) w = 0 := eval_append_halt left right w h
example (left right w w' : V) (h : evalValue left w = w'+1) :
    evalValue (appendValue left right) w = evalValue right w' :=
  eval_append_success left right w w' h
example (t s d : V) (xs : List V) (h last : V) (hh : h ≠ 1)
    (hx : ∀ x, x ∈ xs → x ≠ 1) :
    evalValue (nipsWord (xs.length+1)) (stateValue t (pushL (xs++[last]) s) d h) =
      someState t s d last := eval_nips t s d xs h last hh hx
example (a b : V) : wim a b ≠ 1 := wim_ne_one a b
example (a b : V) : wal a b ≠ 1 := wal_ne_one a b
example (a : V) : wim a 1 ≠ 0 := wim_one_ne_zero a
example (a b c : V) : gateValue a b c ≠ 1 := gate_ne_one a b c
example (a h b c u x : V) (hx : x ∈ axList a h b c u) : x ≠ 1 := axList_ne_one a h b c u x hx
example (x rest : Circuit) (a b c u : V) :
    (Circuit.consMp x rest).eval a b c u = mpWord (x.eval a b c u) (rest.eval a b c u) :=
  circuit_consMp x rest a b c u
example (x rest : Circuit) (a b c u : V) :
    (Circuit.consDrop x rest).eval a b c u = dropWord (x.eval a b c u) (rest.eval a b c u) :=
  circuit_consDrop x rest a b c u
example (x rest : Circuit) (a b c u : V) :
    (Circuit.consNip x rest).eval a b c u = nipWord (x.eval a b c u) (rest.eval a b c u) :=
  circuit_consNip x rest a b c u
example (c x y z rest : Circuit) (a b d u : V) :
    (Circuit.consAx c x y z rest).eval a b d u =
      axWord (c.eval a b d u) (x.eval a b d u) (y.eval a b d u) (z.eval a b d u)
        (rest.eval a b d u) := circuit_consAx c x y z rest a b d u
example (k : Nat) (a b c u : V) : (Circuit.nips k).eval a b c u = nipsWord k :=
  circuit_nips k a b c u
example (a b c u t s : V) :
    evalValue (Circuit.discard.eval a b c u) (stateValue t s 0 0) = someState 0 s 0 0 :=
  eval_discard a b c u t s
example (a b c u : V) : Contract (Circuit.discard.eval a b c u) 0 := discard_contract a b c u
