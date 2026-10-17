import BusyBeaver.ZFC.ArithmeticCommandStep254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticTemplates254 ArithmeticCommandStep254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.state_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.someState_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.gate_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.axStack_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.effect_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.stepValue_mp
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.stepValue_drop
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.stepValue_nip
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.stepValue_ax
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.effectValue_eq_zero_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.stepValue_eq_zero_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.stateValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.someState_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.gateValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.axStackValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.stepValue_pack_nat
section IOpen
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (raw w r : V) : stepDef.val.Evalb ![r,raw,w] ↔ r = stepValue raw w := by simp
example (raw w : V) : ∃! r, stepDef.val.Evalb ![r,raw,w] := by simp
example (a b c : V) : gateValue a b c = if c=a ∨ c=b then 0 else bundle a b c := rfl
example (a b : V) : gateValue a b a = 0 := by simp [gateValue]
example (a b : V) : gateValue a b b = 0 := by simp [gateValue]
example (a c : V) (h : c ≠ a) : gateValue a a c = bundle a a c := by simp [gateValue,h]
example (x rest t s d h : V) :
    stepValue (cantor 0 (cantor x rest)) (stateValue t s d h) =
      if wim t (d+x)=h then someState (d+x) (cantor 0 s) (d+x) 0 else someState 0 s (d+x) 0 :=
  stepValue_mp x rest t s d h
example (x rest t s d h : V) :
    stepValue (cantor 1 (cantor x rest)) (stateValue t s d h) = someState h (cantor t s) (d+x) h :=
  stepValue_drop x rest t s d h
example (x rest t s d h : V) :
    stepValue (cantor 2 (cantor x rest)) (stateValue t s d h) =
      if h=1 then 0 else someState t (second s) (d+x) (first s) := stepValue_nip x rest t s d h
example (c x y u rest t s d h : V) :
    stepValue (cantor (c+3) (cantor x (cantor y (cantor u rest)))) (stateValue t s d h) =
      someState (gateValue (d+x) (h+y) c) (axStackValue (d+x) h (h+y) c u t s) 0 0 :=
  stepValue_ax c x y u rest t s d h
example (raw w : V) : stepValue raw w = 0 ↔ first raw=2 ∧ second (second (second w))=1 :=
  stepValue_eq_zero_iff raw w
example (rest t s d : V) : stepValue (cantor 2 (cantor 0 rest)) (stateValue t s d 1)=0 := by
  simp [stepValue_nip]
example (rest : V) : stepValue (cantor 0 (cantor 0 rest)) (stateValue 0 0 0 0)=1 := by
  rw [stepValue_mp]
  simp [someState, stateValue, ArithmeticCode254.wim, tagged, cantor, triangle]
example (x rest t s d h : V) (hm : wim t (d+x) ≠ h) :
    stepValue (cantor 0 (cantor x rest)) (stateValue t s d h) = someState 0 s (d+x) 0 := by
  simp [stepValue_mp,hm]
end IOpen
section Nat
example (c : Enum254.Cmd) (rest : Nat) (w : Enum254.W) :
    stepValue (Enum254.pack c rest) (encodeW w) = encodeResult (Enum254.cstep c w) :=
  stepValue_pack_nat c rest w
example (x rest : Nat) (w : Enum254.W) :
    stepValue (Enum254.pack (.mp x) rest) (encodeW w) = encodeResult (Enum254.cstep (.mp x) w) :=
  stepValue_pack_nat (.mp x) rest w
example (x rest : Nat) (w : Enum254.W) :
    stepValue (Enum254.pack (.drop x) rest) (encodeW w) = encodeResult (Enum254.cstep (.drop x) w) :=
  stepValue_pack_nat (.drop x) rest w
example (x rest : Nat) (w : Enum254.W) :
    stepValue (Enum254.pack (.nip x) rest) (encodeW w) = encodeResult (Enum254.cstep (.nip x) w) :=
  stepValue_pack_nat (.nip x) rest w
example (c x y u rest : Nat) (w : Enum254.W) :
    stepValue (Enum254.pack (.ax c x y u) rest) (encodeW w) = encodeResult (Enum254.cstep (.ax c x y u) w) :=
  stepValue_pack_nat (.ax c x y u) rest w
end Nat
