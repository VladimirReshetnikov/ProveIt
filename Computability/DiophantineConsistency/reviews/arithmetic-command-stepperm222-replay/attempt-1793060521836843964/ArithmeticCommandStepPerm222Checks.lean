import DiophantineConsistency.ArithmeticCommandStepPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandStepPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandStepPerm222

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example (raw w : V) : ∃! out, stepDef.val.Evalb ![out,raw,w] := step_total raw w

/-- Neither short command reads the rest as an argument or changes d. -/
example (rest t s d h : V) :
    stepValue (cantor 1 rest) (stateValue t s d h) = someState h (cantor t s) d h :=
  stepValue_drop rest t s d h

example (rest t s d : V) : stepValue (cantor 0 rest) (stateValue t s d 1) = 0 := by
  simp only [stepValue_nip, if_true]

/-- Exact argument orientation, old-counter GEN, and dominated rho8. -/
example (c y x rest t s d h : V) :
    stepValue (cantor (c+3) (cantor y (cantor x rest))) (stateValue t s d h) =
      someState (gateValue (d+x) (h+y) c)
        (axStackValue (d+x) h (h+y) c d t s) 0 0 := stepValue_ax _ _ _ _ _ _ _ _

example (d x : V) : d ≤ d+x := ax_rho8_dominated d x

/-- Colliding labels return truth without making AX halt. -/
example (a b : V) : gateValue a b a = 0 := by simp [gateValue]
example (a b : V) : gateValue a b b = 0 := by simp [gateValue]

/-- A failed MP producing the allzero state returns one, not halt zero. -/
example : stepValue (EnumPerm.pack (.mp 0) 91) (encodeW ⟨0,0,0,2⟩) = 1 := by
  rw [stepValue_pack_nat]
  decide

example (raw : ℕ) (w : EnumPerm.W) :
    stepValue raw (encodeW w) = encodeResult (EnumPerm.cstep (EnumPerm.decode raw).1 w) :=
  stepValue_nat raw w

example (cmd : EnumPerm.Cmd) (rest : ℕ) (w : EnumPerm.W) :
    stepValue (EnumPerm.pack cmd rest) (encodeW w) = encodeResult (EnumPerm.cstep cmd w) :=
  stepValue_pack_nat cmd rest w

#print axioms state_defined
#print axioms gate_defined
#print axioms axStack_defined
#print axioms effect_defined
#print axioms step_defined
#print axioms step_total
#print axioms ax_rho8_dominated
#print axioms stepValue_eq_zero_iff
#print axioms axStackValue_nat
#print axioms stepValue_pack_nat
#print axioms pack_decode
#print axioms stepValue_nat

end DiophantineConsistency.ArithmeticCommandStepPerm222Checks
