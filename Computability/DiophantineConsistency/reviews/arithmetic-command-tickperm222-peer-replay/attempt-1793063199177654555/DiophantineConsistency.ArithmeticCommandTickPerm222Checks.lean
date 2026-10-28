import DiophantineConsistency.ArithmeticCommandTickPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandTickPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandStepPerm222 ArithmeticCommandTickPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example (w : V) : tickValue (liveValue 0 w) = liveValue 0 w := tick_done w
example (w : V) : tickValue (liveValue 1 w) = nextValue 0 w := by
  simpa only [zero_add] using tick_live_succ (0 : V) w
example (config : V) (h : ¬ Stopped config) :
    tickValue config=0 ∨ remaining (tickValue config)+1 ≤ remaining config :=
  tick_decreases h
example (raw : ℕ) (w : EnumPerm.W) : nextValue raw (encodeW w) =
    match EnumPerm.cstep (EnumPerm.decode raw).1 w with
    | none => 0
    | some w' => liveValue (EnumPerm.decode raw).2 (encodeW w') := nextValue_nat raw w

#print axioms live_defined
#print axioms remaining_defined
#print axioms working_defined
#print axioms live_decode
#print axioms next_defined
#print axioms tick_defined
#print axioms tick_zero
#print axioms tick_done
#print axioms tick_live_succ
#print axioms tick_stopped
#print axioms stopped_tick
#print axioms tick_decreases
#print axioms nextValue_nat
end DiophantineConsistency.ArithmeticCommandTickPerm222Checks
