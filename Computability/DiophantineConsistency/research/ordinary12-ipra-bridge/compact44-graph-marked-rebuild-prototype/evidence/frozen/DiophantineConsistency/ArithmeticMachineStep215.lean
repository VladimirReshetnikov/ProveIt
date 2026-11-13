import BusyBeaver.ZFC.ArithmeticMachineStepPerm252
import DiophantineConsistency.ArithmeticMachineGraph215

/-! The exact decimal215 bounded step graph, reusing generic action/tape arithmetic. All natural configuration codes, including halted and invalid states, are covered. Entering halt still writes and moves. This is not an internal consistency calibration. -/
namespace DiophantineConsistency.ArithmeticMachineStep215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
attribute [local irreducible] DecimalMachine215.machine

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticRow254 ArithmeticHistory254
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def stepValue (input : V) : V :=
  genericStepValue ArithmeticMachineGraph215.actionLookup input

def stepDef : 𝚺₀.Semisentence 2 :=
  genericStepDef ArithmeticMachineGraph215.actionLookupDef

instance step_defined : 𝚺₀-Function₁[V] stepValue via stepDef :=
  generic_step_defined ArithmeticMachineGraph215.actionLookup
    ArithmeticMachineGraph215.actionLookupDef
    ArithmeticMachineGraph215.actionLookup_defined
    ArithmeticMachineGraph215.actionLookup_bound

theorem step_total (input : V) : ∃! out, stepDef.val.Evalb ![out,input] := by simp

def nativeStep (code : Nat) : Nat :=
  encodeConfig (numericStep DecimalMachine215.machine (decodeConfig code))

lemma lookup_zero (bit : Nat) :
    lookupNat ArithmeticMachineGraph215.literalRows 0 0 bit = 0 :=
  lookupNat_absent _ _ _ _ (.inl (by omega))

lemma lookup_invalid (q bit : Nat) (hq : 215 < q) :
    lookupNat ArithmeticMachineGraph215.literalRows 0 q bit = 0 :=
  lookupNat_absent _ _ _ _ (.inr (by
    simpa only [ArithmeticMachineGraph215.literalRows_length, Nat.zero_add] using hq))

theorem stepValue_nat_encoded (u : NumericConfig) :
    stepValue (encodeConfig u) = encodeConfig (numericStep DecimalMachine215.machine u) := by
  have henc : encodeConfig u = (cantor u.state (cantor u.left u.right) : Nat) := by
    simp only [encodeConfig, cantor_nat]
  rw [henc]
  change genericStepValue ArithmeticMachineGraph215.actionLookup
    (cantor u.state (cantor u.left u.right)) = _
  unfold genericStepValue
  rw [← numeral_two_eq_two]
  simp only [Nat.numeral_eq, first_cantor, second_cantor, HMod.hMod]
  simp only [foundation_rem_nat, ArithmeticMachineGraph215.actionLookup_nat]
  by_cases hz : u.state = 0
  · rw [hz, lookup_zero, if_pos rfl, numericStep_halted DecimalMachine215.machine u hz]
    simp only [cantor_nat, encodeConfig, hz]
  by_cases hbig : 215 < u.state
  · rw [lookup_invalid _ _ hbig, if_pos rfl, numericStep_invalid DecimalMachine215.machine u hbig]
    simp only [cantor_nat, encodeConfig]
  have hfin : u.state - 1 < 215 := by omega
  let q : Fin 215 := ⟨u.state - 1, hfin⟩
  let bit : Bool := decide (u.right % 2 = 1)
  have hlookup : lookupNat ArithmeticMachineGraph215.literalRows 0
      u.state (u.right % 2) = actionNumber (DecimalMachine215.machine.transition q bit) := by
    have hq : q.val + 1 = u.state := by dsimp [q]; omega
    simpa only [hq, bit, native_read_bit] using ArithmeticMachineGraph215.literal_lookup_actual q bit
  rw [hlookup, if_neg (Nat.ne_of_gt (actionNumber_positive _)), applyValue_nat]
  unfold numericStep actionAt
  simp [hz, hfin, q, bit]

theorem stepValue_nat (code : Nat) : stepValue code = nativeStep code := by
  simpa only [encode_decode, nativeStep] using stepValue_nat_encoded (decodeConfig code)

theorem stepDef_nat (out input : Nat) :
    stepDef.val.Evalb ![out,input] ↔ out = nativeStep input := by
  simp [stepValue_nat]

end DiophantineConsistency.ArithmeticMachineStep215
