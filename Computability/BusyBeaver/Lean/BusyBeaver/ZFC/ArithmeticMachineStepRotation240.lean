import BusyBeaver.ZFC.ArithmeticMachineStepPerm252
import BusyBeaver.ZFC.ArithmeticMachineGraphRotation240

/-!
The fixed bounded arithmetic step graph for the exact source-rotation240
machine. Reuse the checked generic tape/action arithmetic and Cantor coding;
instantiate only the transition lookup and its typed-machine comparison.
All natural configuration codes are covered, including halted and invalid
states. This is not yet an internal comparison with the register interpreter.
The original program and compiler attribution remains with Mira-Cult,
Jeff Ketchersid and Andrew James Wade; the source rotation and compensated folds are retained in source80.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticRow254 ArithmeticHistory254
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def stepValue (input : V) : V :=
  genericStepValue ArithmeticMachineGraphRotation240.actionLookup input

def stepDef : 𝚺₀.Semisentence 2 :=
  genericStepDef ArithmeticMachineGraphRotation240.actionLookupDef

instance step_defined : 𝚺₀-Function₁[V] stepValue via stepDef :=
  generic_step_defined ArithmeticMachineGraphRotation240.actionLookup
    ArithmeticMachineGraphRotation240.actionLookupDef
    ArithmeticMachineGraphRotation240.actionLookup_defined
    ArithmeticMachineGraphRotation240.actionLookup_bound

theorem step_total (input : V) : ∃! out, stepDef.val.Evalb ![out,input] := by simp

def nativeStep (code : Nat) : Nat :=
  encodeConfig (numericStep machineRotation240 (decodeConfig code))

lemma lookup_zero (bit : Nat) :
    lookupNat ArithmeticMachineGraphRotation240.literalRows 0 0 bit = 0 :=
  lookupNat_absent _ _ _ _ (.inl (by omega))

lemma lookup_invalid (q bit : Nat) (hq : 240 < q) :
    lookupNat ArithmeticMachineGraphRotation240.literalRows 0 q bit = 0 :=
  lookupNat_absent _ _ _ _ (.inr (by
    simpa only [ArithmeticMachineGraphRotation240.literalRows_length, Nat.zero_add] using hq))

theorem stepValue_nat_encoded (u : NumericConfig) :
    stepValue (encodeConfig u) = encodeConfig (numericStep machineRotation240 u) := by
  have henc : encodeConfig u = (cantor u.state (cantor u.left u.right) : Nat) := by
    simp only [encodeConfig, cantor_nat]
  rw [henc]
  change genericStepValue ArithmeticMachineGraphRotation240.actionLookup
    (cantor u.state (cantor u.left u.right)) = _
  unfold genericStepValue
  rw [← numeral_two_eq_two]
  simp only [Nat.numeral_eq, first_cantor, second_cantor, HMod.hMod]
  simp only [foundation_rem_nat, ArithmeticMachineGraphRotation240.actionLookup_nat]
  by_cases hz : u.state = 0
  · rw [hz, lookup_zero, if_pos rfl, numericStep_halted machineRotation240 u hz]
    simp only [cantor_nat, encodeConfig, hz]
  by_cases hbig : 240 < u.state
  · rw [lookup_invalid _ _ hbig, if_pos rfl, numericStep_invalid machineRotation240 u hbig]
    simp only [cantor_nat, encodeConfig]
  have hfin : u.state - 1 < 240 := by omega
  let q : Fin 240 := ⟨u.state - 1, hfin⟩
  let bit : Bool := decide (u.right % 2 = 1)
  have hlookup : lookupNat ArithmeticMachineGraphRotation240.literalRows 0
      u.state (u.right % 2) = actionNumber (machineRotation240.transition q bit) := by
    have h := ArithmeticMachineGraphRotation240.literal_lookup_actual q bit
    have hq : q.val + 1 = u.state := by dsimp [q]; omega
    simpa only [hq, bit, native_read_bit] using h
  rw [hlookup, if_neg (Nat.ne_of_gt (actionNumber_positive _)), applyValue_nat]
  unfold numericStep actionAt
  simp [hz, hfin, q, bit]

theorem stepValue_nat (code : Nat) : stepValue code = nativeStep code := by
  calc
    stepValue code = stepValue (encodeConfig (decodeConfig code)) := by rw [encode_decode]
    _ = encodeConfig (numericStep machineRotation240 (decodeConfig code)) := stepValue_nat_encoded _
    _ = nativeStep code := rfl

theorem stepDef_nat (out input : Nat) :
    stepDef.val.Evalb ![out,input] ↔ out = nativeStep input := by
  simp [stepValue_nat]

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepRotation240
