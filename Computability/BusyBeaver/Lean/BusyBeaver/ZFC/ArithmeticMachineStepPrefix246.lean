import BusyBeaver.ZFC.ArithmeticMachineStepPerm252
import BusyBeaver.ZFC.ArithmeticMachineGraphPrefix246

/-!
The fixed bounded arithmetic step graph for the exact contextual-fold246
machine. Reuse the checked generic tape/action arithmetic and Cantor coding;
instantiate only the transition lookup and its typed-machine comparison.
All natural configuration codes are covered, including halted and invalid
states. This is not yet an internal comparison with the register interpreter.
The original program and compiler attribution remains with Mira-Cult,
Jeff Ketchersid and Andrew James Wade; the contextual reduction is source63.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPrefix246

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticRow254 ArithmeticHistory254
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def stepValue (input : V) : V :=
  genericStepValue ArithmeticMachineGraphPrefix246.actionLookup input

def stepDef : 𝚺₀.Semisentence 2 :=
  genericStepDef ArithmeticMachineGraphPrefix246.actionLookupDef

instance step_defined : 𝚺₀-Function₁[V] stepValue via stepDef :=
  generic_step_defined ArithmeticMachineGraphPrefix246.actionLookup
    ArithmeticMachineGraphPrefix246.actionLookupDef
    ArithmeticMachineGraphPrefix246.actionLookup_defined
    ArithmeticMachineGraphPrefix246.actionLookup_bound

theorem step_total (input : V) : ∃! out, stepDef.val.Evalb ![out,input] := by simp

def nativeStep (code : Nat) : Nat :=
  encodeConfig (numericStep machinePrefix246 (decodeConfig code))

lemma lookup_zero (bit : Nat) :
    lookupNat ArithmeticMachineGraphPrefix246.literalRows 0 0 bit = 0 :=
  lookupNat_absent _ _ _ _ (.inl (by omega))

lemma lookup_invalid (q bit : Nat) (hq : 246 < q) :
    lookupNat ArithmeticMachineGraphPrefix246.literalRows 0 q bit = 0 :=
  lookupNat_absent _ _ _ _ (.inr (by
    simpa only [ArithmeticMachineGraphPrefix246.literalRows_length, Nat.zero_add] using hq))

theorem stepValue_nat_encoded (u : NumericConfig) :
    stepValue (encodeConfig u) = encodeConfig (numericStep machinePrefix246 u) := by
  have henc : encodeConfig u = (cantor u.state (cantor u.left u.right) : Nat) := by
    simp only [encodeConfig, cantor_nat]
  rw [henc]
  change genericStepValue ArithmeticMachineGraphPrefix246.actionLookup
    (cantor u.state (cantor u.left u.right)) = _
  unfold genericStepValue
  rw [← numeral_two_eq_two]
  simp only [Nat.numeral_eq, first_cantor, second_cantor, HMod.hMod]
  simp only [foundation_rem_nat, ArithmeticMachineGraphPrefix246.actionLookup_nat]
  by_cases hz : u.state = 0
  · rw [hz, lookup_zero, if_pos rfl, numericStep_halted machinePrefix246 u hz]
    simp only [cantor_nat, encodeConfig, hz]
  by_cases hbig : 246 < u.state
  · rw [lookup_invalid _ _ hbig, if_pos rfl, numericStep_invalid machinePrefix246 u hbig]
    simp only [cantor_nat, encodeConfig]
  have hfin : u.state - 1 < 246 := by omega
  let q : Fin 246 := ⟨u.state - 1, hfin⟩
  let bit : Bool := decide (u.right % 2 = 1)
  have hlookup : lookupNat ArithmeticMachineGraphPrefix246.literalRows 0
      u.state (u.right % 2) = actionNumber (machinePrefix246.transition q bit) := by
    have h := ArithmeticMachineGraphPrefix246.literal_lookup_actual q bit
    have hq : q.val + 1 = u.state := by dsimp [q]; omega
    simpa only [hq, bit, native_read_bit] using h
  rw [hlookup, if_neg (Nat.ne_of_gt (actionNumber_positive _)), applyValue_nat]
  unfold numericStep actionAt
  simp [hz, hfin, q, bit]

theorem stepValue_nat (code : Nat) : stepValue code = nativeStep code := by
  calc
    stepValue code = stepValue (encodeConfig (decodeConfig code)) := by rw [encode_decode]
    _ = encodeConfig (numericStep machinePrefix246 (decodeConfig code)) := stepValue_nat_encoded _
    _ = nativeStep code := rfl

theorem stepDef_nat (out input : Nat) :
    stepDef.val.Evalb ![out,input] ↔ out = nativeStep input := by
  simp [stepValue_nat]

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPrefix246
