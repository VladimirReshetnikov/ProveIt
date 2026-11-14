import PA194IncrementRuntimeStandard
import PA194StepperZip
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194IncrementZip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194IncrementRuntimeStandard PA194RegisterFileStandard PA194MarkedFile PA194CarryFile PA194StepperZip PackedStandard List.Vector
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)
local notation a " ⊕ " b => F addCode ![a,b]

theorem word_bits (xs : List Bool) : word xs 0 = PA194Bounded.bits xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [word,PA194Bounded.bits,ih,Nat.add_comm]

theorem pairNat (a b : Nat) : F pairCode ![a,b] = Nat.pair a b := by
  change eval pairCode (List.Vector.ofFn ![a,b]) = _
  rw [ofFn_two,evalPair]
  rfl

def incrementClock (pre vs : List Nat) (v : Nat) : Nat :=
  let selected := valuesArg (v::vs) 0
  let prefArgs := valuesArg pre (F (markedFile vs.length) selected)
  let prefCost := F (costCode pre.length) prefArgs
  let restCost := F (costCode vs.length) (fun i => selected i.succ)
  let front := ((oneN ⊕ oneN) ⊕ selected 0) ⊕ restCost
  let incrementCost := (((front ⊕ TableDispatch.modelNumeral Nat 6) ⊕ restCost) ⊕ (((selected 0 ⊕ oneN) ⊕ oneN) ⊕ oneN))
  (prefCost ⊕ incrementCost) ⊕ prefCost

def numericClock (pre vs : List Nat) (v : Nat) : Nat :=
  let selected := valuesArg (v::vs) 0
  let prefArgs := valuesArg pre (F (markedFile vs.length) selected)
  let prefCost := F (costCode pre.length) prefArgs
  let restCost := F (costCode vs.length) (fun i => selected i.succ)
  let front := 1+1+selected 0+restCost
  let incrementCost := front+6+restCost+(selected 0+1+1+1)
  (prefCost+incrementCost)+prefCost

theorem literalIncrement (pre vs : List Nat) (v : Nat) (left : List Bool) :
    PA194Bounded.encodeZip (zipRunFrom ⟨2,left,M6.Runtime.sepsM pre.length (pre++v::vs)⟩ (incrementClock pre vs v)) =
    (7, PA194Bounded.bits left / 2, PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsR (pre++(v+1)::vs++[1]))) := by
  let c : M6.Zip.Conf := ⟨2,left,M6.Runtime.sepsM pre.length (pre++v::vs)⟩
  let target : PA194Bounded.Conf := (7,PA194Bounded.bits left / 2,PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsR (pre++(v+1)::vs++[1])))
  have h := runtimeIncrement pre vs v (PA194Bounded.bits left)
  dsimp only at h
  simp only [pairNat,ConfigurationStandard.fnHalf,ConfigurationStandard.fnParity,ConfigurationStandard.numeralNat,oneN,natAdd,natOne,word_bits] at h
  have hstep := modelStepperZip c (incrementClock pre vs v)
  have hinput : pack (PA194Bounded.encodeZip c) = Nat.pair 2 (Nat.pair (PA194Bounded.bits left) (PA194Bounded.bits (M6.Runtime.sepsM pre.length (pre++v::vs)))) := rfl
  rw [hinput] at hstep
  have hclock : incrementClock pre vs v = numericClock pre vs v := by
    simp only [incrementClock,numericClock,oneN,natAdd,natOne,ConfigurationStandard.numeralNat]
  change F PA194Stepper.stepper ![numericClock pre vs v,_] = _ at h
  rw [←hclock] at h
  rw [h] at hstep
  have hout : pack target = Nat.pair 7 (Nat.pair (PA194Bounded.bits left / 2) (PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsR (pre++(v+1)::vs++[1])))) := rfl
  have hp : pack target = pack (PA194Bounded.encodeZip (zipRunFrom c (incrementClock pre vs v))) := by
    rw [hout]
    have hn (a b : Nat) : a+2*b = a+b+b := by omega
    rw [hn]
    exact hstep
  have := congrArg unpack hp
  simpa only [unpackPack] using this.symm
#print axioms literalIncrement
end PA194IncrementZip
