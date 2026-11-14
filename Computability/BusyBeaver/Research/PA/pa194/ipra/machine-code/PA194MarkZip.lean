import PA194MarkRuntimeStandard
import PA194StepperZip
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194MarkZip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194MarkerScan PA194RegisterFile PA194RegisterFileStandard PA194UnaryRuns PA194CarryFile PA194MarkRuntimeStandard PA194StepperZip PackedStandard List.Vector
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem word_bits (xs : List Bool) : word xs 0 = PA194Bounded.bits xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [word,PA194Bounded.bits,ih,Nat.add_comm]

theorem pairNat (a b : Nat) : F pairCode ![a,b] = Nat.pair a b := by
  change eval pairCode (List.Vector.ofFn ![a,b]) = _
  rw [ofFn_two,evalPair]
  rfl

def markClock (first : Nat) (pre vs : List Nat) (v : Nat) : Nat :=
  let selectedTail := F ones ![v,F (fileCode vs.length) (valuesArg vs 0)]
  let selectedBlock := (selectedTail+selectedTail+1)+(selectedTail+selectedTail+1)
  let ep := valuesArg (first::pre) selectedBlock
  (F (costCode (pre.length+1)) ep+3)+F (costCode (pre.length+1)) ep

theorem literalMarkPositive (first : Nat) (pre vs : List Nat) (v : Nat) (left : List Bool)
    (bound : pre.length+1 < 9) :
    PA194Bounded.encodeZip (zipRunFrom ⟨markerControl ⟨pre.length+1,bound⟩,left,M6.Runtime.sepsR ((first::pre)++v::vs)⟩ (markClock first pre vs v)) =
    (17, PA194Bounded.bits left / 2, PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsM (pre.length+1) ((first::pre)++v::vs))) := by
  let c : M6.Zip.Conf := ⟨markerControl ⟨pre.length+1,bound⟩,left,M6.Runtime.sepsR ((first::pre)++v::vs)⟩
  let target : PA194Bounded.Conf := (17,PA194Bounded.bits left / 2,PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsM (pre.length+1) ((first::pre)++v::vs)))
  have h := runtimeMarkPositive first pre vs v (PA194Bounded.bits left) 0 bound
  dsimp only at h
  simp only [pairNat,ConfigurationStandard.fnHalf,ConfigurationStandard.fnParity,ConfigurationStandard.numeralNat,word_bits] at h
  have hstep := modelStepperZip c (markClock first pre vs v)
  have hinput : pack (PA194Bounded.encodeZip c) = Nat.pair (markerControl ⟨pre.length+1,bound⟩) (Nat.pair (PA194Bounded.bits left) (PA194Bounded.bits (M6.Runtime.sepsR ((first::pre)++v::vs)))) := rfl
  rw [hinput] at hstep
  change F PA194Stepper.stepper ![markClock first pre vs v,_] = _ at h
  rw [h] at hstep
  have hout : pack target = Nat.pair 17 (Nat.pair (PA194Bounded.bits left / 2) (PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsM (pre.length+1) ((first::pre)++v::vs)))) := rfl
  have hp : pack target = pack (PA194Bounded.encodeZip (zipRunFrom c (markClock first pre vs v))) := by
    rw [hout]
    have hn (a b : Nat) : a+2*b = a+b+b := by omega
    rw [hn]
    exact hstep
  have hresult := congrArg unpack hp
  simpa only [unpackPack] using hresult.symm
theorem literalMarkFirst (v : Nat) (vs : List Nat) (left : List Bool) :
    PA194Bounded.encodeZip (zipRunFrom ⟨113,left,M6.Runtime.sepsR (v::vs)⟩ 3) =
    (15, PA194Bounded.bits left / 2, PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsM 0 (v::vs))) := by
  let c : M6.Zip.Conf := ⟨113,left,M6.Runtime.sepsR (v::vs)⟩
  let target : PA194Bounded.Conf := (15,PA194Bounded.bits left / 2,PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsM 0 (v::vs)))
  have h := runtimeMarkFirst v (PA194Bounded.bits left) 0 vs
  simp only [pairNat,ConfigurationStandard.fnHalf,ConfigurationStandard.fnParity,ConfigurationStandard.numeralNat,word_bits] at h
  have hstep := modelStepperZip c 3
  have hinput : pack (PA194Bounded.encodeZip c) = Nat.pair 113 (Nat.pair (PA194Bounded.bits left) (PA194Bounded.bits (M6.Runtime.sepsR (v::vs)))) := rfl
  rw [hinput,h] at hstep
  have hout : pack target = Nat.pair 15 (Nat.pair (PA194Bounded.bits left / 2) (PA194Bounded.bits left % 2 + 2 * PA194Bounded.bits (M6.Runtime.sepsM 0 (v::vs)))) := rfl
  have hp : pack target = pack (PA194Bounded.encodeZip (zipRunFrom c 3)) := by
    rw [hout]
    have hn (a b : Nat) : a+2*b = a+b+b := by omega
    rw [hn]
    exact hstep
  have hresult := congrArg unpack hp
  simpa only [unpackPack] using hresult.symm
#print axioms literalMarkFirst
#print axioms literalMarkPositive
end PA194MarkZip
