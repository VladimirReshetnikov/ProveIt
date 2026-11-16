import PA194Site49PositivePath
import PA194Site49SmallGapArithmetic
set_option autoImplicit false
namespace PA194Site49SmallGapPhysical
open DiophantineConsistency LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
theorem natAdd (x y : Nat) : Structure.func (L := language) addCode ![x,y] = x+y := by
  change eval addCode (List.Vector.ofFn ![x,y]) = _
  rw [ofFn_two]
  exact eval_addCode x y

theorem natOne : Structure.func (L := language) oneCode (Fin.elim0 : Fin 0 → Nat) = 1 := by decide +kernel
theorem wordEq (bits : List Bool) (x : Nat) : PA194Path27Header.modelWord bits x = PA194Site49SmallGapArithmetic.word bits x := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · change Structure.func (L := language) addCode ![PA194Path27Header.modelWord bs x, PA194Path27Header.modelWord bs x] = 0 + 2 * PA194Site49SmallGapArithmetic.word bs x
      rw [natAdd,ih]
      simp [Nat.two_mul]
    · change Structure.func (L := language) addCode ![Structure.func (L := language) addCode ![PA194Path27Header.modelWord bs x, PA194Path27Header.modelWord bs x],Structure.func (L := language) oneCode (Fin.elim0 : Fin 0 → Nat)] = 1 + 2 * PA194Site49SmallGapArithmetic.word bs x
      rw [natAdd,natAdd,natOne,ih]
      simp [Nat.two_mul,Nat.add_comm]

open PA194BinaryDouble PackedDecoderModel TableDispatch
local notation "F" => Structure.func (L := language)

theorem wordMismatchTwo (f x : Nat) :
    PA194Path27Header.modelWord [true,false,true,false,true,false,false,true,false,false] (2*(2*f+1)) ≠
      PA194Path27Header.modelWord (PA194SourceProgram.path 50) x := by
  rw [PA194Site49PositivePath.path50,wordEq,wordEq]
  exact PA194Site49SmallGapArithmetic.gapTwo f x

theorem wordMismatchThree (f x : Nat) :
    PA194Path27Header.modelWord [true,false,true,false,true,false,false,true,false,false] (4*(2*f+1)) ≠
      PA194Path27Header.modelWord (PA194SourceProgram.path 50) x := by
  rw [PA194Site49PositivePath.path50,wordEq,wordEq]
  exact PA194Site49SmallGapArithmetic.gapThree f x

theorem wordMismatchFour (f x : Nat) :
    PA194Path27Header.modelWord [true,false,true,false,true,false,false,true,false,false] (8*(2*f+1)) ≠
      PA194Path27Header.modelWord (PA194SourceProgram.path 50) x := by
  rw [PA194Site49PositivePath.path50,wordEq,wordEq]
  exact PA194Site49SmallGapArithmetic.gapFour f x

theorem rootMismatchTwo (f x : Nat) :
    F PA194Stepper.stepper ![modelNumeral Nat 24,F pairCode ![modelNumeral Nat 16,F pairCode ![modelNumeral Nat 106,
      PA194Path27Header.modelWord [false,true,false,false] (2*(2*f+1))]]] ≠
      F pairCode ![modelNumeral Nat 24,F pairCode ![modelNumeral Nat 1,PA194Path27Header.modelWord (PA194SourceProgram.path 50) x]] := by
  intro h
  rw [PA194Site49PositiveFinish.returnWord] at h
  letI : Zero Nat := ⟨F (Code.zero 0) Fin.elim0⟩
  letI : One Nat := ⟨F oneCode Fin.elim0⟩
  letI : Add Nat := ⟨fun x y => F addCode ![x,y]⟩
  letI : Mul Nat := ⟨fun x y => F mulCode ![x,y]⟩
  letI : LT Nat := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : Nat↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  have hw := congrArg (fun z => pi₂ (pi₂ z)) h
  simp only [modelPairCode,pi₂_pair] at hw
  exact wordMismatchTwo f x hw
theorem rootMismatchThree (f x : Nat) :
    F PA194Stepper.stepper ![modelNumeral Nat 24,F pairCode ![modelNumeral Nat 16,F pairCode ![modelNumeral Nat 106,
      PA194Path27Header.modelWord [false,true,false,false] (4*(2*f+1))]]] ≠
      F pairCode ![modelNumeral Nat 24,F pairCode ![modelNumeral Nat 1,PA194Path27Header.modelWord (PA194SourceProgram.path 50) x]] := by
  intro h
  rw [PA194Site49PositiveFinish.returnWord] at h
  letI : Zero Nat := ⟨F (Code.zero 0) Fin.elim0⟩
  letI : One Nat := ⟨F oneCode Fin.elim0⟩
  letI : Add Nat := ⟨fun x y => F addCode ![x,y]⟩
  letI : Mul Nat := ⟨fun x y => F mulCode ![x,y]⟩
  letI : LT Nat := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : Nat↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  have hw := congrArg (fun z => pi₂ (pi₂ z)) h
  simp only [modelPairCode,pi₂_pair] at hw
  exact wordMismatchThree f x hw

theorem rootMismatchFour (f x : Nat) :
    F PA194Stepper.stepper ![modelNumeral Nat 24,F pairCode ![modelNumeral Nat 16,F pairCode ![modelNumeral Nat 106,
      PA194Path27Header.modelWord [false,true,false,false] (8*(2*f+1))]]] ≠
      F pairCode ![modelNumeral Nat 24,F pairCode ![modelNumeral Nat 1,PA194Path27Header.modelWord (PA194SourceProgram.path 50) x]] := by
  intro h
  rw [PA194Site49PositiveFinish.returnWord] at h
  letI : Zero Nat := ⟨F (Code.zero 0) Fin.elim0⟩
  letI : One Nat := ⟨F oneCode Fin.elim0⟩
  letI : Add Nat := ⟨fun x y => F addCode ![x,y]⟩
  letI : Mul Nat := ⟨fun x y => F mulCode ![x,y]⟩
  letI : LT Nat := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : Nat↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  have hw := congrArg (fun z => pi₂ (pi₂ z)) h
  simp only [modelPairCode,pi₂_pair] at hw
  exact wordMismatchFour f x hw
#print axioms wordEq
#print axioms wordMismatchTwo
#print axioms wordMismatchThree
#print axioms wordMismatchFour
#print axioms rootMismatchTwo
#print axioms rootMismatchThree
#print axioms rootMismatchFour
end PA194Site49SmallGapPhysical
