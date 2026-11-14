import PA194BinaryDouble
import PA194FiniteControls
/-! The PA194 tape codes agree with arithmetic division and remainder in every candidate-PRA model, including nonstandard elements. -/
set_option autoImplicit false
namespace PA194HalfDiv
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelHalfDiv (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    F halfCode (fun _ => x) = x / 2 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rcases even_or_odd' x with he | ho
  · have hx : x = (x / 2)+(x / 2) := by simpa only [two_mul] using he
    calc
      F halfCode (fun _ => x) = F halfCode (fun _ => (x / 2)+(x / 2)) := congrArg (fun y => F halfCode (fun _ => y)) hx
      _ = x / 2 := (modelDouble (x / 2)).2
  · have hx : x = (x / 2)+(x / 2)+1 := by simpa only [two_mul] using ho
    calc
      F halfCode (fun _ => x) = F halfCode (fun _ => (x / 2)+(x / 2)+1) := congrArg (fun y => F halfCode (fun _ => y)) hx
      _ = x / 2 := (modelOdd (x / 2)).2
theorem modelParityMod (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    F parityCode (fun _ => x) = x % 2 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rcases mod_two x with he | ho
  · have hx : x = (x / 2)+(x / 2) := by
      have h := div_add_mod x 2
      rw [he] at h
      simpa only [two_mul,add_zero] using h.symm
    calc
      F parityCode (fun _ => x) = F parityCode (fun _ => (x / 2)+(x / 2)) := congrArg (fun y => F parityCode (fun _ => y)) hx
      _ = 0 := (modelDouble (x / 2)).1
      _ = x % 2 := he.symm
  · have hx : x = (x / 2)+(x / 2)+1 := by
      have h := div_add_mod x 2
      rw [ho] at h
      simpa only [two_mul] using h.symm
    calc
      F parityCode (fun _ => x) = F parityCode (fun _ => (x / 2)+(x / 2)+1) := congrArg (fun y => F parityCode (fun _ => y)) hx
      _ = 1 := (modelOdd (x / 2)).1
      _ = x % 2 := ho.symm
theorem modelNumeralCast (n : Nat) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    TableDispatch.modelNumeral M n = (n : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PA194FiniteControls.modelNumeralSucc, ih]
    simp
#print axioms modelNumeralCast
#print axioms modelParityMod
#print axioms modelHalfDiv
end models
end PA194HalfDiv
