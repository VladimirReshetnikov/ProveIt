import PA194IncrementOutputExact
import PA194SevenReturnController
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194IncrementBoundary
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- The dense-7 endpoint's even left half differs from the singleton-one
left tape of the canonical standard-natural source root. -/
theorem evenLeftNotOne (a : M) : a+a ≠ (1 : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro he
  have hp := congrArg (fun x : M => F parityCode (fun _ => x)) he
  have h1 := (modelOdd (0 : M)).1
  simp only [zero_add] at h1
  rw [(modelDouble a).1,h1] at hp
  exact zero_ne_one hp
#print axioms evenLeftNotOne
end models
end PA194IncrementBoundary
