import PA194PathLengthGlobalBound
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194MinimumWidthSafety
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAExhaustion PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem gapAtLeast12 (pc gap : M)
    (hwidth : modelNumeral M 48 ≤ gap + F PA194PathLengthCode.pathLengthCode (fun _ => pc)) :
    modelNumeral M 12 ≤ gap := by
  have hlen := PA194PathLengthGlobalBound.pathLengthBound pc
  have h := add_le_add_left hlen (modelNumeral M 12)
  have hnum : modelNumeral M 36 + modelNumeral M 12 = modelNumeral M 48 := by rw [←modelNumeralAdd]
  rw [hnum] at h
  have h' : modelNumeral M 12 + F PA194PathLengthCode.pathLengthCode (fun _ => pc) ≤
      gap + F PA194PathLengthCode.pathLengthCode (fun _ => pc) := by
    calc
      _ = F PA194PathLengthCode.pathLengthCode (fun _ => pc) + modelNumeral M 12 := add_comm _ _
      _ ≤ modelNumeral M 48 := h
      _ ≤ _ := hwidth
  exact le_of_add_le_add_right h'

theorem gapAtLeast2 (pc gap : M)
    (hwidth : modelNumeral M 48 ≤ gap + F PA194PathLengthCode.pathLengthCode (fun _ => pc)) :
    modelNumeral M 2 ≤ gap := by
  exact le_trans (le_of_lt (modelNumeralStrict 2 12 (by decide))) (gapAtLeast12 pc gap hwidth)
#print axioms gapAtLeast12
#print axioms gapAtLeast2
end models
end PA194MinimumWidthSafety
