import PA194OneSpareSeed2
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194OneSpareSeed26
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194OneSpareReturn PA194OneSpareSeed2 PA194StartupSourceFrame PA194RegisterFile PA194StateOne PRAModelIOpenPairing PA194UnaryRuns PA194BinaryDouble PA194FiniteControls
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSeed26 : F repeatOutput ![modelNumeral M 26,(0 : M)] = F block ![(1 : M),modelNumeral M seedTail] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hn : modelNumeral M 26 = F Code.succ (fun _ => modelNumeral M 25) := by
    rw [←modelAddOne]
    change modelNumeral M (25+1) = modelNumeral M 25+(1 : M)
    rw [←modelNumeralOne,←modelNumeralAdd]
  rw [hn,modelOutputSucc,modelOutputBlock,modelSeed]
#print axioms modelSeed26
end models
end PA194OneSpareSeed26
