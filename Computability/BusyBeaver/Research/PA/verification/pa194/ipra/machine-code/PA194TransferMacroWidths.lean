import PA194PathLengthCode
import Mathlib.Tactic.Abel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194TransferMacroWidths
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing

theorem pathLengths : [(PA194SourceProgram.path 3661).length, (PA194SourceProgram.path 3664).length,
    (PA194SourceProgram.path 3668).length, (PA194SourceProgram.path 3671).length,
    (PA194SourceProgram.path 3672).length, (PA194SourceProgram.path 0).length] = [6,7,7,3,3,6] := by
  decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def width (site : Nat) (gap : M) : M := gap + modelNumeral M (PA194SourceProgram.path site).length

theorem macroWidths (k : M) :
    let g := ((k+1)+1)+1
    let g' := ((k+1)+1)
    let g'' := (((((k+1)+1)+1)+1)+1+1)
    width 3661 g = width 3664 g' ∧ width 3664 g' = width 3668 g' ∧
    width 3668 g' = width 3671 g'' ∧ width 3671 g'' = width 3672 g'' ∧
    width 3672 g'' = width 0 g := by
  have hpaths := pathLengths
  simp only [List.cons.injEq, and_true] at hpaths
  rcases hpaths with ⟨h1,h2,h3,h4,h5,h0⟩
  have h7 : modelNumeral M 7 = modelNumeral M 6 + (1 : M) := by rw [←modelNumeralOne,←modelNumeralAdd]
  have h6 : modelNumeral M 6 = ((modelNumeral M 3 + (1 : M))+1)+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  dsimp only [width]
  rw [h1,h2,h3,h4,h5,h0,h7,h6]
  repeat' constructor <;> (try abel) <;> simp_all
#print axioms pathLengths
#print axioms macroWidths
end models
end PA194TransferMacroWidths
