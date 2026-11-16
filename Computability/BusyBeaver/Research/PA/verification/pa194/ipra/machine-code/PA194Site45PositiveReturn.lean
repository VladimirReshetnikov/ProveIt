import PA194Site45Branch
import PA194Site32PositiveReturnExact
import PA194MarkedFile
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site45PositiveReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194MarkedFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem positiveReturn (k : M) (args : Fin 11 → M) (m : M) (hm : args 6 = m+1) :
    let before := F ones ![k+1,modelNumeral M 408]
    F PA194Stepper.stepper ![PA194Site32PositiveReturnExact.returnCost args,PA194Site45Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 6,F pairCode ![before+before+1,F sourceFileCode (Function.update args 6 m)]] := by
  dsimp only
  let v := physicalArgs args
  let sel := PA194Site45MarkedFile.selectedArgs args
  let tail := F (fileCode 1) (fun i => sel i.succ)
  let q := F ones ![m+1,tail]
  let vec : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
  let before := F ones ![k+1,modelNumeral M 408]
  let left := F (PA194CarryFile.leftCode 8) (Fin.cases before vec)
  let z := left+left+1
  have hmarked : F (markedFile 1) sel = (q+q)+(q+q) := by
    rw [modelMarkedFile,modelMarkedBlock]
    change (F ones ![args 6,tail]+F ones ![args 6,tail])+(F ones ![args 6,tail]+F ones ![args 6,tail]) = _
    rw [hm]
  have hvec : PA194Site45MarkedFile.prefixArgs args = vec := by
    dsimp only [PA194Site45MarkedFile.prefixArgs,vec]
    rw [hmarked]
  have hmark : PA194Site45Branch.marker k args = z := by
    dsimp only [PA194Site45Branch.marker,z,left,before]
    rw [hvec]
  have htail : PA194Site45Branch.selectedTail args = tail := rfl
  have h4 := PA194Site45Branch.at4 k args
  dsimp only at h4
  change PA194Site45Branch.runTo4 k args = F pairCode ![modelNumeral M 4,F pairCode ![
    PA194Site45Branch.marker k args+PA194Site45Branch.marker k args,F ones ![args 6,PA194Site45Branch.selectedTail args]]] at h4
  rw [hmark,hm,htail] at h4
  have hr := PA194Site32PositiveReturnExact.returnFile args before m
  dsimp only at hr
  change F PA194Stepper.stepper ![PA194Site32PositiveReturnExact.returnCost args,F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] = _ at hr
  rw [h4,hr]
#print axioms positiveReturn
end models
end PA194Site45PositiveReturn
