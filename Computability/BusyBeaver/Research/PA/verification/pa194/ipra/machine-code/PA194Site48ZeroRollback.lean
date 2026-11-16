import PA194Site48Branch
import PA194Site48ZeroRollbackCell
import PA194Site48ZeroFile
import PA194MarkedFile
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site48ZeroRollback
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194ReturnFile PA194Site48ZeroFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def cost (args : Fin 11 → M) : M :=
  F addCode ![F addCode ![modelNumeral M 1,modelNumeral M 2],F (PA194CarryFile.costCode 5) (five args)]
noncomputable def before (k : M) : M := F ones ![k+1,modelNumeral M 208]

theorem zeroRollback (k : M) (args : Fin 11 → M) (hz : args 3 = (0 : M)) :
    F PA194Stepper.stepper ![cost args,PA194Site48Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),
        F parityCode (fun _ => before k)+F sourceFileCode args+F sourceFileCode args]] := by
  let v := physicalArgs args
  let t := tailWord args
  let q := F ones ![(0 : M),t+t]
  let four : Fin 5 → M := ![v 0,v 1,v 2,v 3,(q+q)+(q+q)]
  let carried := F (PA194CarryFile.leftCode 4) (Fin.cases (before k) four)
  let z := carried+carried+1
  have htail : PA194Site48Branch.selectedTail args = t+t := by
    have ht := tailIdentity args
    change t+t = F (fileCode 5) (fun i : Fin 6 => v ⟨i.val+5,by omega⟩) at ht
    have hf : (fun i : Fin 6 => (PA194Site48MarkedFile.selectedArgs args) i.succ) = (fun i : Fin 6 => v ⟨i.val+5,by omega⟩) := by
      funext i
      fin_cases i <;> rfl
    dsimp only [PA194Site48Branch.selectedTail]
    rw [hf,←ht]
  have hmarked : F (markedFile 5) (PA194Site48MarkedFile.selectedArgs args) = (q+q)+(q+q) := by
    rw [modelMarkedFile,modelMarkedBlock]
    change (F ones ![args 3,PA194Site48Branch.selectedTail args]+F ones ![args 3,PA194Site48Branch.selectedTail args])+
      (F ones ![args 3,PA194Site48Branch.selectedTail args]+F ones ![args 3,PA194Site48Branch.selectedTail args]) = _
    rw [hz,htail]
  have hvec : PA194Site48MarkedFile.prefixArgs args = four := by
    dsimp only [PA194Site48MarkedFile.prefixArgs,four]
    rw [hmarked]
  have h4 := PA194Site48Branch.at4 k args
  dsimp only at h4
  change PA194Site48Branch.runTo4 k args = F pairCode ![modelNumeral M 4,F pairCode ![
    PA194Site48Branch.marker k args+PA194Site48Branch.marker k args,F ones ![args 3,PA194Site48Branch.selectedTail args]]] at h4
  rw [hz,htail] at h4
  have hmarker : PA194Site48Branch.marker k args = z := by
    dsimp only [PA194Site48Branch.marker,z,carried,before]
    rw [hvec]
  rw [hmarker] at h4
  have hr := PA194Site48ZeroRollbackCell.rollback (before k) (v 0) (v 1) (v 2) (v 3) (v 5) (F (fileCode 4) (fun i => v ⟨i.val+6,by omega⟩))
  dsimp only at hr
  change F PA194Stepper.stepper ![cost args,F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),F parityCode (fun _ => before k)+returned args+returned args]] at hr
  rw [returnedIsSourceFile args hz] at hr
  rw [h4,hr]
#print axioms zeroRollback
end models
end PA194Site48ZeroRollback
