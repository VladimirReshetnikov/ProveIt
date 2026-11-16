import PA194Site3664Branch
import PA194Site3664ZeroRollbackCell
import PA194Site3664ZeroFile
import PA194MarkedFile
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site3664ZeroRollback
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194MarkedFile PA194ReturnFile PA194Site3664ZeroFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
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
  F addCode ![F addCode ![modelNumeral M 1,modelNumeral M 2],F (PA194CarryFile.costCode 8) (three args)]
noncomputable def before (k : M) : M := F ones ![k+1,modelNumeral M 880]

theorem zeroRollback (k : M) (args : Fin 11 → M) (hz : args 5 = (0 : M)) :
    F PA194Stepper.stepper ![cost args,PA194Site3664Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),
        F parityCode (fun _ => before k)+F sourceFileCode args+F sourceFileCode args]] := by
  let v := physicalArgs args
  let t := tailWord args
  let q := F ones ![(0 : M),t+t]
  let two : Fin 8 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,(q+q)+(q+q)]
  let carried := F (PA194CarryFile.leftCode 7) (Fin.cases (before k) two)
  let z := carried+carried+1
  have htail : PA194Site3664Branch.selectedTail args = t+t := by
    have ht := tailIdentity args
    change t+t = F (fileCode 2) (fun i : Fin 3 => v ⟨i.val+8,by omega⟩) at ht
    have hf : (fun i : Fin 3 => (PA194Site3664MarkedFile.selectedArgs args) i.succ) = (fun i : Fin 3 => v ⟨i.val+8,by omega⟩) := by
      funext i
      fin_cases i <;> rfl
    dsimp only [PA194Site3664Branch.selectedTail]
    rw [hf,←ht]
  have hmarked : F (markedFile 2) (PA194Site3664MarkedFile.selectedArgs args) = (q+q)+(q+q) := by
    rw [modelMarkedFile,modelMarkedBlock]
    change (F ones ![args 5,PA194Site3664Branch.selectedTail args]+F ones ![args 5,PA194Site3664Branch.selectedTail args])+
      (F ones ![args 5,PA194Site3664Branch.selectedTail args]+F ones ![args 5,PA194Site3664Branch.selectedTail args]) = _
    rw [hz,htail]
  have hvec : PA194Site3664MarkedFile.prefixArgs args = two := by
    dsimp only [PA194Site3664MarkedFile.prefixArgs,two]
    rw [hmarked]
  have h4 := PA194Site3664Branch.at4 k args
  dsimp only at h4
  change PA194Site3664Branch.runTo4 k args = F pairCode ![modelNumeral M 4,F pairCode ![
    PA194Site3664Branch.marker k args+PA194Site3664Branch.marker k args,F ones ![args 5,PA194Site3664Branch.selectedTail args]]] at h4
  rw [hz,htail] at h4
  have hmarker : PA194Site3664Branch.marker k args = z := by
    dsimp only [PA194Site3664Branch.marker,z,carried,before]
    rw [hvec]
  rw [hmarker] at h4
  have hr := PA194Site3664ZeroRollbackCell.rollback (before k) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 8) (F (fileCode 1) (fun i => v ⟨i.val+9,by omega⟩))
  dsimp only at hr
  change F PA194Stepper.stepper ![cost args,F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),F parityCode (fun _ => before k)+returned args+returned args]] at hr
  rw [returnedIsSourceFile args hz] at hr
  rw [h4,hr]
#print axioms zeroRollback
end models
end PA194Site3664ZeroRollback
