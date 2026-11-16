import PA194Site35RestoreEntryExists
import PA194SeedValues
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedToFirstSite35
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ModelLoopIteration PA194SeedFrameAlignment PA194ModelSourceLoop PA194ActualLoopOrbit PA194SourceSite31Physical PA194RegisterPermutation PA194OneSpareReturn PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def r31 : Fin 9 → M := running (seedRegs (M := M)) (seedRegs 0)
noncomputable def k31 : M := modelNumeral M 39+seedRegs (M := M) 0
noncomputable def n31 : M := (modelNumeral M 27+seedRegs (M := M) 0)+seedRegs 0
noncomputable def spare : M := seedArgs30 (M := M) 9
noncomputable def out34 : Fin 11 → M :=
  let r' := PA194ModelRestoreSource.running (r31 (M := M)) (r31 6)
  let n' := n31 (M := M)+r31 6
  PA194Site31OutputFile.updated (frameArgs r' n' (spare (M := M))) n'
noncomputable def next35 : Fin 11 → M := Function.update (out34 (M := M)) 8 (1 : M)
noncomputable def count35 : M := F Code.succ (fun _ => n31 (M := M)+r31 6)

theorem blankTo35 (tail : M) :
    ∃ c0 c1 c2 c3 : M,
      F PA194Stepper.stepper ![c3,F PA194Stepper.stepper ![c2,F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,modelNumeral M 0]]]] =
        physicalFrame 35 (((modelNumeral M 42+1)+1)+1) (next35 (M := M)) ∧
      physicalArgs (next35 (M := M)) 10 = F repeatOutput ![count35 (M := M),(0 : M)] := by
  have hseed := PA194SeedToFirstRestore.blankToFirstRestore (M := M) tail
  dsimp only at hseed
  obtain ⟨_,c0,c1,h31⟩ := hseed
  have hguard : out34 (M := M) 8 = (1 : M)+1 := by
    exact PA194SeedValues.firstSite34Guard (M := M)
  have hentry := PA194Site35RestoreEntryExists.existsRestoreFeedsSite35 (r31 (M := M)) tail (k31 (M := M)) (n31 (M := M)) (spare (M := M)) (1 : M) hguard
  dsimp only at hentry
  obtain ⟨c2,c3,h35,hsuffix⟩ := hentry
  have hgap := PA194SeedValues.firstSite36Gap (M := M)
  dsimp only at hgap
  change k31 (M := M)+r31 6 = modelNumeral M 42 at hgap
  rw [hgap] at h35
  refine ⟨c0,c1,c2,c3,?_,?_⟩
  · rw [h31]
    exact h35
  · exact hsuffix
#print axioms blankTo35
end models
end PA194SeedToFirstSite35
