import PA194SeedControllerReturn27
import PA194OneSpareSeed26
import PA194ActualLoopOrbit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedFrameAlignment
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StartupSourceFrame PA194ActualLoopOrbit PA194OneSpareSeed26 PA194OneSpareReturn PA194RegisterFile PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def seedArgs30 : Fin 11 → M :=
  let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
  let args29 := PA194Site28OutputFile.updated (Function.update e 0 (1 : M))
  PA194Site29OutputWithCarry.updated args29
noncomputable def seedRegs : Fin 9 → M := fun i => seedArgs30 ⟨i.val,by have h:=i.isLt;omega⟩

theorem seed27 : F repeatOutput ![modelNumeral M 27,(0 : M)] = F block ![(1 : M),F block ![(1 : M),modelNumeral M seedTail]] := by
  change F repeatOutput ![F Code.succ (fun _ => modelNumeral M 26),(0 : M)] = _
  rw [modelOutputSucc,modelOutputBlock,modelSeed26]

theorem seedFrame : frameArgs (seedRegs (M := M)) (modelNumeral M 27) (seedArgs30 (M := M) 9) = seedArgs30 := by
  have hs : seedArgs30 (M := M) 10 = F repeatOutput ![modelNumeral M 27,(0 : M)] := by
    rw [seed27]
    simp [seedArgs30,PA194Site29OutputWithCarry.updated]
  funext i
  fin_cases i <;> simp [frameArgs,PA194ActualSourceLoop.args,seedRegs,hs]
#print axioms seed27
#print axioms seedFrame
end models
end PA194SeedFrameAlignment
