import PA194ModelMPSchedule
import PA194SchedulerSourceFrame
import PA194SchedulerBranchesOpen

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ModelMPFromFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerIteration PA194SchedulerCode PA194SchedulerSourceFrame
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194SchedulerBranchesOpen

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fetch, decode and execute MP from the exact aligned scheduler frame. -/
theorem advance (s : M) (hMP : F (head fN fL) ![s] = 1) :
    ∃ c : M, 0 < c ∧ F PA194SourceControllerCode.run ![c,F frame ![s]] =
      F frame ![F PA194SchedulerIteration.step ![s]] := by
  let a := arguments s
  let next := F PA194SchedulerIteration.step ![s]
  obtain ⟨clock,out,_,hL,hN,hX,hY,_,hmp,_,hkeep⟩ :=
    fetchDecodeBranchesPreserving s a (0 : M) rfl rfl rfl rfl rfl
  let mpArgs := Function.update out 3 (0 : M)
  have hfetch : Reaches (sourceState 25 a 0) (sourceState 3554 mpArgs 0) :=
    ⟨(clock+1)+1,hmp hMP⟩
  have hn' : mpArgs 0 = F (nextN fN fL) ![s] := by
    have h := PA194ModelMPFields.nextFields s hMP
    rw [show mpArgs 0 = out 0 from Function.update_of_ne (by decide) _ _]
    exact hN.symm.trans h.1
  have ht' : mpArgs 1 = F fT ![s] := by
    rw [show mpArgs 1 = out 1 from Function.update_of_ne (by decide) _ _]
    exact hkeep 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hw' : mpArgs 2 = F fW ![s] := by
    rw [show mpArgs 2 = out 2 from Function.update_of_ne (by decide) _ _]
    exact hkeep 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hd' : mpArgs 4 = F fD ![s] := by
    rw [show mpArgs 4 = out 4 from Function.update_of_ne (by decide) _ _]
    exact hkeep 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hh' : mpArgs 5 = F fH ![s] := by
    rw [show mpArgs 5 = out 5 from Function.update_of_ne (by decide) _ _]
    exact hkeep 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hl' : mpArgs 8 = F (PA194SchedulerCode.tail fN fL) ![s] :=
    (Function.update_of_ne (by decide) _ out).trans hL.symm
  have hx' : mpArgs 6 = 0 := (Function.update_of_ne (by decide) _ out).trans hX
  have hy' : mpArgs 7 = 0 := (Function.update_of_ne (by decide) _ out).trans hY
  have htag : mpArgs 3 = 0 := Function.update_self 3 0 out
  obtain ⟨result,hbody,h0,h1,h2,h3,h4,h5,h6,h7,h8,_⟩ :=
    PA194ModelMPSchedule.commandMatches s mpArgs 0 hMP hn' ht' hw' hd' hh' hl' hx' hy'
  have he : regsOfArgs result = regsOfArgs (arguments next) := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3.trans htag
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
  have hframe : sourceState 25 result (0 : M) = F frame ![next] := by
    rw [frame_model]
    unfold sourceState
    rw [he]
  have h := appendPositive hfetch hbody
  rw [hframe] at h
  rw [frame_model s]
  exact h

#print axioms advance
end models
end PA194ModelMPFromFrame
