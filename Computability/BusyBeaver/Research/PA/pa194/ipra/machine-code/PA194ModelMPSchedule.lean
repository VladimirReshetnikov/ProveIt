import PA194ModelMPCommand

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ModelMPSchedule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelMPCommand PA194ModelMPField
open PA194MachineProjections PA194TargetCantor PA194SchedulerCode PA194SchedulerIteration

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

theorem resultFields (a : Fin 11 → M) :
    let b := result a
    let d := a 4 + F fixedFirst ![a 8]
    let ok := impValue (a 1) d = a 5
    b 0 = a 0 ∧ b 1 = (if ok then d else 0) ∧
    b 2 = (if ok then cantor 0 (a 2) else a 2) ∧
    b 3 = a 3 ∧ b 4 = d ∧ b 5 = 0 ∧
    b 6 = a 6 ∧ b 7 = a 7 ∧ b 8 = F fixedSecond ![a 8] := by
  classical
  simp [result,fieldArgs]

/-- At the actual MP entry, the source machine implements the exact modeled
scheduler store update and returns to the dispatch frame. -/
theorem commandMatches (s : M) (a : Fin 11 → M) (tail : M)
    (tag : F (head fN fL) ![s] = 1)
    (hN : a 0 = F (nextN fN fL) ![s])
    (hT : a 1 = F fT ![s]) (hW : a 2 = F fW ![s])
    (hD : a 4 = F fD ![s]) (hH : a 5 = F fH ![s])
    (hL : a 8 = F (PA194SchedulerCode.tail fN fL) ![s])
    (hX : a 6 = 0) (hY : a 7 = 0) :
    let ns := F step ![s]
    ∃ out : Fin 11 → M,
      ReachesPositive (sourceState 3554 a tail) (sourceState 25 out tail) ∧
      out 0 = F fN ![ns] ∧ out 1 = F fT ![ns] ∧ out 2 = F fW ![ns] ∧
      out 3 = a 3 ∧ out 4 = F fD ![ns] ∧ out 5 = F fH ![ns] ∧
      out 6 = 0 ∧ out 7 = 0 ∧ out 8 = F fL ![ns] ∧ F haltAt ![s] = 0 := by
  have hf := resultFields a
  dsimp only at hf
  rw [hN,hT,hW,hD,hH,hL,hX,hY] at hf
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := hf
  obtain ⟨n,l,t,w,d,h,stop⟩ := PA194ModelMPFields.nextFields s tag
  exact ⟨result a,command a tail hX hY,h0.trans n.symm,h1.trans t.symm,h2.trans w.symm,
    h3,h4.trans d.symm,h5.trans h.symm,h6,h7,h8.trans l.symm,stop⟩

#print axioms commandMatches
end models
end PA194ModelMPSchedule
