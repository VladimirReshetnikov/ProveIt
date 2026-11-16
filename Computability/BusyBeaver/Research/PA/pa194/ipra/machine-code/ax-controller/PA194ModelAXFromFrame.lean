import PA194ModelAXGate
import PA194ModelAXFields
import PA194SchedulerSourceFrame
import PA194SchedulerBranchesOpen

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace PA194ModelAXFromFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerIteration PA194SchedulerCode PA194SchedulerSourceFrame
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194SchedulerBranchesOpen
open PA194TargetCantor PA194TargetGate PA194MachineStack PA194MachineProjections PA194PathIterator

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

/-- Register file at the final AX gate. The two unused positions of the
argument vector have no effect on the encoded source state. -/
noncomputable def bodyResult (a : Fin 11 → M) : Fin 11 → M :=
  let field := F fixedSecond ![a 8]
  let d := a 4 + F fixedFirst ![field]
  let h := a 5 + F fixedFirst ![a 8]
  ![a 0,oldBundleValue h d (a 3),axStack d h (a 3) (a 4) (a 5) (a 1) (a 2),
    a 3,d,h,0,0,F fixedSecond ![field],a 9,a 10]

/-- The remaining body contract for the source AX instruction. -/
def Body : Prop :=
  ∀ (a : Fin 11 → M) (tail : M), a 6 = 0 → a 7 = 0 →
    Reaches (sourceState 50 a tail) (sourceState 3519 (bodyResult a) tail)

private theorem unaryValue (f g : Code 1) (s : M) :
    F (unary f g) ![s] = F f ![F g ![s]] := by
  rw [PA194PathIterator.modelUnary]
  apply congrArg (F f)
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem resultFields (s c : M) (a : Fin 11 → M)
    (hT : a 1 = F fT ![s]) (hW : a 2 = F fW ![s]) (hA : a 3 = c)
    (hD : a 4 = F fD ![s]) (hH : a 5 = F fH ![s])
    (hL : a 8 = F (PA194SchedulerCode.tail fN fL) ![s]) :
    let out := PA194ModelAXGate.result (bodyResult a)
    out 0 = a 0 ∧
    out 1 = axTop (F fH ![s]+F (yArg fN fL) ![s]) (F fD ![s]+F (xArg fN fL) ![s]) c ∧
    out 2 = axStack (F fD ![s]+F (xArg fN fL) ![s]) (F fH ![s]+F (yArg fN fL) ![s])
      c (F fD ![s]) (F fH ![s]) (F fT ![s]) (F fW ![s]) ∧
    out 3 = 0 ∧ out 4 = 0 ∧ out 5 = 0 ∧ out 6 = 0 ∧ out 7 = 0 ∧ out 8 = F (tail3 fN fL) ![s] := by
  let b := bodyResult a
  have ht : b 1 = oldBundleValue (b 5) (b 4) (b 3) := rfl
  have htop := PA194ModelAXGate.resultTop b ht
  have h0 := PA194ModelAXGate.resultKeeps b 0 (by simp)
  have h2 := PA194ModelAXGate.resultKeeps b 2 (by simp)
  have h8 := PA194ModelAXGate.resultKeeps b 8 (by simp)
  have h3 := PA194ModelAXGate.resultClears b 3 (by simp)
  have h4 := PA194ModelAXGate.resultClears b 4 (by simp)
  have h5 := PA194ModelAXGate.resultClears b 5 (by simp)
  have h6 := PA194ModelAXGate.resultClears b 6 (by simp)
  have h7 := PA194ModelAXGate.resultClears b 7 (by simp)
  refine ⟨h0,?_,?_,h3,h4,h5,h6,h7,?_⟩
  · simpa [b,bodyResult,hA,hD,hH,hL,yArg,xArg,tail2,unaryValue] using htop
  · simpa [b,bodyResult,hT,hW,hA,hD,hH,hL,yArg,xArg,tail2,unaryValue] using h2
  · simpa [b,bodyResult,hL,tail2,tail3,unaryValue] using h8

/-- Fetch and decode an AX tag, execute the body, then apply the verified
literal gate and recover the next exact scheduler frame. -/
theorem advance (s c : M) (htag : F (head fN fL) ![s] = (c+1)+1) (body : Body (M := M)) :
    ∃ k : M, 0 < k ∧ F PA194SourceControllerCode.run ![k,F frame ![s]] =
      F frame ![F PA194SchedulerIteration.step ![s]] := by
  let initial := arguments s
  let next := F PA194SchedulerIteration.step ![s]
  obtain ⟨clock,out,_,hL,hN,hX,hY,_,_,hax,hkeep⟩ :=
    fetchDecodeBranchesPreserving s initial (0 : M) rfl rfl rfl rfl rfl
  let a := Function.update out 3 c
  have hfetch : Reaches (sourceState 25 initial 0) (sourceState 50 a 0) :=
    ⟨(clock+1)+1,hax c htag⟩
  have h0 : a 0 = F fN ![next] :=
    (Function.update_of_ne (by decide) c out).trans hN.symm
  have h1 : a 1 = F fT ![s] :=
    (Function.update_of_ne (by decide) c out).trans
      (hkeep 1 (by decide) (by decide) (by decide) (by decide) (by decide))
  have h2 : a 2 = F fW ![s] :=
    (Function.update_of_ne (by decide) c out).trans
      (hkeep 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  have h3 : a 3 = c := Function.update_self 3 c out
  have h4 : a 4 = F fD ![s] :=
    (Function.update_of_ne (by decide) c out).trans
      (hkeep 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  have h5 : a 5 = F fH ![s] :=
    (Function.update_of_ne (by decide) c out).trans
      (hkeep 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  have h8 : a 8 = F (PA194SchedulerCode.tail fN fL) ![s] :=
    (Function.update_of_ne (by decide) c out).trans hL.symm
  have hx : a 6 = 0 := (Function.update_of_ne (by decide) c out).trans hX
  have hy : a 7 = 0 := (Function.update_of_ne (by decide) c out).trans hY
  have hbody := body a 0 hx hy
  have hgate := PA194ModelAXGate.returnToDispatch (bodyResult a) (0 : M) rfl rfl
  let result := PA194ModelAXGate.result (bodyResult a)
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8⟩ := resultFields s c a h1 h2 h3 h4 h5 h8
  obtain ⟨_,nL,nT,nW,nD,nH,_⟩ := PA194ModelAXFields.nextFields s c htag
  have he : regsOfArgs result = regsOfArgs (arguments next) := by
    funext i
    fin_cases i
    · exact r0.trans h0
    · exact r1.trans nT.symm
    · exact r2.trans nW.symm
    · exact r3
    · exact r4.trans nD.symm
    · exact r5.trans nH.symm
    · exact r6
    · exact r7
    · exact r8.trans nL.symm
  have hframe : sourceState 25 result (0 : M) = F frame ![next] := by
    rw [frame_model]
    unfold sourceState
    rw [he]
  have h := appendPositive (append hfetch hbody) hgate
  change ReachesPositive (sourceState 25 initial 0) (sourceState 25 result 0) at h
  rw [hframe] at h
  rw [frame_model s]
  exact h

#print axioms advance
end models
end PA194ModelAXFromFrame
