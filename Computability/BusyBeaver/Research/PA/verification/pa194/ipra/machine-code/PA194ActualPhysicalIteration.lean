import PA194ActualLoopOneStep
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualPhysicalIteration
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
open PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem physicalOrbit (c27 : Code 12) (c28 c29 : Code 13) (r : Fin 9 → M) (tail g n spare steps : M)
    (hstep : let x := packed g n spare (PA194ModelSourceLoop.source r tail)
      ∀ i, i < r 0 →
        F PA194Stepper.stepper ![F (loopCost c27 c28 c29 PA194ControllerLoopFrame.readers)
          (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![i,x]),
          F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers)
            (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![i,x])] =
        F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers)
          (fun _ => F (PA194ModelLoopState.next quad) (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![i,x])))
    (h : steps ≤ r 0) :
    let x := packed g n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    let a' := frameArgs (PA194ModelSourceLoop.running r steps) ((n+steps)+steps) spare
    F PA194Stepper.stepper ![F (timeCode (PA194ModelLoopState.next quad)
      (loopCost c27 c28 c29 PA194ControllerLoopFrame.readers)) ![steps,x],physicalFrame 27 g a] =
        physicalFrame 27 (g+steps) a' := by
  dsimp only at hstep ⊢
  let x := packed g n spare (PA194ModelSourceLoop.source r tail)
  let a := frameArgs r n spare
  let a' := frameArgs (PA194ModelSourceLoop.running r steps) ((n+steps)+steps) spare
  have hi := PA194ModelLoopIteration.modelIteration (M := M) (PA194ModelLoopState.next quad)
    (loopCost c27 c28 c29 PA194ControllerLoopFrame.readers) (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers)
    (r 0) x steps hstep h
  have ho := PA194ActualLoopOrbit.frameOrbit r tail g n spare steps h
  dsimp only at ho
  change F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers)
    (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![steps,x]) = physicalFrame 27 (g+steps) a' at ho
  have ht : a 10 = F repeatOutput ![n,(0 : M)] := by simp [a,frameArgs]
  have hs : a 9 = spare := by simp [a,frameArgs]
  have hc := PA194ActualLoopOrbit.controllerSource r n spare tail
  have hf := PA194ControllerLoopFrame.frameSource a g n tail ht
  rw [hs,hc] at hf
  change F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => x) = physicalFrame 27 g a at hf
  rw [←hf]
  exact hi.trans ho
#print axioms physicalOrbit
end models
end PA194ActualPhysicalIteration
