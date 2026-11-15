import PA194ActualLoopNextFrame
import PA194ModelLoopCost
import PA194SourceSite30Physical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualLoopOneStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch
open PA194SourceSite25Physical PA194SourceSite30Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem oneStep (c27 : Code 12) (c28 c29 : Code 13) (r : Fin 9 → M) (tail k n spare m : M)
    (hm : r 0 = m+1)
    (h27 : let a := frameArgs r n spare
      let a28 := Function.update a 0 m
      F PA194Stepper.stepper ![F c27 (Fin.cases (k+1) (Fin.cases m (fun i : Fin 10 => a i.succ))),physicalFrame 27 (((k+1)+1)+1) a] = physicalFrame 28 (((k+1)+1)+1) a28)
    (h28 : let a := frameArgs r n spare
      let a28 := Function.update a 0 m
      let a29 := PA194Site28DynamicOutput.updated a28 n
      F PA194Stepper.stepper ![F c28 (Fin.cases (k+1) (Fin.cases n a28)),physicalFrame 28 (((k+1)+1)+1) a28] = physicalFrame 29 ((k+1)+1) a29)
    (h29 : let a := frameArgs r n spare
      let a28 := Function.update a 0 m
      let a29 := PA194Site28DynamicOutput.updated a28 n
      let out := PA194Site29DynamicOutput.updated a29 (n+1)
      F PA194Stepper.stepper ![F c29 (Fin.cases k (Fin.cases (n+1) a29)),physicalFrame 29 ((k+1)+1) a29] = physicalFrame 30 ((k+1)+1) out) :
    let x := packed (((k+1)+1)+1) n spare (PA194ModelSourceLoop.source r tail)
    F PA194Stepper.stepper ![F (loopCost c27 c28 c29 PA194ControllerLoopFrame.readers) (fun _ => x),
      F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => x)] =
      F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => F (PA194ModelLoopState.next quad) (fun _ => x)) := by
  dsimp only at h27 h28 h29 ⊢
  let x := packed (((k+1)+1)+1) n spare (PA194ModelSourceLoop.source r tail)
  let a := frameArgs r n spare
  let a28 := Function.update a 0 m
  let a29 := PA194Site28DynamicOutput.updated a28 n
  let out := PA194Site29DynamicOutput.updated a29 (n+1)
  let e27 : Fin 12 → M := Fin.cases (k+1) (Fin.cases m (fun i : Fin 10 => a i.succ))
  let e28 : Fin 13 → M := Fin.cases (k+1) (Fin.cases n a28)
  let e29 : Fin 13 → M := Fin.cases k (Fin.cases (n+1) a29)
  have hin := PA194ActualLoopCostInputs.inputs r tail k n spare m hm
  dsimp only at hin
  have hc := PA194ModelLoopCost.modelLoopCost c27 c28 c29 PA194ControllerLoopFrame.readers x
  rw [hin.1,hin.2.1,hin.2.2] at hc
  have ha29 : a29 = Function.update (Function.update a28 8 (a28 8+1)) 10 (F repeatOutput ![n+1,(0 : M)]) := by
    funext i
    fin_cases i <;> simp [a29,PA194Site28DynamicOutput.updated,←modelAddOne] <;> rfl
  rw [←ha29] at hc
  change F (loopCost c27 c28 c29 PA194ControllerLoopFrame.readers) (fun _ => x) = ((F c27 e27+F c28 e28)+F c29 e29)+modelNumeral M 40 at hc
  have htail : a 10 = F repeatOutput ![n,(0 : M)] := by simp [a,frameArgs]
  have hspare : a 9 = spare := by simp [a,frameArgs]
  have hs := PA194ActualLoopOrbit.controllerSource r n spare tail
  have hframe := PA194ControllerLoopFrame.frameSource a (((k+1)+1)+1) n tail htail
  rw [hspare,hs] at hframe
  change F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => x) = physicalFrame 27 (((k+1)+1)+1) a at hframe
  have hnext := PA194ActualLoopNextFrame.nextFrame r tail k n spare m hm
  dsimp only at hnext
  change F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => F (PA194ModelLoopState.next quad) (fun _ => x)) = physicalFrame 27 ((((k+1)+1)+1)+1) out at hnext
  have h30 := (PA194SourceSite30Physical.sourcePhysical k tail out).2
  change F PA194Stepper.stepper ![F c27 e27,physicalFrame 27 (((k+1)+1)+1) a] = physicalFrame 28 (((k+1)+1)+1) a28 at h27
  change F PA194Stepper.stepper ![F c28 e28,physicalFrame 28 (((k+1)+1)+1) a28] = physicalFrame 29 ((k+1)+1) a29 at h28
  change F PA194Stepper.stepper ![F c29 e29,physicalFrame 29 ((k+1)+1) a29] = physicalFrame 30 ((k+1)+1) out at h29
  have hp : F PA194Stepper.stepper ![modelNumeral M 40,F PA194Stepper.stepper ![F c29 e29,
      F PA194Stepper.stepper ![F c28 e28,F PA194Stepper.stepper ![F c27 e27,
        F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => x)]]]] =
        physicalFrame 27 ((((k+1)+1)+1)+1) out := by
    rw [hframe,h27,h28,h29,h30]
  simp only [←PA194StepperCompose.modelStepperCompose] at hp
  change F PA194Stepper.stepper ![((F c27 e27+F c28 e28)+F c29 e29)+modelNumeral M 40,
    F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => x)] =
    physicalFrame 27 ((((k+1)+1)+1)+1) out at hp
  rw [←hc,←hnext] at hp
  exact hp
#print axioms oneStep
end models
end PA194ActualLoopOneStep
