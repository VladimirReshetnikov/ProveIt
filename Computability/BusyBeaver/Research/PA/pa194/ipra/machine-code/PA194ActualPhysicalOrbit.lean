import PA194ActualPhysicalIteration
import PA194ActualLoopExactStep
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194ActualPhysicalOrbit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
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

theorem physicalOrbit (r : Fin 9 → M) (tail k n spare steps : M) (h : steps ≤ r 0) :
    let g := (((k+1)+1)+1)
    let x := packed g n spare (PA194ModelSourceLoop.source r tail)
    let a := frameArgs r n spare
    let a' := frameArgs (PA194ModelSourceLoop.running r steps) ((n+steps)+steps) spare
    F PA194Stepper.stepper ![F (timeCode (PA194ModelLoopState.next quad)
      (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers)) ![steps,x],physicalFrame 27 g a] =
        physicalFrame 27 (g+steps) a' := by
  let g := (((k+1)+1)+1)
  have hstep : let x := packed g n spare (PA194ModelSourceLoop.source r tail)
      ∀ i, i < r 0 →
        F PA194Stepper.stepper ![F (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers)
          (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![i,x]),
          F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers)
            (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![i,x])] =
        F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers)
          (fun _ => F (PA194ModelLoopState.next quad) (fun _ => F (iterCode (PA194ModelLoopState.next quad)) ![i,x])) := by
    dsimp only
    intro i hi
    let m := F predCode (fun _ => F subCode ![r 0,i])
    have hp : (0 : M) < F subCode ![r 0,i] := by
      rw [modelSubAsTsub]
      exact tsub_pos_of_lt hi
    have hs := (PRAExhaustion.modelZeroOrSuccPred (F subCode ![r 0,i])).resolve_left (ne_of_gt hp)
    rw [←modelAddOne] at hs
    change m+1 = F subCode ![r 0,i] at hs
    have hm : running r i 0 = m+1 := by
      change F subCode ![r 0,i] = m+1
      exact hs.symm
    have hiter := PA194ModelLoopState.iterPacked (M := M) quad i g n spare (PA194ModelSourceLoop.source r tail)
    rw [PA194ActualSourceLoop.sourceIteration r tail i (le_of_lt hi)] at hiter
    have hg : g+i = ((((k+i)+1)+1)+1) := by dsimp [g]; simp [add_assoc,add_comm,add_left_comm]
    have hexact := PA194ActualLoopExactStep.exactOneStep (running r i) tail (k+i) ((n+i)+i) spare m hm
    dsimp only at hexact
    rw [hiter,hg]
    exact hexact
  exact PA194ActualPhysicalIteration.physicalOrbit PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode r tail g n spare steps hstep h
#print axioms physicalOrbit
end models
end PA194ActualPhysicalOrbit
