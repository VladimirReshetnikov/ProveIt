import PA194ActualLoopOneStep
import PA194Site27ClockDirect
import PA194Site28ClockCode
import PA194Site29ClockCode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194ActualLoopExactStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ActualLoopOneStep PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch
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

theorem exactOneStep (r : Fin 9 → M) (tail k n spare m : M) (hm : r 0 = m+1) :
    let x := packed (((k+1)+1)+1) n spare (PA194ModelSourceLoop.source r tail)
    F PA194Stepper.stepper ![F (loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers) (fun _ => x),
      F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => x)] =
      F (PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers) (fun _ => F (PA194ModelLoopState.next quad) (fun _ => x)) := by
  let a := frameArgs r n spare
  let a28 := Function.update a 0 m
  let a29 := PA194Site28DynamicOutput.updated a28 n
  let out := PA194Site29DynamicOutput.updated a29 (n+1)
  let e27 : Fin 12 → M := Fin.cases (k+1) (Fin.cases m (fun i : Fin 10 => a i.succ))
  let e28 : Fin 13 → M := Fin.cases (k+1) (Fin.cases n a28)
  let e29 : Fin 13 → M := Fin.cases k (Fin.cases (n+1) a29)
  have ht : a 10 = F repeatOutput ![n,(0 : M)] := by simp [a,frameArgs]
  have ht28 : a28 10 = F repeatOutput ![n,(0 : M)] := by simp [a28,ht]
  have ht29 : a29 10 = F repeatOutput ![n+1,(0 : M)] := by
    simp [a29,PA194Site28DynamicOutput.updated,←modelAddOne]
    rfl
  have ha0 : a 0 = m+1 := by simpa [a,frameArgs,PA194ActualSourceLoop.args] using hm
  have hes : (fun i => Semiterm.val e27 Empty.elim (PA194Site27ClockDirect.args i)) = a := by
    funext i
    fin_cases i <;> simp [PA194Site27ClockDirect.args,e27,PA194StartupSentence.valApp2,PA194StartupSentence.valOne,
      Semiterm.val_bvar,ha0] <;> rfl
  have heu : (fun i => Semiterm.val e27 Empty.elim (PA194Site27ClockDirect.updatedArgs i)) = a28 := by
    funext i
    by_cases hi : i=0
    · subst i
      simp [PA194Site27ClockDirect.updatedArgs,a28,e27]
      rfl
    · have h := congrFun hes i
      simp [PA194Site27ClockDirect.updatedArgs,a28,hi,Function.update_of_ne hi] at h ⊢
      exact h
  have he270 : e27 0 = k+1 := by rfl
  have h27 := PA194Site27ClockDirect.exactClock (M := M) e27
  dsimp only at h27
  rw [hes,heu,he270] at h27
  change F PA194Stepper.stepper ![F PA194Site27ClockDirect.clockCode e27,physicalFrame 27 (((k+1)+1)+1) a] = physicalFrame 28 (((k+1)+1)+1) a28 at h27
  have h28code := PA194Site28ClockCode.modelClock (M := M) e28
  have he280 : e28 0 = k+1 := by rfl
  have he281 : e28 1 = n := by rfl
  have he28rest : (fun i : Fin 11 => e28 ⟨i.val+2,by omega⟩) = a28 := by funext i; rfl
  rw [he280,he281,he28rest] at h28code
  have h28 := PA194Site28DynamicClock.exactClock (M := M) (k+1) n a28 ht28
  rw [←h28code] at h28
  change F PA194Stepper.stepper ![F PA194Site28ClockCode.clockCode e28,physicalFrame 28 (((k+1)+1)+1) a28] = physicalFrame 29 ((k+1)+1) a29 at h28
  have h29code := PA194Site29ClockCode.modelClock (M := M) e29
  have he290 : e29 0 = k := by rfl
  have he291 : e29 1 = n+1 := by rfl
  have he29rest : (fun i : Fin 11 => e29 ⟨i.val+2,by omega⟩) = a29 := by funext i; rfl
  rw [he290,he291,he29rest] at h29code
  have ht29' : PA194RegisterPermutation.physicalArgs a29 10 = F repeatOutput ![n+1,(0 : M)] := by
    rw [PA194RegisterPermutation.sourceSuffixAt]
    exact ht29
  have h29 := PA194Site29DynamicClock.exactClock (M := M) k (n+1) a29 ht29'
  rw [←h29code] at h29
  change F PA194Stepper.stepper ![F PA194Site29ClockCode.clockCode e29,physicalFrame 29 ((k+1)+1) a29] = physicalFrame 30 ((k+1)+1) out at h29
  exact PA194ActualLoopOneStep.oneStep PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode r tail k n spare m hm h27 h28 h29
#print axioms exactOneStep
end models
end PA194ActualLoopExactStep
