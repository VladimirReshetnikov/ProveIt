import PA194CompressedExecutor
import PA194FoldedRuntimeRows
import PA194RegisterSplit
import PA194MarkAll
import PA194MarkDelimiter

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedBoxFiles
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion
open PA194StateOne PA194FiniteControls TableDispatch PA194BidirectionalRow PA194SymbolicMove
open PA194BidirectionalRunScan PA194CompressedTape PA194FoldedRuntimeRows
open PA194RegisterFile PA194MarkedFile PA194RegisterSplit PA194ReturnFile PA194ReturnFileMeaning PA194CarryFile
open PA194MarkerScan PA194MarkAll PA194MarkDelimiter PA194DecrementChoice PA194UnaryRuns
open M6.Runtime

theorem skipControl (p : Fin 9) : denseControl (sk p.val) = markerControl p := by
  fin_cases p <;> decide +kernel

theorem markExitZero : denseControl (markExit 0) = 15 := by decide +kernel
theorem markExitSucc (p : Nat) : denseControl (markExit (p+1)) = 17 := by
  change denseControl 3 = 17
  decide +kernel

theorem decEntry : denseControl 0 = 1 := by decide +kernel
theorem decZeroExit : denseControl 97 = 11 := by decide +kernel
theorem decPositiveExit : denseControl 40 = 7 := by decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Physical file arguments are in tape order. The first ten values are the
nine working registers and the first spare. The last value is the packed
tail and can include any number of further spares. -/
def slot (p : Fin 9) : Fin 11 := ⟨p.val,by have := p.isLt; omega⟩

noncomputable def file (a : Fin 11 → M) : M := F (fileCode 10) a

noncomputable def rest (p : Fin 9) (a : Fin 11 → M) : M :=
  F (fileCode (8-p.val+1)) (tailArgs p a)

noncomputable def marked (p : Fin 9) (a : Fin 11 → M) : M :=
  F markedBlock ![a (slot p),rest p a]

noncomputable def markedFileValue (p : Fin 9) (a : Fin 11 → M) : M :=
  F (fileCode p.val) (frontArgs p a (marked p a))

theorem frontLast (p : Fin 9) (a : Fin 11 → M) (x : M) :
    frontArgs p a x (Fin.last p.val) = x := by
  unfold frontArgs
  rw [Fin.snoc_last]

theorem restorePrefix (p : Fin 9) (a : Fin 11 → M) (x y : M) :
    F (returnCode p.val) (Fin.cases y (frontArgs p a x)) =
      F (fileCode p.val) (frontArgs p a y) := by
  rw [modelReturnMeaning]
  unfold replaceLast frontArgs
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem ordinaryFileSplit (p : Fin 9) (a : Fin 11 → M) (v : M) :
    F (fileCode p.val) (frontArgs p a (F block ![v,rest p a])) =
      file (Function.update a (slot p) v) := by
  have h := splitFile p a v (0 : M)
  rw [restorePrefix] at h
  exact h

theorem ordinaryFileSplit_self (p : Fin 9) (a : Fin 11 → M) :
    F (fileCode p.val) (frontArgs p a (F block ![a (slot p),rest p a])) = file a := by
  rw [ordinaryFileSplit]
  congr 1
  funext i
  by_cases hi : i = slot p
  · subst i; simp
  · simp [hi]

theorem fileBoundary (a : Fin 11 → M) : ∃ tail, file a = PA194BidirectionalRow.push false tail := by
  unfold file
  rw [modelFileSucc,modelBlock]
  exact ⟨_,rfl⟩

theorem markedBoundary (p : Fin 9) (a : Fin 11 → M) :
    ∃ tail, markedFileValue p a = PA194BidirectionalRow.push false tail := by
  rcases p with ⟨p,hp⟩
  unfold markedFileValue
  cases p with
  | zero =>
    rw [show F (fileCode 0) (frontArgs ⟨0,hp⟩ a (marked ⟨0,hp⟩ a)) =
      marked ⟨0,hp⟩ a from by
      change F (.proj 0) _ = _
      rw [modelProjection]
      change Fin.snoc _ _ (Fin.last 0) = _
      rw [Fin.snoc_last]]
    rw [marked,modelMarkedBlock]
    exact ⟨_,rfl⟩
  | succ p =>
    rw [modelFileSucc,modelBlock]
    exact ⟨_,rfl⟩

theorem blockMarkForm (v t : M) :
    let s := F ones ![v,t]
    F block ![v,t] = (s+s+1)+(s+s+1) ∧
      F markedBlock ![v,t] = (s+s)+(s+s) := by
  dsimp only
  have hs := runSucc true v t
  change F ones ![v+1,t] = _ at hs
  rw [modelBlock,modelMarkedBlock,hs]
  exact ⟨rfl,rfl⟩

/-- The native mark oracle is sound at every physical register position,
with arbitrary register and packed tail values in every PRA model. -/
theorem markOracle (p : Fin 9) (a : Fin 11 → M) (l : M) :
    Reach (frame true (denseControl (sk p.val)) l (file a))
      (frame false (denseControl (markExit p.val)) (markedFileValue p a) l) := by
  rcases p with ⟨p,hp⟩
  cases p with
  | zero =>
    let p : Fin 9 := ⟨0,hp⟩
    have hc : denseControl (sk 0) = 113 := by decide +kernel
    rw [hc,markExitZero]
    let v := a (slot p)
    let t := rest p a
    let s := F ones ![v,t]
    have hform := blockMarkForm v t
    have hinput : file a = (s+s+1)+(s+s+1) := by
      rw [←ordinaryFileSplit_self p a]
      change F (.proj 0) (frontArgs p a (F block ![v,t])) = _
      rw [modelProjection]
      have hfront : frontArgs p a (F block ![v,t]) 0 = F block ![v,t] := by
        change Fin.snoc _ _ (Fin.last 0) = _
        rw [Fin.snoc_last]
      rw [hfront]
      exact hform.1
    have houtput : markedFileValue p a = (s+s)+(s+s) := by
      unfold markedFileValue
      change F (.proj 0) (frontArgs p a (marked p a)) = _
      rw [modelProjection]
      have hfront : frontArgs p a (marked p a) 0 = marked p a := by
        change Fin.snoc _ _ (Fin.last 0) = _
        rw [Fin.snoc_last]
      rw [hfront]
      exact hform.2
    refine ⟨modelNumeral M 3,?_⟩
    change F PA194Stepper.stepper ![modelNumeral M 3,frame true 113 l (file a)] =
      frame false 15 (markedFileValue p a) l
    rw [hinput,houtput]
    have h := modelMarkDelimiter l s
    simpa only [frame,packed,↓reduceIte,Bool.false_eq_true,add_assoc] using h
  | succ n =>
    let p : Fin 9 := ⟨n+1,hp⟩
    have hc := skipControl p
    change denseControl (sk (n+1)) = markerControl p at hc
    rw [hc,markExitSucc]
    let v := a (slot p)
    let t := rest p a
    let s := F ones ![v,t]
    let arg : M := F block ![v,t]
    let e := frontArgs p a arg
    have he : e (Fin.last (n+1)) = (s+s+1)+(s+s+1) := by
      have harg := frontLast p a arg
      change e (Fin.last (n+1)) = arg at harg
      exact harg.trans (blockMarkForm v t).1
    have hm := modelMarkAllPositive n hp e l s he
    dsimp only at hm
    have heIn : F (fileCode (n+1)) e = file a := ordinaryFileSplit_self p a
    rw [heIn] at hm
    have hshape : (s+s)+(s+s) = marked p a := (blockMarkForm v t).2.symm
    rw [hshape] at hm
    have hreturn : F (returnCode (n+1)) (Fin.cases (marked p a) e) = markedFileValue p a :=
      restorePrefix p a arg (marked p a)
    refine ⟨F (costCode (n+1)) e + modelNumeral M 3 + F (costCode (n+1)) e,?_⟩
    change F PA194Stepper.stepper ![_,packed (markerControl p) l (file a)] =
      frame false 17 (markedFileValue p a) l
    rw [←hreturn]
    simpa only [frame,packed,↓reduceIte,Bool.false_eq_true,add_assoc] using hm

/-- The zero decrement rolls back the mark and retains the entire file. -/
theorem decZeroOracle (p : Fin 9) (a : Fin 11 → M) (l : M) (hz : a (slot p) = 0) :
    Reach (frame true (denseControl 0) l (markedFileValue p a))
      (frame false (denseControl 97) (file a) l) := by
  classical
  let v := a (slot p)
  let ep := frontArgs p a (marked p a)
  have hp : ep (Fin.last p.val) = F markedBlock ![v,F (fileCode (8-p.val+1)) (tailArgs p a)] := by
    change Fin.snoc _ _ (Fin.last p.val) = _
    rw [Fin.snoc_last]
    rfl
  have h := modelDecrementChoice p.val (8-p.val) ep (tailArgs p a) v l hp
  dsimp only at h
  have hv : v = (0 : M) := hz
  simp only [hv,if_true] at h
  have hu : Function.update a (slot p) (0 : M) = a := by
    funext i
    by_cases hi : i = slot p
    · subst i; simp [hz]
    · simp [hi]
  have hout := splitFile p a (0 : M) (marked p a)
  change F (returnCode p.val) (Fin.cases (F block ![(0 : M),rest p a]) ep) =
    file (Function.update a (slot p) (0 : M)) at hout
  rw [hu] at hout
  refine ⟨F (costCode p.val) ep + modelNumeral M 7 + F (costCode p.val) ep,?_⟩
  simp only [decEntry,decZeroExit,frame,packed,↓reduceIte,Bool.false_eq_true,modelNumeralOne,←hout,←add_assoc]
  exact h

/-- A positive decrement changes the selected physical register and moves
the file boundary once. It retains the model-valued packed tail. -/
theorem decPositiveOracle (p : Fin 9) (a : Fin 11 → M) (l : M) (hnz : a (slot p) ≠ 0) :
    Reach (frame true (denseControl 0) l (markedFileValue p a))
      (frame false (denseControl 40)
        (file (Function.update a (slot p) (F predCode (fun _ => a (slot p)))))
        (PA194BidirectionalRow.push true l)) := by
  classical
  let v := a (slot p)
  let ep := frontArgs p a (marked p a)
  have hp : ep (Fin.last p.val) = F markedBlock ![v,F (fileCode (8-p.val+1)) (tailArgs p a)] := by
    change Fin.snoc _ _ (Fin.last p.val) = _
    rw [Fin.snoc_last]
    rfl
  have h := modelDecrementChoice p.val (8-p.val) ep (tailArgs p a) v l hp
  dsimp only at h
  have hv : v ≠ (0 : M) := hnz
  simp only [hv,if_false] at h
  let d := F predCode (fun _ => v)
  have hout := splitFile p a d (marked p a)
  change F (returnCode p.val) (Fin.cases (F block ![d,rest p a]) ep) =
    file (Function.update a (slot p) d) at hout
  refine ⟨F (costCode p.val) ep + modelNumeral M 4 + F (costCode p.val) ep,?_⟩
  rw [decEntry,decPositiveExit,leftFrameBit]
  change F PA194Stepper.stepper ![_,frame true 1 l (markedFileValue p a)] =
    packed 7 l (PA194BidirectionalRow.push true (file (Function.update a (slot p) d)))
  rw [←hout]
  simpa only [frame,packed,↓reduceIte,modelNumeralOne,PA194BidirectionalRow.push,d,v,ep,rest,markedFileValue] using h

#print axioms restorePrefix
#print axioms markOracle
#print axioms decZeroOracle
#print axioms decPositiveOracle
end models
end PA194CompressedBoxFiles
