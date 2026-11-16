import PA194RepeatedSpareIncrement
import PA194RegisterSplit

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace PA194RepeatedSpareFileIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194IncrementFront PA194ReturnFile PA194ReturnFileMeaning PA194ReturnCell PA194OnesCommute
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

open PA194RegisterSplit PA194CompressedTape PA194BidirectionalRunScan

private theorem suffix_index (p : Fin 9) :
    (⟨p.val+1+(Fin.last (8-p.val+1)).val, by have := p.isLt; simp; omega⟩ : Fin 11) = 10 := by
  apply Fin.ext
  have := p.isLt
  simp
  omega

private theorem tailArgs_update_last (p : Fin 9) (a : Fin 11 → M) (t : M) :
    replaceLast (8-p.val+1) (tailArgs p a) t = tailArgs p (Function.update a 10 t) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [replaceLast, Fin.snoc_last, tailArgs, suffix_index, Function.update_self]
  · have hj : (⟨p.val+1+j.val, by have := p.isLt; have := j.isLt; omega⟩ : Fin 11) ≠ 10 := by
      intro he
      have h := congrArg Fin.val he
      have := p.isLt
      have := j.isLt
      simp at h
      omega
    simp [replaceLast, tailArgs, Function.update, hj]

private theorem frontArgs_update_last (p : Fin 9) (a : Fin 11 → M) (x t : M) :
    frontArgs p a x = frontArgs p (Function.update a 10 t) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [frontArgs]
  · have hj : (⟨j.val, by have := p.isLt; have := j.isLt; omega⟩ : Fin 11) ≠ 10 := by
      intro he
      have h := congrArg Fin.val he
      have := p.isLt
      have := j.isLt
      simp at h
      omega
    simp [frontArgs, Function.update, hj]

private abbrev slot (p : Fin 9) : Fin 11 := ⟨p.val,by have := p.isLt; omega⟩
private abbrev following (p : Fin 9) := 8-p.val+1
private abbrev selection (p : Fin 9) (a : Fin 11 → M) : Fin (following p+2) → M :=
  Fin.cons (a (slot p)) (tailArgs p a)

private theorem selectionLast (p : Fin 9) (a : Fin 11 → M) :
    selection p a (Fin.last (following p+1)) = a 10 := by
  have hl : Fin.last (following p+1) = (Fin.last (following p)).succ := Fin.ext rfl
  rw [hl]
  exact congrArg a (suffix_index p)

private theorem normalizedOutput (p : Fin 9) (a : Fin 11 → M) (val mark tail : M) :
    F (returnCode p.val) (Fin.cases
      (F block ![val,F (returnCode (following p)) (Fin.cases tail (tailArgs p a))])
      (frontArgs p a mark)) =
    F (fileCode 10) (Function.update (Function.update a 10 tail) (slot p) val) := by
  have hs := splitFile p (Function.update a 10 tail) val mark
  rw [← frontArgs_update_last p a mark tail] at hs
  rw [modelReturnMeaning (following p) (tailArgs p a) tail, tailArgs_update_last p a tail]
  exact hs

/-- Increment of any of the nine working registers, preserving the tenth
ordinary block and appending one trailing spare. -/
theorem incrementOracle (p : Fin 9) (a : Fin 11 → M) (count l : M)
    (hTail : a 10 = F repeatOutput ![count,(0 : M)]) :
    let i : Fin 11 := ⟨p.val,by have := p.isLt; omega⟩
    let marked := F markedBlock ![a i,F (fileCode (8-p.val+1)) (tailArgs p a)]
    let suffix := F repeatOutput ![count+1,(0 : M)]
    Reach (frame true 2 l (F (fileCode p.val) (frontArgs p a marked)))
      (frame false 7 (F (fileCode 10) (Function.update (Function.update a 10 suffix) i (a i+1))) l) := by
  let m := following p
  let e := selection p a
  let i := slot p
  let marked := F markedBlock ![a i,F (fileCode m) (tailArgs p a)]
  let ep := frontArgs p a marked
  have hm : ep (Fin.last p.val) = F (markedFile m) e := by
    rw [modelMarkedFile m e]
    exact Fin.snoc_last _ _
  have he : e (Fin.last (m+1)) = F repeatOutput ![count,(0 : M)] := (selectionLast p a).trans hTail
  have h := PA194RepeatedSpareIncrement.incrementAnywhere p.val m count l ep e hm he
  dsimp only at h
  let t := F repeatOutput ![count+1,(0 : M)]
  have hout := normalizedOutput p a (a i+1) marked t
  have hpost := congrArg (fun y => frame false 7 y l) hout
  exact Eq.mp (congrArg (Reach (frame true 2 l (F (fileCode p.val) ep))) hpost) h

#print axioms incrementOracle
end models
end PA194RepeatedSpareFileIncrement
