import PA194ORSpareSweep
import PA194CompressedIncrementOracle

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 6500000
set_option linter.unusedSectionVars false

namespace PA194ORBoxAgreement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAExhaustion
open PA194ORRegisterFile PA194RegisterFile
open PA194MarkedFile PA194RegisterSplit PA194CompressedBoxFiles
open PA194CompressedBoxOracle PA194CompressedIncrementOracle
open PA194OneSpareReturn PA194ORData
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime (Branch BoxSt Eff oracle skipTarget sk)

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

private def before (p : Fin 9) (args : Fin 11 → M) : List M :=
  List.ofFn (fun i : Fin p.val => args ⟨i.val,by have := p.isLt; have := i.isLt; omega⟩)

private def after (p : Fin 9) (args : Fin 11 → M) : List M :=
  List.ofFn (fun i : Fin (8-p.val+1) => (tailArgs p args) i.castSucc)

private theorem front_eq (p : Fin 9) (a : Fin 11 → M) (value : M) :
    F (fileCode p.val) (frontArgs p a value) = PA194ORMark.file (before p a) value := by
  rw [file_eq,frontLast]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [frontArgs]

private theorem marked_eq_file (p : Fin 9) (a : Fin 11 → M) :
    markedFileValue p a =
      PA194ORMark.file (before p a) (PA194ORMark.marked (a (slot p)) (rest p a)) := by
  rw [markedFileValue,front_eq,marked,marked_eq]

private theorem ordinary_eq_file (p : Fin 9) (a : Fin 11 → M) (v : M) :
    file (Function.update a (slot p) v) =
      PA194ORMark.file (before p a) (PA194ORMark.block v (rest p a)) := by
  rw [← ordinaryFileSplit,front_eq,block_eq]

private theorem rest_eq_file (p : Fin 9) (a : Fin 11 → M) :
    rest p a = PA194ORMark.file (after p a) (a 10) := by
  rw [rest,file_eq]
  congr 1
  apply congrArg a
  apply Fin.ext
  have := p.isLt
  simp
  omega

private theorem before_update (p : Fin 9) (a : Fin 11 → M) (v : M) :
    before p (Function.update a 10 v) = before p a := by
  apply congrArg List.ofFn
  funext i
  have h : (⟨i.val,by have := p.isLt; have := i.isLt; omega⟩ : Fin 11) ≠ 10 := by
    intro h
    have hi := congrArg Fin.val h
    have := p.isLt
    have := i.isLt
    simp at hi
    omega
  exact Function.update_of_ne h v a

private theorem after_update (p : Fin 9) (a : Fin 11 → M) (v : M) :
    after p (Function.update a 10 v) = after p a := by
  apply congrArg List.ofFn
  funext i
  have h : (⟨p.val+1+i.val,by have := p.isLt; have := i.isLt; omega⟩ : Fin 11) ≠ 10 := by
    intro h
    have hi := congrArg Fin.val h
    have := p.isLt
    have := i.isLt
    simp at hi
    omega
  exact Function.update_of_ne h v a

theorem zeroOracle (p : Fin 9) (a : Fin 11 → M) (l : M) (zero : a (slot p) = 0) :
    Reach table (scanFrame true (denseControl 0) l (markedFileValue p a))
      (scanFrame false (denseControl 97) (file a) l) := by
  have ordinary : file a = PA194ORMark.file (before p a) (PA194ORMark.block 0 (rest p a)) := by
    rw [← ordinaryFileSplit_self p a,front_eq,block_eq,zero]
  have restBlock : rest p a = PA194ORMark.block (tailArgs p a 0)
      (F (fileCode (8-p.val)) (fun i => tailArgs p a i.succ)) := by
    rw [rest,modelFileSucc,block_eq]
  have ov := PA194ORDecrement.zero (before p a) l (tailArgs p a 0)
    (F (fileCode (8-p.val)) (fun i => tailArgs p a i.succ))
  simpa only [show denseControl 0 = 1 by decide +kernel,
    show denseControl 97 = 11 by decide +kernel,marked_eq_file,zero,ordinary,restBlock] using ov

theorem positiveOracle (p : Fin 9) (a : Fin 11 → M) (l : M) (positive : a (slot p) ≠ 0) :
    Reach table (scanFrame true (denseControl 0) l (markedFileValue p a))
      (scanFrame false (denseControl 40) (file (decrement a p)) (push true l)) := by
  let d := F predCode (fun _ => a (slot p))
  have count : a (slot p) = d+1 := by
    have h := (modelZeroOrSuccPred (a (slot p))).resolve_left positive
    change a (slot p) = F addCode ![d,F oneCode Fin.elim0]
    rw [modelAddOne]
    exact h.symm
  have post : file (decrement a p) =
      PA194ORMark.file (before p a) (PA194ORMark.block d (rest p a)) := ordinary_eq_file p a d
  rw [show denseControl 0 = 1 by decide +kernel,
    show denseControl 40 = 7 by decide +kernel,post,marked_eq_file,count]
  exact PA194ORDecrement.positive (before p a) d l (rest p a)

theorem incrementOracle (p : Fin 9) (a : Fin 11 → M) (count l : M)
    (tail : a 10 = F repeatOutput ![count,(0 : M)]) :
    Reach table (scanFrame true (denseControl 64) l (markedFileValue p a))
      (scanFrame false (denseControl 40) (file (incremented a count p)) l) := by
  let newTail := F repeatOutput ![count+1,(0 : M)]
  let updated := Function.update a 10 newTail
  have output : file (incremented a count p) =
      PA194ORMark.file (before p a) (PA194ORMark.block (a (slot p)+1)
        (PA194ORMark.file (after p a) newTail)) := by
    change file (Function.update updated (slot p) (a (slot p)+1)) = _
    rw [ordinary_eq_file,rest_eq_file]
    exact congrArg (fun earlier => PA194ORMark.file earlier _) (before_update p a newTail) |>.trans
      (by simp [updated,after_update])
  have ov := PA194ORIncrement.increment (before p a) (after p a) (a (slot p)) l
    (F repeatOutput ![count,(0 : M)]) newTail (PA194ORSpareSweep.roundTrip count)
  simpa only [show denseControl 64 = 2 by decide +kernel,
    show denseControl 40 = 7 by decide +kernel,marked_eq_file,rest_eq_file,tail,output] using ov

private theorem boundary (box : BoxSt → M)
    (h : ∀ x, ∃ y, box x = PA194BidirectionalRow.push false y) :
    ∀ x, ∃ tail, box x = push false tail := by
  intro x
  obtain ⟨y,hy⟩ := h x
  exact ⟨y,by simpa only [PA194BidirectionalRow.push,push,Bool.false_eq_true,if_false,
    Bool.toNat_false,Nat.cast_zero,add_zero,two_mul] using hy⟩

/-- The exact OR literal rows independently implement all accepted
    compressed register operations for the controller's packed file. -/
theorem concreteBoxAgreement (a : Fin 11 → M) (count : M) (br : Branch)
    (tail : a 10 = F repeatOutput ![count,(0 : M)]) (branch : BranchOK a br) :
    BoxAgreement table denseControl br (boxValue a (incremented a count)) := by
  refine ⟨boundary _ ?_, ?_⟩
  · intro x
    cases x with
    | plain e =>
      cases e with
      | none => exact fileBoundary a
      | inc r =>
        by_cases h : r < 9 <;> simp only [boxValue,h,dite_true,dite_false] <;> exact fileBoundary _
      | dec r =>
        by_cases h : r < 9 <;> simp only [boxValue,h,dite_true,dite_false] <;> exact fileBoundary _
    | mark r =>
      by_cases h : r < 9
      · simpa only [boxValue,h,dite_true] using markedBoundary ⟨r,h⟩ a
      · simpa only [boxValue,h,dite_false] using fileBoundary a
  · intro q q' x x' extra l h
    cases x with
    | plain e =>
      cases e with
      | inc r => simp [oracle] at h
      | dec r => simp [oracle] at h
      | none =>
        cases hh : skipTarget q with
        | none => simp [oracle,hh] at h
        | some r =>
          obtain ⟨rfl,hr⟩ := M6.Runtime.skipTarget_sk hh
          simp only [oracle,hh,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl,rfl⟩ := h
          simpa only [boxValue,hr,dite_true,Bool.false_eq_true,if_false] using PA194ORRegisterFile.markOracle ⟨r,hr⟩ a l
    | mark r =>
      by_cases hr : r < 9
      · by_cases hq : q = 64
        · subst q
          simp only [oracle,hr,if_true,Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl,rfl⟩ := h
          simpa only [boxValue,hr,dite_true,Bool.false_eq_true,if_false] using
            incrementOracle ⟨r,hr⟩ a count l tail
        · by_cases hq' : q = 0
          · subst q
            cases br with
            | none => simp [oracle,hr] at h
            | some rb =>
              rcases rb with ⟨r',z⟩
              by_cases hreg : r = r'
              · subst r'
                cases z with
                | false =>
                  simp only [oracle,hr,if_true,show (0 : Nat) ≠ 64 by decide,if_false,
                    Bool.false_eq_true,Option.some.injEq,Prod.mk.injEq] at h
                  obtain ⟨rfl,rfl,rfl⟩ := h
                  have hPositive : a (slot ⟨r,hr⟩) ≠ 0 := branch hr
                  simpa only [boxValue,hr,dite_true,if_true] using positiveOracle ⟨r,hr⟩ a l hPositive
                | true =>
                  simp only [oracle,hr,show (0 : Nat) ≠ 64 by decide,
                    ↓reduceIte,Option.some.injEq,Prod.mk.injEq] at h
                  obtain ⟨rfl,rfl,rfl⟩ := h
                  have hZero : a (slot ⟨r,hr⟩) = 0 := branch hr
                  simpa only [boxValue,hr,dite_true,Bool.false_eq_true,if_false] using zeroOracle ⟨r,hr⟩ a l hZero
              · simp [oracle,hr,hreg] at h
          · simp [oracle,hr,hq,hq'] at h
      · simp [oracle,hr] at h

#print axioms zeroOracle
#print axioms positiveOracle
#print axioms incrementOracle
#print axioms concreteBoxAgreement
end models
end PA194ORBoxAgreement
