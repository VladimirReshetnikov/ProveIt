import PA194ReturnedUpdatedEven
import PA194RegisterFile
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194UpdatedHead
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194RegisterFile PA194ReturnFileMeaning PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- A finite file whose final tail is even is itself even. -/
theorem fileEvenOfLast (n : Nat) (e : Fin (n+1) → M) (t : M)
    (ht : e (Fin.last n) = t+t) : ∃ z : M, F (fileCode n) e = z+z := by
  cases n with
  | zero =>
    rw [fileCode,modelProjection]
    exact ⟨t,ht⟩
  | succ n =>
    rw [modelFileSucc,modelBlock]
    exact ⟨_,rfl⟩

/-- The updated remaining file begins with an ordinary physical block, even
when the selected block is first. Its half begins with a nonempty one-run. -/
theorem updatedHead (idx n : Nat) (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (v r : M)
    (hr : F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
      (F block ![v,F (fileCode (n+1)) rest])) = r+r) :
    ∃ head tail : M, F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
      (F block ![v,F (fileCode (n+1)) rest])) = F block ![head,tail] ∧
      r = F PA194UnaryRuns.ones ![head+1,tail] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hx : ∃ head tail : M, F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
      (F block ![v,F (fileCode (n+1)) rest])) = F block ![head,tail] := by
    cases idx with
    | zero =>
      refine ⟨v,F (fileCode (n+1)) rest,?_⟩
      rw [fileCode,modelProjection]
      rfl
    | succ idx =>
      let ep := replaceLast (idx+1) (fun i : Fin (idx+2) => e i.succ) (F block ![v,F (fileCode (n+1)) rest])
      refine ⟨ep 0,F (fileCode idx) (fun i => ep i.succ),?_⟩
      exact modelFileSucc idx ep
  obtain ⟨head,tail,hfile⟩ := hx
  refine ⟨head,tail,hfile,?_⟩
  have hb := hfile.trans (modelBlock head tail)
  have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (hr.symm.trans hb)
  rw [(modelDouble r).2,(modelDouble (F PA194UnaryRuns.ones ![head+1,tail])).2] at hh
  exact hh
/-- The first updated block has an even tail, because it is followed by at
least the selected or spare block. -/
theorem updatedHeadEvenTail (idx n : Nat) (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (v r : M)
    (hr : F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
      (F block ![v,F (fileCode (n+1)) rest])) = r+r) :
    ∃ head tail : M, F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
      (F block ![v,F (fileCode (n+1)) rest])) = F block ![head,tail+tail] ∧
      r = F PA194UnaryRuns.ones ![head+1,tail+tail] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hx : ∃ head tail : M, F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
      (F block ![v,F (fileCode (n+1)) rest])) = F block ![head,tail+tail] := by
    cases idx with
    | zero =>
      have htail : ∃ t : M, F (fileCode (n+1)) rest = t+t := by
        rw [modelFileSucc,modelBlock]
        exact ⟨_,rfl⟩
      obtain ⟨tail,htail⟩ := htail
      refine ⟨v,tail,?_⟩
      rw [fileCode,modelProjection]
      change F block ![v,F (fileCode (n+1)) rest] = _
      rw [htail]
    | succ idx =>
      let ep := replaceLast (idx+1) (fun i : Fin (idx+2) => e i.succ) (F block ![v,F (fileCode (n+1)) rest])
      let remaining : Fin (idx+1) → M := fun i => ep i.succ
      have heplast : remaining (Fin.last idx) = F block ![v,F (fileCode (n+1)) rest] := by
        simp [remaining,ep,replaceLast]
      have hblock := modelBlock v (F (fileCode (n+1)) rest)
      obtain ⟨tail,htail⟩ := fileEvenOfLast idx remaining _ (heplast.trans hblock)
      refine ⟨ep 0,tail,?_⟩
      rw [modelFileSucc]
      rw [htail]
  obtain ⟨head,tail,hfile⟩ := hx
  refine ⟨head,tail,hfile,?_⟩
  have hb := hfile.trans (modelBlock head (tail+tail))
  have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (hr.symm.trans hb)
  rw [(modelDouble r).2,(modelDouble (F PA194UnaryRuns.ones ![head+1,tail+tail])).2] at hh
  exact hh
#print axioms updatedHeadEvenTail
#print axioms fileEvenOfLast
#print axioms updatedHead
end models
end PA194UpdatedHead
