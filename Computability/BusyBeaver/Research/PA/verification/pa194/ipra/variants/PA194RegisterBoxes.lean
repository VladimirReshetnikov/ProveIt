import PA194CompressedIncrementOracle
import ConPAMachineCompressedNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194RegisterBoxes
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAExhaustion
open PA194RegisterFile PA194MarkedFile PA194RegisterSplit PA194CompressedBoxFiles
open PA194CompressedBoxOracle PA194CompressedIncrementOracle
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

private theorem boundary (box : BoxSt → M)
    (h : ∀ x, ∃ y, box x = PA194BidirectionalRow.push false y) :
    ∀ x, ∃ tail, box x = push false tail := by
  intro x
  obtain ⟨y,hy⟩ := h x
  exact ⟨y,by simpa only [PA194BidirectionalRow.push,push,Bool.false_eq_true,if_false,
    Bool.toNat_false,Nat.cast_zero,add_zero,two_mul] using hy⟩

/-- Register-box dispatch from the checked literal mark, increment and
    decrement segments, with box-boundary arithmetic discharged. -/
theorem boxAgreement (T : Table) (label : Nat → Nat) (a : Fin 11 → M) (incremented : Fin 9 → Fin 11 → M) (br : Branch)
    (branch : BranchOK a br)
    (mark : ∀ p : Fin 9, ∀ l : M,
      Reach T
        (scanFrame true (label (sk p.val)) l (file a))
        (scanFrame false (label (M6.Runtime.markExit p.val)) (markedFileValue p a) l))
    (increment : ∀ p : Fin 9, ∀ l : M,
      Reach T
        (scanFrame true (label 64) l (markedFileValue p a))
        (scanFrame false (label 40) (file (incremented p)) l))
    (zero : ∀ p : Fin 9, ∀ l : M, a (slot p) = 0 →
      Reach T
        (scanFrame true (label 0) l (markedFileValue p a))
        (scanFrame false (label 97) (file a) l))
    (positive : ∀ p : Fin 9, ∀ l : M, a (slot p) ≠ 0 →
      Reach T
        (scanFrame true (label 0) l (markedFileValue p a))
        (scanFrame false (label 40) (file (decrement a p)) (push true l))) :
    BoxAgreement T label br (boxValue a incremented) := by
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
          simpa only [boxValue,hr,dite_true,Bool.false_eq_true,if_false] using mark ⟨r,hr⟩ l
    | mark r =>
      by_cases hr : r < 9
      · by_cases hq : q = 64
        · subst q
          simp only [oracle,hr,if_true,Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl,rfl⟩ := h
          simpa only [boxValue,hr,dite_true,Bool.false_eq_true,if_false] using increment ⟨r,hr⟩ l
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
                  simpa only [boxValue,hr,dite_true,if_true] using positive ⟨r,hr⟩ l hPositive
                | true =>
                  simp only [oracle,hr,show (0 : Nat) ≠ 64 by decide,
                    ↓reduceIte,Option.some.injEq,Prod.mk.injEq] at h
                  obtain ⟨rfl,rfl,rfl⟩ := h
                  have hZero : a (slot ⟨r,hr⟩) = 0 := branch hr
                  simpa only [boxValue,hr,dite_true,Bool.false_eq_true,if_false] using zero ⟨r,hr⟩ l hZero
              · simp [oracle,hr,hreg] at h
          · simp [oracle,hr,hq,hq'] at h
      · simp [oracle,hr] at h

#print axioms boxAgreement
end models
end PA194RegisterBoxes
