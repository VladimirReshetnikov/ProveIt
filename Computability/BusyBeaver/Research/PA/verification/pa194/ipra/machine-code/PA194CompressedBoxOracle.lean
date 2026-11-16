import PA194CompressedBoxFiles

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedBoxOracle
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA194BidirectionalRunScan PA194CompressedTape PA194FoldedRuntimeRows
open PA194CompressedBoxFiles PA194CompressedExecutor
open M6.Runtime

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local notation "F" => Structure.func (L := language)

noncomputable def decrement (a : Fin 11 → M) (p : Fin 9) : Fin 11 → M :=
  Function.update a (slot p) (F predCode (fun _ => a (slot p)))

/-- Interpret the symbolic register effect in a PRA model. The increment
argument supplies the file after appending its additional spare. -/
noncomputable def boxValue (a : Fin 11 → M) (incremented : Fin 9 → Fin 11 → M) : BoxSt → M
  | .plain .none => file a
  | .plain (.inc r) => if hr : r < 9 then file (incremented ⟨r,hr⟩) else file a
  | .plain (.dec r) => if hr : r < 9 then file (decrement a ⟨r,hr⟩) else file a
  | .mark r => if hr : r < 9 then markedFileValue ⟨r,hr⟩ a else file a

def BranchOK (a : Fin 11 → M) : Branch → Prop
  | none => True
  | some (r,z) => ∀ hr : r < 9, if z then a (slot ⟨r,hr⟩) = 0 else a (slot ⟨r,hr⟩) ≠ 0

def IncrementOracle (a : Fin 11 → M) (incremented : Fin 9 → Fin 11 → M) : Prop :=
  ∀ p : Fin 9, ∀ l : M,
    Reach (frame true (denseControl 64) l (markedFileValue p a))
      (frame false (denseControl 40) (file (incremented p)) l)

/-- Every register-box call of the compressed executor has a matching literal
segment, given the increment segment for the file's remaining spares. -/
theorem boxAgreement (a : Fin 11 → M) (incremented : Fin 9 → Fin 11 → M)
    (hi : IncrementOracle a incremented) (br : Branch) (hb : BranchOK a br) :
    BoxAgreement denseControl br (boxValue a incremented) := by
  refine ⟨?_,?_⟩
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
          obtain ⟨rfl,hr⟩ := skipTarget_sk hh
          simp only [oracle,hh,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl,rfl⟩ := h
          simpa only [boxValue,hr,dite_true,Bool.false_eq_true,↓reduceIte] using markOracle ⟨r,hr⟩ a l
    | mark r =>
      by_cases hr : r < 9
      · by_cases hq : q = 64
        · subst q
          simp only [oracle,hr,if_true,Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl,rfl⟩ := h
          simpa only [boxValue,hr,dite_true,Bool.false_eq_true,↓reduceIte] using hi ⟨r,hr⟩ l
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
                  have hz : a (slot ⟨r,hr⟩) ≠ 0 := hb hr
                  simpa only [boxValue,hr,dite_true,↓reduceIte,decrement] using
                    decPositiveOracle ⟨r,hr⟩ a l hz
                | true =>
                  simp only [oracle,hr,show (0 : Nat) ≠ 64 by decide,
                    ↓reduceIte,Option.some.injEq,Prod.mk.injEq] at h
                  obtain ⟨rfl,rfl,rfl⟩ := h
                  have hz : a (slot ⟨r,hr⟩) = 0 := hb hr
                  simpa only [boxValue,hr,dite_true,Bool.false_eq_true,↓reduceIte] using
                    decZeroOracle ⟨r,hr⟩ a l hz
              · simp [oracle,hr,hreg] at h
          · simp [oracle,hr,hq,hq'] at h
      · simp [oracle,hr] at h

#print axioms boxAgreement
end models
end PA194CompressedBoxOracle
