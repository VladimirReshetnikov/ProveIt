import PA194AllPreimage
/-! Total branch selection for the internal Foundation universal rule.
This is a selector component, not a complete proof compiler. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace PA194AllChoice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAEqualityCode PRASelectCode PRAHistoryPairCode
 PA194TermRecursion PA194PathIterator PA194CloseVariable PA194SetSearchRoot PA194AllPreimage

/-- Zero selects the distinguished formula; a successor encodes a preimage. -/
noncomputable def choiceCode : Code 3 :=
  selectAmong (bin equalityCode (.proj 1) (.proj 2)) (.zero 3)
    (unary .succ (bin preimageCode (.proj 0) (.proj 2)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem choice_model (s special q : M) : F choiceCode ![s,special,q] =
    if special = q then 0 else F preimageCode ![s,q]+1 := by
  rw [choiceCode, modelChooseEqual, modelProjection, modelProjection]
  change (if special = q then F (.zero 3) ![s,special,q]
    else F (unary .succ (bin preimageCode (.proj 0) (.proj 2))) ![s,special,q]) = _
  rw [PRAMultiplication.modelZero, modelUnary, modelBin, modelProjection, modelProjection]
  change (if special = q then (0 : M) else F Code.succ (fun _ => F preimageCode ![s,q])) = _
  rw [← modelAddOne]
  rfl

theorem all_premise_choice (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    (s p dp q : M)
    (hdp : DerivationOf T dp (insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s)))
    (hq : q ∈ insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s)) :
    let value := F choiceCode ![s,free M6.PA.RelationalSource.language p,q]
    (q = free M6.PA.RelationalSource.language p ∧ value = 0) ∨
      ∃ u, value = u+1 ∧ u ∈ s ∧ shift M6.PA.RelationalSource.language u = q := by
  by_cases h : q = free M6.PA.RelationalSource.language p
  · left
    refine ⟨h, ?_⟩
    rw [choice_model, if_pos h.symm]
  · right
    let u := F preimageCode ![s,q]
    have hu := all_premise_preimage T s p dp q hdp hq h
    refine ⟨u, ?_, hu⟩
    rw [choice_model, if_neg (Ne.symm h)]

#print axioms all_premise_choice
end models
end PA194AllChoice
