import PA194SetSearchRoot
/-! Preimage search on the exact Foundation universal-rule premise.
This lemma is a single compiler component, not a complete translation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace PA194AllPreimage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PA194SetSearchRoot
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

/-- Exact preimage selection for an all-introduction premise: a member other
than its distinguished free formula comes from the shifted conclusion set. -/
theorem all_premise_preimage (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    (s p dp q : M)
    (hdp : DerivationOf T dp (insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s)))
    (hq : q ∈ insert (free M6.PA.RelationalSource.language p)
      (setShift M6.PA.RelationalSource.language s))
    (hne : q ≠ free M6.PA.RelationalSource.language p) :
    let found := F preimageCode ![s,q]
    found ∈ s ∧ shift M6.PA.RelationalSource.language found = q := by
  have hs : IsFormulaSet M6.PA.RelationalSource.language s := by
    have hp := hdp.isFormulaSet
    exact IsFormulaSet.setShift_iff.mp (IsFormulaSet.insert_iff.mp hp).2
  have hq' : q ∈ setShift M6.PA.RelationalSource.language s := by
    rcases mem_bitInsert_iff.mp hq with he | hm
    · exact False.elim (hne he)
    · exact hm
  exact preimage_correct s q hs hq'

#print axioms all_premise_preimage
end models
end PA194AllPreimage
