import DiophantineConsistency.PRAFstIdxWitnessBound
import DiophantineConsistency.PRAWitnessFold
import DiophantineConsistency.PRAWitnessIndexFamilyBound
set_option autoImplicit false
namespace DiophantineConsistency.PRAFstIdxFamilyBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAFstIdxWitnessBound PRAWitnessFold StrictSigmaOneInduction
section
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

/-- Each actual first-index witness with code p below k has all its syntactic
existential witnesses bounded by one common primitive-recursive code. -/
theorem modelFstIdxFoldBound (k p x : M)
    (hp : Structure.rel (L := language) Language.ORing.Rel.lt ![p,k])
    (hx : (Semiformula.lMap embedding fstIdxDef.val).Eval ![x,p] Empty.elim) :
    (Semiformula.lMap embedding (bnd fstIdxDef.val)).Eval
      ![x,p,Structure.func (L := language) (foldCode Code.succ) ![k]] Empty.elim := by
  exact PRAWitnessIndexFamilyBound.modelIndexFamilyBound fstIdxDef.val candidate_fstIdx_bound k p x hp hx

end
end DiophantineConsistency.PRAFstIdxFamilyBound
