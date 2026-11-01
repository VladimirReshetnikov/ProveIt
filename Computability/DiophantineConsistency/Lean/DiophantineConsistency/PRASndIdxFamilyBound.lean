import DiophantineConsistency.PRASndIdxWitnessBound
import DiophantineConsistency.PRAWitnessFold
import DiophantineConsistency.PRAWitnessIndexFamilyBound
set_option autoImplicit false
namespace DiophantineConsistency.PRASndIdxFamilyBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRASndIdxWitnessBound PRAWitnessFold StrictSigmaOneInduction
section
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

/-- Each actual second-index witness with code p below k has all its syntactic
existential witnesses bounded by one common primitive-recursive code. -/
theorem modelSndIdxFoldBound (k p x : M)
    (hp : Structure.rel (L := language) Language.ORing.Rel.lt ![p,k])
    (hx : (Semiformula.lMap embedding sndIdxDef.val).Eval ![x,p] Empty.elim) :
    (Semiformula.lMap embedding (bnd sndIdxDef.val)).Eval
      ![x,p,Structure.func (L := language) (foldCode Code.succ) ![k]] Empty.elim := by
  exact PRAWitnessIndexFamilyBound.modelIndexFamilyBound sndIdxDef.val candidate_sndIdx_bound k p x hp hx

end
end DiophantineConsistency.PRASndIdxFamilyBound
