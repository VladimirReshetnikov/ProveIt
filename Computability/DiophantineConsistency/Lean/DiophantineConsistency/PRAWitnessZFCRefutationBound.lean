import DiophantineConsistency.PRAWitnessRefutationGraph
import DiophantineConsistency.PRAWitnessBoundCertificate
import DiophantineConsistency.PRAWitnessPositiveCoreZFC
import DiophantineConsistency.PRAWitnessZFCNegativePiCore

/-! The fixed Foundation ZFC refutation predicate has a candidate-PRA
bounded-witness proof. It does not prove that a refutation exists or fails. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessZFCRefutationBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
  PRAWitnessRefutationGraph StrictSigmaOneInduction

local instance {N : Type} [Structure language N] : Zero N := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {N : Type} [Structure language N] : One N := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {N : Type} [Structure language N] : Add N := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {N : Type} [Structure language N] : Mul N := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {N : Type} [Structure language N] : LT N := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

noncomputable def refutation : ArithmeticSentence :=
  provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)

theorem wb_refutation (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
    [N↓[language] ⊧* PRA] : WB N refutation := by
  exact wb_provabilityPred_of_core (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)
    (PRAWitnessPositiveCoreZFC.wb_coreSigma (M := N))
    (PRAWitnessZFCNegativePiCore.wb_neg_zfcCorePi (M := N))

/-- Candidate PRA proves that any actual Foundation ZFC refutation has a
single bound for the witnesses in its arithmetized predicate. -/
theorem PRA_proves_refutation_bound :
    PRA ⊢ Semiformula.lMap embedding (refutation 🡒 ∃⁰ bnd refutation) :=
  PRAWitnessBoundCertificate.certificate_of_witness_bounds refutation wb_refutation

end DiophantineConsistency.PRAWitnessZFCRefutationBound
