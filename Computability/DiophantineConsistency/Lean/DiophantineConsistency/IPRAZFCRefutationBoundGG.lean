import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.PRAWitnessZFCRefutationBound
import DiophantineConsistency.IPRAImpGG
/-! Actual Foundation ZFC refutation predicate has the translated bounded
witness implication in native iPRA. This is not a proof of consistency. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAZFCRefutationBoundGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory StrictSigmaOneInduction
open PRAWitnessZFCRefutationBound IPRANativeTheory

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem refutation_bound_gg : nativeTheory ⊢
    (Semiformula.lMap embedding refutation)ᴺ 🡒
      (Semiformula.lMap embedding (∃⁰ bnd refutation))ᴺ := by
  have h : PRA ⊢ (Semiformula.lMap embedding refutation) 🡒
      (Semiformula.lMap embedding (∃⁰ bnd refutation)) := by
    simpa only [LogicalConnective.HomClass.map_imply] using PRA_proves_refutation_bound
  exact IPRAImpGG.unpack_imp_image nativeTheory _ _ (IPRAFullGGTransfer.from_classical h)

/-- Proof-object form for clients requiring the translated bound as a premise. -/
def refutation_bound_gg_proof : nativeTheory ⊢!
    (Semiformula.lMap embedding refutation)ᴺ 🡒
      (Semiformula.lMap embedding (∃⁰ bnd refutation))ᴺ :=
  Classical.choice refutation_bound_gg
end DiophantineConsistency.IPRAZFCRefutationBoundGG
