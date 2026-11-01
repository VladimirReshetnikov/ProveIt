import DiophantineConsistency.IPRABinaryRelationNative
import DiophantineConsistency.IPRARelationGGLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRABinaryRelationGG
open PRALanguage IPRANativeTheory IPRABinaryRelationNative IPRARelationGGLogic
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem binary_relExt_image (r : language.Rel 2) : nativeTheory ⊢ (Theory.Eq.relExt r)ᴺ := by
  apply mdp! (binary_relExt_adapter r)
  simpa [relCongruenceI, relationI] using relation_native r

theorem relExt_image {k : ℕ} (r : language.Rel k) : nativeTheory ⊢ (Theory.Eq.relExt r)ᴺ := by
  change Language.ORing.Rel k at r
  cases r with
  | eq => exact binary_relExt_image Language.ORing.Rel.eq
  | lt => exact binary_relExt_image Language.ORing.Rel.lt
end DiophantineConsistency.IPRABinaryRelationGG
