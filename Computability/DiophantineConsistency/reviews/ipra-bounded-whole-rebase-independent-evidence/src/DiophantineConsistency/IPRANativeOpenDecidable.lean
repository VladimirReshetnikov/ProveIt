import DiophantineConsistency.IPRANativeEqualityDecidable
import DiophantineConsistency.IPRANativeOpenDecision
/-! Open NNF formulas and order atoms are decidable in the native theory,
using the completed universal equality-decidability construction. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeOpenDecidable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeOpenDecision
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeEqualityDecidable
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def openDecidable (φ : Proposition language) (h : φ.Open) :
    extended nativeTheory ⊢! native φ ⋎ ∼native φ := openDecision equalityDecidable φ h

def openStable (φ : Proposition language) (h : φ.Open) :
    extended nativeTheory ⊢! ∼∼native φ 🡒 native φ := openStability equalityDecidable φ h

def orderDecidable (a b : Term language ℕ) :
    extended nativeTheory ⊢! ltAt a b ⋎ ∼ltAt a b := orderDecOpen equalityDecidable a b
end DiophantineConsistency.IPRANativeOpenDecidable
