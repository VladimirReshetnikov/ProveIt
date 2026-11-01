import DiophantineConsistency.IPRANativeAtomStability
import DiophantineConsistency.IPRANativeFormula
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeAtomCoverage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeFormula
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def atomStable (h : nativeTheory ⊢! eqDecSentence) {k : ℕ}
    (r : language.Rel k) (v : Fin k → Term language ℕ) :
    extended nativeTheory ⊢! ∼∼native (Semiformula.rel r v) 🡒 native (Semiformula.rel r v) := by
  cases r with
  | eq =>
    change extended nativeTheory ⊢! ∼∼(Semiformulaᵢ.rel Language.ORing.Rel.eq v) 🡒 Semiformulaᵢ.rel Language.ORing.Rel.eq v
    have hh := eqStableOpen h (v 0) (v 1)
    rw [Matrix.fun_eq_vec_two v]
    exact hh
  | lt =>
    change extended nativeTheory ⊢! ∼∼(Semiformulaᵢ.rel Language.ORing.Rel.lt v) 🡒 Semiformulaᵢ.rel Language.ORing.Rel.lt v
    have hh := orderStableOpen h (v 0) (v 1)
    rw [Matrix.fun_eq_vec_two v]
    exact hh
end DiophantineConsistency.IPRANativeAtomCoverage
