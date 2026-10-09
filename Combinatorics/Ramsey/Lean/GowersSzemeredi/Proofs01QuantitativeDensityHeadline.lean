import GowersSzemeredi.Proofs01QuantitativeDensityBridge
import OAI.Combinatorics.Progressions.Results.Conclusions

/-! The pinned quantitative density theorem supplies the exact Gowers
headline through the audited finite-set bridge. Its existential constants
do not supply Theorem 18.2's fixed numerical threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem theorem_1_3_holds : theorem_1_3 :=
  theorem_1_3_of_quantitative_density OAI.Erdos3.manuscriptQuantitativeDensityTheorem

end LeanProofs.GowersSzemeredi
