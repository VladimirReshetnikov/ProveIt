import GowersSzemeredi.Proofs08FourTermTheorem
import GowersSzemeredi.Proofs08Coloring

/-! The completed four-term theorem discharges the analytic input to the
previously proved finite-coloring transfer. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

/-- **Corollary 8.3.** The quantitative four-term coloring formulation. -/
theorem corollary_8_3_holds : corollary_8_3 :=
  corollary_8_3_holds_of_theorem_8_2 theorem_8_2_holds

end LeanProofs.GowersSzemeredi
