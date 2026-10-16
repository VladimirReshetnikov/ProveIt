import GowersSzemeredi.Proofs16Lemma5
import GowersSzemeredi.Proofs16TightRadius

/-! The parameterized selection proofs are shared in `Proofs16Lemma5`.
This module adds the tight-radius specialization. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The tight radius `tightZeta (t1/4)` satisfies the radius hypothesis for
every density `t1`. -/
theorem tightZeta_condition {t1 : Real} (ha0 : 0 < t1 / 4) :
    ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → tightZeta (t1 / 4) ≤ section10Zeta alpha :=
  fun _ ha ha1 => tightZeta_le_section10Zeta ha0 ha ha1

end LeanProofs.GowersSzemeredi
