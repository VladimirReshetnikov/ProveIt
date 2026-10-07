import GowersSzemeredi.Proofs13CoefficientPartition

/-! Restore the geometric context stated immediately before Lemma 13.9.
The conclusion, including its quantitative bounds, is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_13_9_without_construction_geometry_holds :
    lemma_13_9_without_construction_geometry := by
  intro N _ S D E F G H h135 h136 h137 h138 hlength
  exact lemma_13_9_of_progression_length_bound S D E F G H
    h135 h136 h137 h138 hlength

end LeanProofs.GowersSzemeredi
