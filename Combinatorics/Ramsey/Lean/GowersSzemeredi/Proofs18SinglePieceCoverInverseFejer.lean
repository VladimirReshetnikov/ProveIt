import GowersSzemeredi.Proofs16SinglePieceCoverGlobal
import GowersSzemeredi.Proofs16ClassStepFejer
import GowersSzemeredi.Proofs16SinglePieceFrequency
import GowersSzemeredi.Proofs17DenseFrequencyLocalization
import GowersSzemeredi.Proofs18ShortLocalizationInverse

/-! The slice control `singlePieceGlobalF` and the spectrum graph-count bound
`singlePieceGlobalQmaxF` of the joint-cover single-piece lift at the Fejér
density (Notes L.16d).

The Fejér inverse step itself (`single_piece_inverse_step_global_cover_fejer`)
is in `Proofs18SinglePieceCoverInverseFejerSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The slice control of the single-piece lift at the Fejér density. -/
def singlePieceGlobalF (Qb : Nat → Real → Real → Real → Real) (theta gamma : Real) (k : Nat) :
    Real → Real :=
  fun s => s / 2 / Qb k gamma (globalBudgetW (fejerThetaOne theta gamma k) k) (s / 2)

/-- The spectrum graph-count bound. -/
def singlePieceGlobalQmaxF (Qb : Nat → Real → Real → Real → Real)
    (theta gamma : Real) (k : Nat) : Real :=
  Qb k (section16Delta (fejerThetaOne theta gamma k)) (globalBudgetW (fejerThetaOne theta gamma k) k)
    (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k / 2 / 2)

end LeanProofs.GowersSzemeredi
