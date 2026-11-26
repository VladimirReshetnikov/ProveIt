import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumChord
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScaleOrder

/-!
# Difference readback of the strong Gamma chord

The weighted inequality is evaluated at the actual independent-clock
log-Gamma name. At a common output query its normalization errors are
bounded explicitly. Subtracting the full base weight gives the scaled
center difference plus the squared-separation margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordReadback

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaMinimumChord (centerData center_source margin strong_chord)
open GaussianNamedNaturalScaleOrder (cost weighted_chord_difference_at)
open GaussianRationalHorner (canonical qadd)
open GaussianRationalMetric (qsub)
open GaussianRationalNaturalScale (natScale)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => logGammaF
local notation "lg" => logGammaData

def budget (a c b W : PTm n) : PTm n :=
  cost G W (centerData a c b W)+cost G (pred W) (lg a b)+num 8

ipra_subst budget

theorem log_sample_canonical (p a b : PTm n) : Γ ⊢[PRAAx] canonical (ap2 G p (lg a b)) := by
  unfold logGammaF logGammaData
  apply GaussianRationalHorner.canonical_congr (GaussianNamedPositiveLogarithm.sample_at _ _ _ _)
  exact GaussianPositiveRationalLogarithm.sample_canonical _ _ _

/-- The actual finite observation of the chord compares the signed
difference to the base at the same query. Its cost is fixed before
choosing that query. -/
theorem difference_at (p a c b M W : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b)) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] upper
      (fstT (qadd (margin a c b M) (natScale W (qsub (ap2 G p (centerData a c b W)) (ap2 G p (lg a b))))))
      (fstT (qsub (ap2 G p (lg c b)) (ap2 G p (lg a b)))) (budget a c b W) (unit p) := by
  exact weighted_chord_difference_at G p (margin a c b M) W (lg a b) (lg c b) (centerData a c b W)
    (le_trans RationalAlgebra.two_positive hW) (log_gamma_regular a b (.andI ha hb))
    (log_gamma_regular c b (.andI hc hb)) (log_gamma_regular _ _ (center_source a c b W hc hb hW))
    (log_sample_canonical p a b) (log_sample_canonical p c b) (strong_chord a c b M W ha hc hb haM hcM hW)

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordReadback
