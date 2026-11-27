import IPRADerivations.Analysis.Gamma.Digamma.ElementaryBounds.GaussianGammaDigammaHarmonicCells
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationLogarithm
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmProduct

/-!
# Exact cutoff logarithm gaps at a common denominator

The original harmonic observations for log(a/b) and log(c/b) differ
by the actual interval from c to a on the common factorial mesh.
The rectangle bound therefore applies directly without observation slack.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftLogGap

open_ipra
open GaussianGammaDigammaHarmonicCells (cell chain)
open GaussianGammaFiniteApproximantName (logF log_sample_at)
open GaussianHarmonicLogarithmName (sample sample_at clock)
open GaussianHarmonicLogarithmProduct (mesh)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qsub_congr qadd_sub_cancel)
open RationalGaussianEmbedding (embed embed_canonical)
open RationalHarmonicInterval (at_common common interval horizon)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sample_difference (p a c b : PTm n) :
    Γ ⊢[PRAAx] qsub (sample p a b) (sample p c b) ≐ embed (interval a c (mesh p)) := by
  let Q := mesh p
  let L := Q*(a+c+b)
  let X := cell a b Q L
  let Y := cell c b Q L
  let Z := cell a c Q L
  have h₁ : Γ ⊢[PRAAx] le (horizon a b Q) L := le_of_eq_add (d := Q*c) (by unfold horizon L; ipra_ring)
  have h₂ : Γ ⊢[PRAAx] le (horizon c b Q) L := le_of_eq_add (d := Q*a) (by unfold horizon L; ipra_ring)
  have h₃ : Γ ⊢[PRAAx] le (horizon a c Q) L := le_of_eq_add (d := Q*b) (by unfold horizon L; ipra_ring)
  have first : Γ ⊢[PRAAx] sample p a b ≐ X := (sample_at p a b).eqTrans (RationalGaussianRealPart.embed_congr (at_common a b Q L h₁)).eqSymm
  have second : Γ ⊢[PRAAx] sample p c b ≐ Y := (sample_at p c b).eqTrans (RationalGaussianRealPart.embed_congr (at_common c b Q L h₂)).eqSymm
  have last : Γ ⊢[PRAAx] Z ≐ embed (interval a c Q) := RationalGaussianRealPart.embed_congr (at_common a c Q L h₃)
  have merge : Γ ⊢[PRAAx] qadd Y Z ≐ X := chain b c a Q L
  exact (qsub_congr (first.eqTrans merge.eqSymm) second).eqTrans
    ((qadd_sub_cancel Y Z (embed_canonical (common a c Q L))).eqTrans last)

theorem gap (p a c b K D : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hca : Γ ⊢[PRAAx] le c a) (hD : Γ ⊢[PRAAx] le one D)
    (hgap : Γ ⊢[PRAAx] le (D*monus a c) (K*c)) :
    Γ ⊢[PRAAx] distanceBounded (sample p a b) (sample p c b) K D := by
  have ha := le_trans hc hca
  have raw := GaussianGaussMultiplicationLogarithm.integer_log_distance_at c a (clock p) K D hc hca hD hgap
  have cut := (qsub_congr (log_sample_at (clock p) a) (log_sample_at (clock p) c)).eqTrans
    (GaussianPositiveRationalLogarithmProperness.original_finite_difference a c (mesh p) ha hc)
  exact GaussianRationalReciprocal.bound_congr (cut.eqTrans (sample_difference p a c b).eqSymm) (.eqRefl _) (.eqRefl _) raw

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftLogGap
