import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationLogarithm
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmProduct
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# The relative logarithm for the Gauss multiplication powers

The synchronized harmonic name for (log(mN/L)) is within (1/N)
at every observation. The actual rational logarithm for (N/L) is
the sum of this name and the actual rational logarithm for (1/m).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationRelativeLog

open_ipra
open GaussianGaussMultiplicationLogarithm (top top_positive log_distance_at)
open GaussianGammaFiniteApproximantName (log_sample_at)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianPositiveRationalLogarithm (logF data source)
open GaussianRationalMetric (bounded qsub)
open RationalGaussianEmbedding (embed)
open RationalHarmonicInterval (interval)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev relativeLogF : PR 2 := GaussianHarmonicLogarithmName.nameF
def relativeLogData (m N : PTm n) : PTm n := GaussianHarmonicLogarithmName.data (m*N) (top m N)

ipra_subst relativeLogData

theorem relative_log_bound_at (m N p : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (ap2 relativeLogF p (relativeLogData m N)) one N := by
  let t := GaussianHarmonicLogarithmName.clock p
  let L := top m N
  let Q := GammaEulerConstantName.mesh t
  let f := GaussianGammaFiniteApproximantName.logF
  have hl := top_positive m N hm hN
  have hs := RationalAlgebra.positive_product hm hN
  have eq : Γ ⊢[PRAAx] qsub (ap2 f t (m*N)) (ap2 f t L) ≐ embed (interval (m*N) L Q) :=
    (GaussianRationalSyntheticDivision.qsub_congr (log_sample_at t (m*N)) (log_sample_at t L)).eqTrans
      (GaussianPositiveRationalLogarithmProperness.original_finite_difference (m*N) L Q hs hl)
  exact GaussianRationalReciprocal.bound_congr
    (eq.eqTrans (GaussianHarmonicLogarithmName.sample_at p (m*N) L).eqSymm)
    (.eqRefl _) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hN (log_distance_at m N t hm hN))

theorem relative_log_regular (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN relativeLogF (relativeLogData m N) :=
  GaussianHarmonicLogarithmName.name_regular _ _
    (.andI (RationalAlgebra.positive_product hm hN) (top_positive m N hm hN))

theorem relative_log_addition (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent logF (addF logF relativeLogF) (data N (top m N))
      (addData (data one m) (relativeLogData m N)) := by
  let L := top m N
  let a := one*(m*N)
  let b := m*L
  let f := relativeLogF
  let xs := GaussianHarmonicLogarithmName.data one m
  let ys := relativeLogData m N
  have limits : Γ ⊢[PRAAx] source one m := .andI (le_refl one) hm
  have row : Γ ⊢[PRAAx] source N L := .andI hN (top_positive m N hm hN)
  have split : Γ ⊢[PRAAx] GaussianHarmonicLogarithmProduct.source one m (m*N) L :=
    .andI limits (.andI (RationalAlgebra.positive_product hm hN) row.andE₂)
  have prod : Γ ⊢[PRAAx] source a b := GaussianHarmonicLogarithmProduct.product_source one m (m*N) L split
  have same := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper N L a b row prod
    (by dsimp [a,b]; ipra_ring)
  have sampler := GaussianHarmonicLogarithmName.cross_original a b prod
  have logarithms := GaussianHarmonicLogarithmProduct.logarithm_product one m (m*N) L split
  have regular := relative_log_regular m N hm hN
  have replace := GaussianNamedGammaHalfShift.add_cross f logF f f xs (data one m) ys ys
    (GaussianHarmonicLogarithmName.name_regular one m limits) (GaussianPositiveRationalLogarithm.name_regular one m limits)
    regular regular (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original one m limits))
    (cross_refl f ys regular)
  exact cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ same sampler) logarithms) replace

theorem actual_gauss_multiplication_relative_log_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 1) ⋏ le one (var 2)) ⟶
      bounded (ap2 relativeLogF (var 0) (relativeLogData (var 1) (var 2))) one (var 2)) :=
  closeUniv 3 (.impI (relative_log_bound_at _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_gauss_multiplication_relative_log_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 1) ⋏ le one (var 0)) ⟶
      crossEquivalent logF (addF logF relativeLogF) (data (var 0) (top (var 1) (var 0)))
        (addData (data one (var 1)) (relativeLogData (var 1) (var 0)))) :=
  closeUniv 2 (.impI (relative_log_addition _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationRelativeLog
