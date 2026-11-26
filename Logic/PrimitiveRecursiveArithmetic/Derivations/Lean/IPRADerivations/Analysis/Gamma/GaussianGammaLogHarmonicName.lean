import IPRADerivations.Analysis.Gamma.GaussianGammaFiniteApproximantName
import IPRADerivations.Analysis.Exponential.GaussianExponentialReference
import IPRADerivations.Core.CongruenceTactic

/-!
# The exact named harmonic identity for the two finite approximants

The original fixed Euler name and the original mesh logarithm have the
same mesh at the actual addition query. Their sum is the exact constant
harmonic name at every observation. This supplies the cancellation in
the relation between the folded finite Euler and Weierstrass exponents.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaLogHarmonicName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (logF)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianNameEquivalence (crossEquivalent diagonalEquivalent)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fixedF : PR 2 := RationalGaussianNameEmbedding.nameF GammaEulerConstantName.fixedF
def sumF : PR 2 := GaussianNameArithmetic.addF fixedF logF
def sumData (N : PTm n) : PTm n := GaussianNameArithmetic.addData N N
@[simp] theorem subst_sumData {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (sumData N) = sumData (Syn.subst σ N) := by simp [sumData]

theorem fixed_regular (N : PTm n) (h : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN fixedF N :=
  RationalGaussianNameEmbedding.name_regular _ _ (GammaEulerConstantName.fixed_name_regular N h)

theorem sum_sample_at (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] ap2 sumF p (sumData N) ≐ harmonicPoint N := by
  let t := GaussianFastValueCut.exponent two p
  let g := GammaEulerConstantName.fixedSample t N
  let l := GammaMeshRobinLogBridge.meshLogSample t N
  have hs := GammaMeshRobinLogBridge.fixed_log_samples_sum t N hN
  have ha : Γ ⊢[PRAAx] RationalGaussianEmbedding.embed (RationalArithmetic.add g l) ≐ harmonicPoint N := by
    ipra_congr (RationalGaussianEmbedding.embed (var 0) : PTm 1) with
      [hs] using [harmonicPoint, GaussianGammaCanonicalExponent.harmonic, GammaMeshRobinLogBridge.harmonicValue,
        RationalCubeMidpoint.fraction]
  have hg := RationalGaussianNameEmbedding.sample_at (Γ := Γ) GammaEulerConstantName.fixedF t N
  have hl := RationalGaussianNameEmbedding.sample_at (Γ := Γ) GammaMeshRobinLogBridge.meshLogF t N
  have main := (GaussianRationalSyntheticDivision.qadd_congr hg hl).eqTrans
    ((RationalGaussianEmbedding.embed_add g l).eqSymm.eqTrans ha)
  exact (GaussianNameArithmetic.add_at fixedF logF N N p).eqTrans
    ((GaussianNameArithmetic.recode_congr main).eqTrans
      (GaussianExponentialReference.recode_fixed _ (RationalGaussianEmbedding.embed_canonical _)))

theorem exact_sum_name (N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent sumF constantF (sumData N) (harmonicPoint N) := by
  have sum := GaussianNameArithmetic.add_fast fixedF logF N N (fixed_regular N h)
    (GaussianGammaFiniteApproximantName.log_regular N h)
  refine GaussianNameEquivalence.diagonal_to_cross _ _ _ _ sum (constant_regular _) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift, Syn.shift, subst_le, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using h.shift
  let x := harmonicPoint (Syn.shift N)
  let p : PTm (n+1) := var 0
  have d := distance_radius_mono x x LeanProofs.ConciseIPRA.PTm.zero (unit p) two (unit p)
    (unit_positive (Γ := Γ.map Fm.shift) p) (unit_positive p)
    (le_of_eq_add (d := two*unit p) (by ipra_ring))
    (GaussianRationalPowerDifference.distance_refl_zero x (unit p) (unit_positive p))
  have main := distance_congr (sum_sample_at p (Syn.shift N) hs).eqSymm (constant_at p x).eqSymm
    (.eqRefl _) (.eqRefl _) d
  simpa only [diagonalEquivalent, Syn.shift, subst_sumData, GaussianGammaCanonicalExponent.subst_harmonicPoint,
    GaussianEuclideanPointDistance.unit, unit, p, x] using main

theorem original_exact_harmonic_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent sumF constantF (sumData (var 0)) (harmonicPoint (var 0))) :=
  closeUniv 1 (.impI (exact_sum_name _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaLogHarmonicName
