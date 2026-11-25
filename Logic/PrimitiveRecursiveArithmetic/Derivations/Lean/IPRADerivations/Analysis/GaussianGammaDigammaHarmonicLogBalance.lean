import IPRADerivations.Analysis.GaussianGammaDigammaHarmonicPrefix
import IPRADerivations.Analysis.GaussianHarmonicLogarithmProduct
import IPRADerivations.Analysis.GaussianStirlingGammaFractionalIncrementLogGap

/-!
# Cofinal logarithm balance for the finite digamma slope

The harmonic interval from a/b to a/b+N, subtracted from the
original cutoff logarithm, approaches the actual harmonic name of log(a/b).
All errors use the same dyadic observation clock with N=2^p.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicLogBalance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaFiniteSum (index)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianHarmonicLogarithmName (sample sample_at clock)
open GaussianHarmonicLogarithmProduct (mesh mesh_later finite_samples)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianStirlingGammaLogarithm (source)
open RationalGaussianEmbedding (embed embed_canonical)
open RationalHarmonicInterval (interval)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem same_ratio_at (p a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (e : Γ ⊢[PRAAx] a*d ≐ b*c) :
    Γ ⊢[PRAAx] distanceBounded (sample p a b) (sample p c d) two (unit p) := by
  have hQ := le_trans (unit_positive (Γ := Γ) p) (mesh_later p)
  have raw := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hQ
    (RationalHarmonicInterval.equal_ratio_finite a b c d (mesh p) ha hb hc hd hQ e)
  exact distance_radius_mono _ _ _ _ two (unit p) hQ (unit_positive p)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) (mesh_later p))
    (distance_congr (sample_at p a b).eqSymm (sample_at p c d).eqSymm (.eqRefl _) (.eqRefl _) raw)

private theorem nearby_at (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (sample p (index a b (unit p)) (unit p*b)) qzero a (unit p) := by
  let N := unit p
  let A := index a b N
  let B := N*b
  have hN := unit_positive (Γ := Γ) p
  have hB := positive_product _ _ hN hs.andE₂
  have hBA : Γ ⊢[PRAAx] le B A := le_add_left _ _
  have hA := le_trans hB hBA
  have hGap : Γ ⊢[PRAAx] le (N*monus A B) (a*B) := by
    have e : Γ ⊢[PRAAx] monus A B ≐ a := add_monus a B
    exact le_congr (congrMul (.eqRefl _) e).eqSymm (.eqRefl _) (by
      unfold B
      ipra_le 𝔞 a*𝔞 N*sl hs.andE₂)
  have raw := GaussianGaussMultiplicationLogarithm.integer_log_distance_at B A (clock p) a N hB hBA hN hGap
  have e := (qsub_congr (GaussianGammaFiniteApproximantName.log_sample_at (clock p) A)
      (GaussianGammaFiniteApproximantName.log_sample_at (clock p) B)).eqTrans
    ((GaussianPositiveRationalLogarithmProperness.original_finite_difference A B (mesh p) hA hB).eqTrans
      (sample_at p A B).eqSymm)
  have h : Γ ⊢[PRAAx] bounded (sample p A B) a N := GaussianRationalReciprocal.bound_congr e (.eqRefl _) (.eqRefl _) raw
  have hc := GaussianRationalHorner.canonical_congr (sample_at (Γ := Γ) p A B) (embed_canonical (interval A B (mesh p)))
  exact GaussianRationalReciprocal.bound_congr (GaussianRationalReconstruction.qsub_zero_right _ hc).eqSymm (.eqRefl _) (.eqRefl _) h

theorem cutoff_balance (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (ap2 logF p (unit p)) (sample p (index a b (unit p)) a))
      (sample p a b) (a+num 10) (unit p) := by
  let N := unit p
  let A := index a b N
  let B := N*b
  let X := sample p a b
  let T := sample p A B
  let L := sample p A a
  let V := sample p N one
  let old := ap2 logF p N
  let common := sample p A b
  have hN := unit_positive (Γ := Γ) p
  have hB := positive_product _ _ hN hs.andE₂
  have hA : Γ ⊢[PRAAx] le one A := le_trans hs.andE₁ (le_add_right _ _)
  have hLeft := finite_samples p A a a b (.andI (.andI hA hs.andE₁) hs)
  have hRight := finite_samples p N one A B (.andI (.andI hN (le_refl one)) (.andI hA hB))
  have eLeft := same_ratio_at p (A*a) (a*b) A b (positive_product _ _ hA hs.andE₁)
    (positive_product _ _ hs.andE₁ hs.andE₂) hA hs.andE₂ (by ipra_ring)
  have eRight := same_ratio_at p (N*A) (one*B) A b (positive_product _ _ hN hA)
    (positive_product _ _ (le_refl one) hB) hA hs.andE₂ (by unfold B; ipra_ring)
  have left := distance_triangle_same common _ (qadd L X) two two N hN
    (distance_symmetric _ _ _ _ hN eLeft) hLeft
  have right := distance_triangle_same (qadd V T) _ common two two N hN
    (distance_symmetric _ _ _ _ hN hRight) eRight
  have together := distance_triangle_same (qadd V T) common (qadd L X) (two+two) (two+two) N hN right left
  have e := (GaussianNameArithmetic.sum_difference (Γ := Γ) V L T X).eqTrans
    (qadd_congr (.eqRefl _) (GaussianRationalDistanceOrder.reversed_difference X T).eqSymm)
  have balanced : Γ ⊢[PRAAx] distanceBounded (qsub V L) (qsub X T) (num 8) N :=
    GaussianRationalReciprocal.bound_congr e (by ipra_ring) (.eqRefl _) together
  have eV := GaussianStirlingGammaFractionalIncrementLogGap.sample_from_one N p hN
  have ht : Γ ⊢[PRAAx] le N (unit (clock p)) :=
    GaussianExponentialReference.unit_monotone (le_add_right p (num 9))
  have original := GaussianNameEquivalence.point_at logF N p (clock p) (log_regular N hN)
  have originalV : Γ ⊢[PRAAx] distanceBounded old V two N :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hN (le_trans hN ht)) hN
      (by ipra_le 𝔞 N*sl ht)
      (distance_congr (.eqRefl _) eV.eqSymm (.eqRefl _) (.eqRefl _) original)
  have logClock := difference_distance old V L L two zero N hN originalV (distance_refl_zero L N hN)
  have hX := GaussianRationalHorner.canonical_congr (sample_at (Γ := Γ) p a b) (embed_canonical (interval a b (mesh p)))
  have endGap := difference_distance X X T qzero zero a N hN (distance_refl_zero X N hN) (nearby_at p a b hs)
  have shifted := distance_triangle_same _ _ _ _ _ N hN logClock balanced
  exact distance_congr (.eqRefl _) (GaussianRationalReconstruction.qsub_zero_right _ hX)
    (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ N hN shifted endGap)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicLogBalance
