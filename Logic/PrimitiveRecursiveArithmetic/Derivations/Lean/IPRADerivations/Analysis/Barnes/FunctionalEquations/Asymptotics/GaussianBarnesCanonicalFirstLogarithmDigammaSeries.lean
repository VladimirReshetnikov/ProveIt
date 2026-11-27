import IPRADerivations.Analysis.Barnes.FunctionalEquations.Asymptotics.GaussianBarnesCanonicalFirstLogarithmDigammaPrefix
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# The original Barnes logarithmic derivative series on the positive axis

At the positive rational argument `A/B` the series part of the original
Barnes logarithmic derivative is `((A-B)/B) * (γ + ψ(A/B))`. The named
comparison uses a common finite prefix from the actual Barnes and
digamma evaluators, chosen at a primitive-recursive observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmDigammaSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFirstLogarithmDigammaPrefix (coordinate original_prefix)
open GaussianBarnesCanonicalPositiveFirstLogarithm (seriesF seriesData series_regular prefixValue series_prefix_error)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (gammaF gamma_regular constantF constant_at constant_regular)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaDigammaSeriesTerms (partialSum literalData literal_rate)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_negative add_zero_left multiply_sample_error)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian_represents qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded bounded_of_cleared)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qmul_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "D" => GaussianGammaDigammaNative.nameF
local notation "S" => GaussianGammaDigammaSeries.nameF
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

def unscaledF : PR 2 := addF gammaF D

def unscaledData (A B : PTm n) : PTm n := addData zero (GaussianGammaDigammaNative.data A B)

def scaledF : PR 2 := multiplyF constantF unscaledF

def scaledData (A B : PTm n) : PTm n :=
  multiplyData constantF unscaledF (coordinate A B) (unscaledData A B)

@[simp] theorem subst_unscaledData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (unscaledData A B) = unscaledData (Syn.subst σ A) (Syn.subst σ B) := by simp [unscaledData]

@[simp] theorem subst_scaledData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (scaledData A B) = scaledData (Syn.subst σ A) (Syn.subst σ B) := by simp [scaledData]

theorem unscaled_regular (A B : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B) :
    Γ ⊢[PRAAx] pointCN unscaledF (unscaledData A B) :=
  add_fast _ _ _ _ gamma_regular (GaussianGammaDigammaNative.name_regular A B hs)

theorem scaled_regular (A B : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B) :
    Γ ⊢[PRAAx] pointCN scaledF (scaledData A B) :=
  multiply_fast _ _ _ _ (constant_regular _) (unscaled_regular A B hs)

private theorem augmented_literal (A B M : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (addF gammaF S) constantF (addData zero (literalData A B M)) (partialSum A B M) := by
  let a := partialSum A B M
  let Z := GaussianNameRingLaws.zeroF
  let N := addF gammaF negativeGammaF
  let b : PTm n := addData zero negativeGammaData
  let c : PTm n := addData zero (literalData A B M)
  have hr := constant_regular (Γ := Γ) a
  have hb : Γ ⊢[PRAAx] pointCN N b :=
    add_fast _ _ _ _ gamma_regular negativeGamma_regular
  have assoc : Γ ⊢[PRAAx]
      crossEquivalent (addF N constantF) (addF gammaF S) (addData b a) c :=
    add_associative gammaF negativeGammaF constantF zero negativeGammaData a
      gamma_regular negativeGamma_regular hr
  have zeroAtA : Γ ⊢[PRAAx] crossEquivalent N Z b a :=
    cross_trans N Z Z b zero a (add_negative gammaF zero gamma_regular)
      (GaussianNameRingLaws.zero_name_cross zero a)
  have cancel : Γ ⊢[PRAAx]
      crossEquivalent (addF N constantF) (addF Z constantF) (addData b a) (addData a a) :=
    add_cross N Z constantF constantF b a a a hb
      (GaussianNameRingLaws.zero_fast a) hr hr zeroAtA (cross_refl _ _ hr)
  have collapse : Γ ⊢[PRAAx] crossEquivalent (addF N constantF) constantF (addData b a) a :=
    cross_trans (addF N constantF) (addF Z constantF) constantF (addData b a) (addData a a) a
      cancel (add_zero_left constantF a hr)
  exact cross_trans (addF gammaF S) (addF N constantF) constantF c (addData b a) a
    (cross_symm (addF N constantF) (addF gammaF S) (addData b a) c assoc) collapse

theorem unscaled_prefix_rate (A B M : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] independentRate unscaledF constantF (unscaledData A B) (partialSum A B M)
      (leadingNumerator zero one A M) (leadingDenominator one M) := by
  let L := addF gammaF S
  let c := addData zero (literalData A B M)
  let P := leadingNumerator zero one A M
  let Q := leadingDenominator one M
  have hQ : Γ ⊢[PRAAx] le one Q := positive_product one M (le_refl one) hM
  have raw : Γ ⊢[PRAAx] independentRate unscaledF L (unscaledData A B) c P Q :=
    GaussianNamedAddRate.independent_rate gammaF D gammaF S zero (GaussianGammaDigammaNative.data A B) zero
      (literalData A B M) zero one A M (le_refl one) hM
      (GaussianNamedAddRate.self_rate gammaF zero gamma_regular) (literal_rate A B M hs hM)
  have actual : Γ ⊢[PRAAx] crossEquivalent unscaledF unscaledF (unscaledData A B) (unscaledData A B) :=
    cross_refl _ _ (unscaled_regular A B hs)
  have finite : Γ ⊢[PRAAx] crossEquivalent L constantF c (partialSum A B M) :=
    augmented_literal A B M
  exact GaussianNamedRateTransport.transport unscaledF L unscaledF constantF (unscaledData A B) c
    (unscaledData A B) (partialSum A B M) P Q hQ raw actual (cross_symm _ _ _ _ finite)

private theorem coordinate_bound (A B R : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] bounded (coordinate A B) R one :=
  bounded_of_cleared _ _ _ _ _ h.andE₁ (le_refl one) (ofGaussian_represents _ _ h.andE₁)
    (le_congr (by ipra_ring) (by ipra_ring) h.andE₂)

private theorem diagonal_at (p A B R : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B)
    (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 seriesF p (seriesData A B R)) (ap2 scaledF p (scaledData A B))
      (num 4+R*num 3+(multiplyModulus constantF unscaledF (coordinate A B) (unscaledData A B)+one)) (unit p) := by
  let L := GaussianBarnesCanonicalDerivativeCofinal.length p R
  let r := L+A*unit p+one
  let M := initial R+r
  let c := coordinate A B
  let P := leadingNumerator zero one A M
  let Q := leadingDenominator one M
  let u := ap2 unscaledF p (unscaledData A B)
  let v := partialSum A B M
  have hp := unit_positive (Γ := Γ) p
  have hM : Γ ⊢[PRAAx] le one M := by
    apply le_of_eq_add (d := initial R+L+A*unit p)
    unfold M r
    ipra_ring
  have hN : Γ ⊢[PRAAx] le (A*unit p) M := by
    apply le_of_eq_add (d := initial R+L+one)
    unfold M r
    ipra_ring
  have hr : Γ ⊢[PRAAx] le L r := by
    apply le_of_eq_add (d := A*unit p+one)
    unfold r
    ipra_ring
  have close := distance_congr (.eqRefl _) (constant_at p v) (.eqRefl _) (.eqRefl _)
    (rate_at unscaledF constantF (unscaledData A B) v P Q p p (unscaled_prefix_rate A B M hs hM))
  have scalar : Γ ⊢[PRAAx] distanceBounded u v (num 3) (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive Q p p (positive_product one M (le_refl one) hM)) hp
      (by unfold rateNumerator rateDenominator P Q leadingNumerator leadingDenominator; ipra_le 𝔞 (unit p)^2*sl hN) close
  have product : Γ ⊢[PRAAx] distanceBounded (qmul c u) (qmul c v) (R*num 3) (unit p) :=
    bound_congr (multiplication_difference c u v).eqSymm (.eqRefl _) (one_mul _)
      (bounded_product c _ R one (num 3) (unit p) (le_refl _) hp (coordinate_bound A B R h) scalar)
  have rows := distance_congr (.eqRefl _) (original_prefix A B M hs.andE₁ hs.andE₂) (.eqRefl _) (.eqRefl _)
    (series_prefix_error p A B R r h hr)
  have productObs := distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (multiply_sample_error constantF unscaledF c (unscaledData A B) p
      (constant_regular c) (unscaled_regular A B hs))
  exact distance_triangle_same _ _ _ _ _ _ hp
    (distance_triangle_same _ _ _ _ _ _ hp rows (distance_symmetric _ _ _ _ hp product))
    (distance_symmetric _ _ _ _ hp productObs)

theorem series_cross (A B R : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B)
    (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] crossEquivalent seriesF scaledF (seriesData A B R) (scaledData A B) := by
  let K := num 4+R*num 3+(multiplyModulus constantF unscaledF (coordinate A B) (unscaledData A B)+one)
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ K
    (series_regular A B R h) (scaled_regular A B hs)
  refine .allI ?_
  have hs' : (Γ.map Fm.shift) ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hs.shift
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] disk (center (Syn.shift A) (Syn.shift B)) (Syn.shift R) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianNamedDiagonalRate.diagonalRate,Syn.shift,K,one] using
    diagonal_at (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift R) hs' h'

theorem actual_Barnes_first_logarithm_digamma_series_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let A := var 0; let B := var 1; let R := var 2
     (GaussianStirlingGammaLogarithm.source A B ⋏ disk (center A B) R B) ⟶
       crossEquivalent seriesF scaledF (seriesData A B R) (scaledData A B)) :=
  closeUniv 3 (.impI (series_cross _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmDigammaSeries
