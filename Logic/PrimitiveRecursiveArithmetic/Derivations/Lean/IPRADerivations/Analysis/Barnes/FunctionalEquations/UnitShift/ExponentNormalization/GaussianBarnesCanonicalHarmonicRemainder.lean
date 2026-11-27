import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaEulerDerivative

/-!
# The harmonic remainder in the original Barnes shift

Use the original finite harmonic rational, the original Euler–Mascheroni
name, and the same integer logarithm as the Gamma Euler approximant.
The actual normalized remainder observations have error `1/K+17·2⁻ᵖ`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHarmonicRemainder

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev harmonicMinusGammaF : PR 2 := addF negativeGammaF constantF
def harmonicMinusGammaData (K : PTm n) : PTm n := addData negativeGammaData (harmonicPoint K)
abbrev nameF : PR 2 := GaussianNamedDifference.nameF harmonicMinusGammaF logF
def data (K : PTm n) : PTm n := GaussianNamedDifference.data (harmonicMinusGammaData K) K

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (K : PTm n) : Syn.subst σ (data K) = data (Syn.subst σ K) := by
  simp [data,harmonicMinusGammaData,GaussianGammaDerivativeAtOne.negativeGammaData]

theorem harmonic_minus_gamma_regular (K : PTm n) : Γ ⊢[PRAAx] pointCN harmonicMinusGammaF (harmonicMinusGammaData K) :=
  add_fast _ _ _ _ negativeGamma_regular (constant_regular _)

theorem regular (K : PTm n) (h : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx] pointCN nameF (data K) :=
  GaussianNamedDifference.name_regular _ _ _ _ (harmonic_minus_gamma_regular K) (log_regular K h)

theorem sample_error (p K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data K)) qzero (unit p+num 17*K) (K*unit p) := by
  let U := unit p
  let E := K*U
  let g := ap2 negativeGammaF p (negativeGammaData : PTm n)
  let l := ap2 logF p K
  let a := harmonicPoint K
  let b := ap2 harmonicMinusGammaF p (harmonicMinusGammaData K)
  let c := qadd g a
  let x := ap2 nameF p (data K)
  have hp := unit_positive (Γ := Γ) p
  have he := positive_product K U hK hp
  have lift (q r A : PTm n) (h : Γ ⊢[PRAAx] distanceBounded q r A U) : Γ ⊢[PRAAx] distanceBounded q r (A*K) E :=
    distance_radius_mono q r A U _ _ hp he (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) h
  have near := GaussianGammaDigammaEulerDerivative.log_sample_error p K hK
  have add := GaussianNameRingLaws.add_sample_error (Γ := Γ) negativeGammaF constantF negativeGammaData a p
    negativeGamma_regular (constant_regular a)
  have raw := lift b c (num 3) (distance_congr (.eqRefl b) (qadd_congr (.eqRefl g) (constant_at p a))
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) add)
  have first := distance_triangle_same b c l _ _ E he raw (distance_symmetric _ _ _ _ he near)
  have last := GaussianNamedDifference.sample_error harmonicMinusGammaF logF (harmonicMinusGammaData K) K p
    (harmonic_minus_gamma_regular K) (log_regular K hK)
  have zero_close := GaussianNamedDifference.difference_distance b l l l (num 3*K+(U+num 8*K)) zero E he first
    (GaussianRationalPowerDifference.distance_refl_zero l E he)
  have endpoint := distance_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self l) (.eqRefl _) (.eqRefl _) zero_close
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same x (qsub b l) qzero _ _ E he (lift x (qsub b l) (num 6) last) endpoint)

theorem actual_Barnes_harmonic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ distanceBounded (ap2 nameF (var 0) (data (var 1))) qzero
      (unit (var 0)+num 17*var 1) (var 1*unit (var 0))) :=
  closeUniv 2 (.impI (sample_error _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHarmonicRemainder
