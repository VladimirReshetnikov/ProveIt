import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmLinearRemainder
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialRadiusIndependence

/-!
# The terminal logarithm remainder in the Barnes shift

The original local logarithm at `1+w/K` is scaled by the exact
integer cutoff. Subtracting `w` leaves a uniform disk error of order
`R²/K`, with a fixed dyadic observation allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTerminalRemainder

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qzero ofGaussian ofGaussian_canonical ofGaussian_represents positive_product
  canonical_unique represents_congr represents_rescale)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_canonical natScale_represents)
open GaussianRationalSyntheticDivision (qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianLocalLogarithmName.pointF
local notation "ld" => GaussianLocalLogarithmName.data

def source (w R B K : PTm n) : Fm PTm n :=
  le one B ⋏ (le one K ⋏ (ComplexLogarithmRemainder.bounded w (R*B) ⋏ le (two*R) K))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (w R B K : PTm n) :
    (source w R B K).subst σ = source (Syn.subst σ w) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [source,one,two]

abbrev scaledF : PR 2 := GaussianNamedNaturalScale.nameF L
def scaledData (w R B K : PTm n) : PTm n := GaussianNamedNaturalScale.data K K (ld w (R*B) (B*K))
abbrev nameF : PR 2 := GaussianNamedDifference.nameF scaledF constantF
def data (w R B K : PTm n) : PTm n := GaussianNamedDifference.data (scaledData w R B K) (ofGaussian w B)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (w R B K : PTm n) :
    Syn.subst σ (data w R B K) = data (Syn.subst σ w) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [data,scaledData]

theorem local_source (w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) : Γ ⊢[PRAAx]
    GaussianLocalLogarithmName.source w (R*B) (B*K) :=
  .andI (positive_product B K h.andE₁ h.andE₂.andE₁) (.andI h.andE₂.andE₂.andE₁
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl B) h.andE₂.andE₂.andE₂)))

theorem scaled_regular (w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) : Γ ⊢[PRAAx]
    pointCN scaledF (scaledData w R B K) :=
  GaussianNamedNaturalScale.name_regular L K K one _
    (GaussianExponentialRadiusIndependence.radius_one_input L _
      (GaussianLocalLogarithmName.original_exponential_input _ _ _ (local_source w R B K h))) (le_refl K)

theorem regular (w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) : Γ ⊢[PRAAx] pointCN nameF (data w R B K) :=
  GaussianNamedDifference.name_regular _ _ _ _ (scaled_regular w R B K h) (constant_regular _)

theorem scaled_linear (w B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    natScale K (ofGaussian w (B*K)) ≐ ofGaussian w B := by
  let D := B*K
  have hD := positive_product B K hB hK
  exact canonical_unique _ _ _ D (natScale_canonical _ _) (ofGaussian_canonical _ _ hB) hD
    (natScale_represents K _ w D hD (ofGaussian_represents _ _ hD))
    (represents_rescale _ w B K (ofGaussian_represents _ _ hB))

theorem scaled_sample_error (p w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 scaledF p (scaledData w R B K)) (ofGaussian w B)
      (R*R*unit p+K) (K*unit p) := by
  have hD := positive_product B K h.andE₁ h.andE₂.andE₁
  have near := GaussianLocalLogarithmLinearRemainder.scaled_linear_remainder p K K w (R*B) (B*K)
    (local_source w R B K h) (le_refl K)
  exact distance_congr (.eqRefl _) (scaled_linear w B K h.andE₁ h.andE₂.andE₁) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hD hD) (unit_positive p))
      (positive_product _ _ h.andE₂.andE₁ (unit_positive p)) (le_of_eq_add (d := zero) (by ipra_ring)) near)

theorem sample_error (p w R B K : PTm n) (h : Γ ⊢[PRAAx] source w R B K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data w R B K)) qzero (R*R*unit p+num 7*K) (K*unit p) := by
  let x := ap2 scaledF p (scaledData w R B K)
  let a := ofGaussian w B
  let U := unit p
  let E := K*U
  let y := ap2 nameF p (data w R B K)
  have hp := unit_positive (Γ := Γ) p
  have he := positive_product K U h.andE₂.andE₁ hp
  have obs := GaussianNamedDifference.sample_error scaledF constantF (scaledData w R B K) a p
    (scaled_regular w R B K h) (constant_regular a)
  have read := distance_congr (.eqRefl y) (qsub_congr (.eqRefl x) (constant_at p a)) (.eqRefl _) (.eqRefl _) obs
  have widened := distance_radius_mono y (qsub x a) _ _ (num 6*K) E hp he
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) read
  have last := GaussianNamedDifference.difference_distance x a a a (R*R*U+K) zero E he
    (scaled_sample_error p w R B K h) (GaussianRationalPowerDifference.distance_refl_zero a E he)
  have exact_last := distance_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self a) (.eqRefl _) (.eqRefl _) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same y (qsub x a) qzero _ _ E he widened exact_last)

theorem actual_Barnes_terminal_logarithm_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let K := var 4
     source w R B K ⟶ distanceBounded (ap2 nameF p (data w R B K)) qzero
       (R*R*unit p+num 7*K) (K*unit p)) :=
  closeUniv 5 (.impI (sample_error _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTerminalRemainder
