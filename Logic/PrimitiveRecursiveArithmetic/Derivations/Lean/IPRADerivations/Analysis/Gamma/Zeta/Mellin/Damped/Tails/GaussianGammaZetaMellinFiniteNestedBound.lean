import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.Windows.GaussianGammaZetaMellinFiniteNested

/-!
# Removing both exterior pieces of the actual finite damped window

Keep the actual finite count and read clock on every panel, including
the rescaled middle panel. Only the two exterior norms are estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteNestedBound

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (data)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaZetaMellinCutoffWindows (panel_split_input three_panel_observation comparison_from_panel_bounds)
open GaussianGammaCompactCutoffGeometry
  (lowerWidth middleWidth upperWidth lower_positive middle_positive upper_positive widths_total three_endpoint)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaZetaMellinFiniteNested (datum interval_source compact_input middle_alignment)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF)
open GaussianGammaZetaMellinFiniteDampedModulus (lipschitz)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (qadd qzero canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerLowerPowerCoefficients.source
local notation "F" => GaussianCompactRiemannName.nameF evaluatorF
local notation "fd" => GaussianGammaZetaMellinFiniteDampedEvaluator.data
local notation "I" => GaussianEulerCompactAdditivity.intervalSource

theorem split_windows_at (r z R B A N Q p q : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B A) (hQ : Γ ⊢[PRAAx] le N Q) (hpq : Γ ⊢[PRAAx] lt p q) :
    let E := etaDen q A R
    let T := top q A R
    let L := lipschitz N (R+one) E T
    let x := fd (shifted z B) B N Q
    let C₁ := lowerWidth p q A
    let C₂ := middleWidth p q A R
    let C₃ := upperWidth p q A R
    let l := ap2 F r (data one C₁ E L T x)
    let m := ap2 F r (data (one+C₁) C₂ E L T x)
    let h := ap2 F r (data (one+(C₁+C₂)) C₃ E L T x)
    Γ ⊢[PRAAx] distanceBounded (ap2 F r (datum z R B N Q A q)) (qadd (qadd l m) h) one (unit r) := by
  intro E T L x C₁ C₂ C₃ l m h
  have hE := eta_den_positive (Γ := Γ) q A R
  have c₁ := lower_positive p q A hz.andE₁ hpq
  have c₂ := middle_positive (Γ := Γ) p q A R
  have c₃ := upper_positive p q A R hpq
  have endpoint : Γ ⊢[PRAAx] one+(C₁+C₂+C₃) ≐ E*T := three_endpoint p q A R (le_of_lt hpq)
  have full : Γ ⊢[PRAAx] I (shifted z B) (R+one) B one (C₁+C₂+C₃) E T :=
    interval_source z R B A _ _ _ _ hz (le_refl one) hE (le_congr endpoint.eqSymm (.eqRefl _) (le_refl _))
  have firstTwo : Γ ⊢[PRAAx] I (shifted z B) (R+one) B one (C₁+C₂) E T :=
    interval_source z R B A _ _ _ _ hz (le_refl one) hE
      (le_trans (le_congr (by ipra_ring) (add_comm _ _) (add_le_add_right one (le_add_right (C₁+C₂) C₃))) full.andE₂.andE₂)
  exact three_panel_observation evaluatorF r one (width q A R) C₁ C₂ C₃ E L T x
    (widths_total p q A R (le_of_lt hpq)).eqSymm
    (panel_split_input evaluatorF one (C₁+C₂) C₃ E L T x
      (compact_input _ _ _ _ _ _ _ _ _ full hQ) (le_trans c₁ (le_add_right _ _)) c₃)
    (panel_split_input evaluatorF one C₁ C₂ E L T x (compact_input _ _ _ _ _ _ _ _ _ firstTwo hQ) c₁ c₂)

theorem comparison_from_tails (r z R B A N Q p q V X Y : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B A) (hQ : Γ ⊢[PRAAx] le N Q) (hpq : Γ ⊢[PRAAx] lt p q)
    (hV : Γ ⊢[PRAAx] le one V)
    (lower : Γ ⊢[PRAAx] bounded (ap2 F r (GaussianGammaZetaMellinFiniteNested.data
      (shifted z B) (R+one) B N Q one (lowerWidth p q A) (etaDen q A R) (top q A R))) X (V*unit r))
    (upper : Γ ⊢[PRAAx] bounded (ap2 F r (GaussianGammaZetaMellinFiniteNested.data (shifted z B) (R+one) B N Q
      (one+(lowerWidth p q A+middleWidth p q A R)) (upperWidth p q A R) (etaDen q A R) (top q A R))) Y (V*unit r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F r (datum z R B N Q A q)) (ap2 F r (datum z R B N Q A p))
      (X+Y+num 3*V) (V*unit r) := by
  let E := etaDen q A R
  let T := top q A R
  let L := lipschitz N (R+one) E T
  let x := fd (shifted z B) B N Q
  let C₁ := lowerWidth p q A
  let C₂ := middleWidth p q A R
  let C₃ := upperWidth p q A R
  let d := data (one+C₁) C₂ E L T x
  let l := ap2 F r (data one C₁ E L T x)
  let m := ap2 F r d
  let h := ap2 F r (data (one+(C₁+C₂)) C₃ E L T x)
  let f := ap2 F r (datum z R B N Q A q)
  let g := ap2 F r (datum z R B N Q A p)
  let U := unit r
  let D := V*U
  have hU := unit_positive (Γ := Γ) r
  have hD := positive_product _ _ hV hU
  have lo : Γ ⊢[PRAAx] distanceBounded l qzero X D :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr lower
  have hi : Γ ⊢[PRAAx] distanceBounded h qzero Y D :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr upper
  have cm : Γ ⊢[PRAAx] canonical m :=
    GaussianRationalHorner.canonical_congr (GaussianCompactRiemannName.name_at evaluatorF r (one+C₁) C₂ E L T x)
      (GaussianCompactRiemannName.sample_canonical evaluatorF r (one+C₁) C₂ E L T x)
  have split : Γ ⊢[PRAAx] distanceBounded f (qadd (qadd l m) h) V D :=
    distance_radius_mono _ _ _ _ _ _ hU hD (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring))
      (split_windows_at r z R B A N Q p q hz hQ hpq)
  have eq := middle_alignment z R B N Q A p q hz hQ (le_of_lt hpq)
  have raw := cross_at F F d (datum z R B N Q A p) r r (cross_symm _ _ _ _ eq)
  have aligned : Γ ⊢[PRAAx] distanceBounded m g (two*V) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring)) raw
  exact comparison_from_panel_bounds f g l m h V X Y D hD cm lo hi split aligned

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteNestedBound
