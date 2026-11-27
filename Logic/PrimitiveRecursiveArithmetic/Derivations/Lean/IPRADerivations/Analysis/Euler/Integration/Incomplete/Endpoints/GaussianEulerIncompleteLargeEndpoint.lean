import IPRADerivations.Analysis.Euler.Integration.Incomplete.Cutoffs.GaussianEulerIncompleteFixedCutoff
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAlignment
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailCauchyBudget

/-!
# Original upper incomplete names at encoded integer cutoffs

At the original integer top cutoff, every positive denominator encoding
has the same actual upper-tail bound. The proof rescales the genuine
later compact piece, then removes only its auxiliary cutoff and query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteLargeEndpoint

open_ipra
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerIncompleteName (upperF)
open GaussianEulerCompactAdditivity (nameF)
open GaussianEulerCutoffCauchyComparison (combined)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator)
open GaussianRationalSlackRemoval (precision slack slack_removal_at)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {ℓ : ℕ} {Γ : List (Fm PTm ℓ)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B A b : PTm ℓ) : Fm PTm ℓ :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏ le one b
def data (k z R B A b : PTm ℓ) : PTm ℓ :=
  GaussianEulerIncompleteName.data z R B A (top k A R*b) b

ipra_subst source
ipra_subst data [top, height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem exact_upper_width (k m A R b : PTm ℓ) (h : Γ ⊢[PRAAx] le k m) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCutoff.upperWidth m A R (top k A R*b) b ≐
      b*GaussianGammaCompactCutoffGeometry.upperWidth k m A R := by
  let E := etaDen m A R
  let W := GaussianGammaCompactCutoffGeometry.upperWidth k m A R
  have endpoint : Γ ⊢[PRAAx] (b*E)*top m A R ≐ (top k A R*b)*E+b*W :=
    (by ipra_ring : Γ ⊢[PRAAx] (b*E)*top m A R ≐ b*(E*top m A R)).eqTrans
      ((congrMul (.eqRefl b) (GaussianGammaCompactCutoffSplit.upper_endpoint k m A R h).eqSymm).eqTrans (by ipra_ring))
  exact (congrMonus endpoint (.eqRefl ((top k A R*b)*E))).eqTrans (add_monus' (b*W) ((top k A R*b)*E))

theorem original_endpoint_alignment (k m z R B A b : PTm ℓ)
    (h : Γ ⊢[PRAAx] source z R B A b) (hkm : Γ ⊢[PRAAx] le k m) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF
      (GaussianEulerIncompleteCutoffParts.upperData z R B m A (top k A R*b) b)
      (GaussianGammaCompactCutoffSplit.upperData z R B k m A) := by
  let E := etaDen m A R
  let W := GaussianGammaCompactCutoffGeometry.upperWidth k m A R
  let T := top m A R
  let a := E*top k A R
  have tailSource : Γ ⊢[PRAAx] GaussianGammaCompactCutoffSplit.source z R B k m A :=
    .andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁ hkm)
  have old := GaussianGammaCompactCutoffSplit.upper_source z R B k m A tailSource
  have input : Γ ⊢[PRAAx] GaussianEulerCompactAlignment.source z R B a W E T T b :=
    .andI old.andE₁ (.andI old.andE₂.andE₁ (.andI h.andE₂ (.andI old.andE₂.andE₂ old.andE₂.andE₂)))
  have aligned := GaussianEulerCompactAlignment.aligned_names z R B a W E T T b input
  have literal : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.data z R B (b*a) (b*W) (b*E) T ≐
      GaussianEulerIncompleteCutoffParts.upperData z R B m A (top k A R*b) b :=
    GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _
      (by unfold GaussianEulerIncompleteCutoff.splitPoint; dsimp only [a,E]; ipra_ring)
      (exact_upper_width k m A R b hkm).eqSymm (.eqRefl _) (.eqRefl _)
  exact cross_symm _ _ _ _ (GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _
    (.eqRefl _) literal aligned)

private theorem upper_slack (p t k z R B A b : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A b) : Γ ⊢[PRAAx]
    slack (ap2 upperF p (data k z R B A b))
      (two*majorant R*unit p+unit (height k A R)) (unit (height k A R)*unit p) (num 5) t := by
  let a := top k A R*b
  let m := k+GaussianEulerIncompleteCutoff.clock t a b
  let P := unit p
  let U := unit t
  let H := unit (height k A R)
  let J := unit (height m A R)
  let K := combined A R
  let D := H*P*U
  let V := ap2 upperF p (data k z R B A b)
  let X := ap2 nameF t (GaussianEulerIncompleteCutoffParts.upperData z R B m A a b)
  let Y := ap2 nameF t (GaussianGammaCompactCutoffSplit.upperData z R B k m A)
  have hP := unit_positive (Γ := Γ) p
  have hU := unit_positive (Γ := Γ) t
  have hH := unit_positive (Γ := Γ) (height k A R)
  have hJ := unit_positive (Γ := Γ) (height m A R)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hH hP) hU
  have hm : Γ ⊢[PRAAx] le (GaussianEulerIncompleteCutoff.clock t a b) m := le_add_left _ _
  have hkm : Γ ⊢[PRAAx] le k m := le_add_right _ _
  have later := le_trans (GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) t a b) hm
  have budget := GaussianEulerIncompleteCofinalRate.cutoff_budget t m A R later
  have lc : Γ ⊢[PRAAx] le t (GaussianEulerCutoffCauchyComparison.clock t) := le_add_right _ _
  have tail : Γ ⊢[PRAAx] le (K*U) J :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl K) (GaussianExponentialReference.unit_monotone lc)) budget
  have native : Γ ⊢[PRAAx] GaussianEulerIncompleteCofinalRate.source z R B A a b :=
    .andI h.andE₁ (.andI (positive_product _ _ (GaussianGammaIntegralCutoffs.top_positive k A R) h.andE₂) h.andE₂)
  have rates := GaussianEulerIncompleteFixedCutoff.original_cutoff_rates t m z R B A a b (.andI native hm)
  have first : Γ ⊢[PRAAx] distanceBounded V X ((U+two*P)*H) D :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive J p t hJ) hD
      (by dsimp only [D,P,U,K,H,J,rateNumerator,rateDenominator]
          ipra_le (𝔞(unit (height k A R))*𝔞(unit p)*𝔞(unit p)*𝔞(unit t))*sl tail)
      (rate_at _ _ _ _ _ _ p t rates.andE₂)
  have second : Γ ⊢[PRAAx] distanceBounded X Y (two*H*P) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring))
      (cross_at _ _ _ _ t t (original_endpoint_alignment k m z R B A b h hkm))
  have ts : Γ ⊢[PRAAx] GaussianGammaCompactCutoffSplit.source z R B k m A :=
    .andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁ hkm)
  have hHU := positive_product _ _ hH hU
  have last : Γ ⊢[PRAAx] distanceBounded Y qzero ((two*majorant R*U+H)*P) D :=
    distance_radius_mono _ _ _ _ _ _ hHU hD
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hHU).iffMpr
        (GaussianEulerNamedUpperTail.original_named_upper_tail t z R B k m A ts))
  have total := distance_triangle_same V Y qzero _ _ D hD
    (distance_triangle_same V X Y _ _ D hD first second) last
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [P,U,H,unit]; ipra_ring) (.eqRefl _) total)

theorem original_upper_bound (p k z R B A b : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A b) : Γ ⊢[PRAAx]
    bounded (ap2 upperF p (data k z R B A b))
      (two*majorant R*unit p+unit (height k A R)) (unit (height k A R)*unit p) := by
  let V := ap2 upperF p (data k z R B A b)
  let N := two*majorant R*unit p+unit (height k A R)
  let D := unit (height k A R)*unit p
  let t := precision V N D (num 5)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) (unit_positive _)
  exact slack_removal_at V N D (num 5) hD (upper_slack p t k z R B A b h)

theorem original_dyadic_upper_bound (p k z R B A b : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A b) : Γ ⊢[PRAAx]
    bounded (ap2 upperF p (data k z R B A b))
      (unit p+unit (k+num 6)) (unit (k+num 6)*unit p) := by
  have budget := GaussianEulerUpperTailCauchyBudget.upper_tail_cutoff_budget (Γ := Γ) k A R
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (positive_product _ _ (unit_positive _) (unit_positive _))
    (by ipra_le (𝔞(unit p)*𝔞(unit p))*sl budget) (original_upper_bound p k z R B A b h)

theorem actual_original_upper_incomplete_encoded_integer_cutoff_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ bounded
        (ap2 upperF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (two*majorant (var 3)*unit (var 0)+unit (height (var 1) (var 5) (var 3)))
        (unit (height (var 1) (var 5) (var 3))*unit (var 0))) :=
  closeUniv 7 (.impI (original_upper_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteLargeEndpoint
