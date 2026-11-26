import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteCutoffRefinement
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandTimeProperness
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsNamedEndpoints
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteCofinalRate
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPrimitiveEvaluationPascal
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsCompact
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference

/-!
# Boundary values on the two incomplete Euler intervals

The split point is the same rational number in both encodings. The
original shifted integrand there is the shared boundary value. Only the
two external boundaries are small at the computed cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteBoundary

open_ipra
open GaussianEulerIncompleteCutoff (clock denominator splitPoint lowerWidth upperWidth)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerIntegrandName (sample)
open GaussianEulerIntegrationByPartsCompact (boundary)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (qsub qnegative bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def endpointData (z B a b : PTm n) : PTm n := GaussianEulerIntegrandName.data (shifted z B) B a b

ipra_subst endpointData

private theorem pair_to_dyadic (p q t x y : PTm n) (hp : Γ ⊢[PRAAx] le t p) (hq : Γ ⊢[PRAAx] le t q)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit q) (unit p*unit q)) : Γ ⊢[PRAAx]
    distanceBounded x y two (unit t) := by
  have hp' := unit_monotone hp
  have hq' := unit_monotone hq
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive t)
    (by ipra_le 𝔞(unit p)*sl hq'+𝔞(unit q)*sl hp') h

private theorem external_bound (q t x y : PTm n) (hq : Γ ⊢[PRAAx] le t q)
    (h : Γ ⊢[PRAAx] distanceBounded x y two (unit t))
    (hy : Γ ⊢[PRAAx] bounded y (unit q+unit t) (unit q*unit t)) : Γ ⊢[PRAAx]
    distanceBounded x qzero (num 4) (unit t) := by
  have hT := unit_positive (Γ := Γ) t
  have hd := positive_product _ _ (unit_positive q) hT
  have y0 := pair_to_dyadic q t t _ _ hq (le_refl _)
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hd).iffMpr hy)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hT h y0)

theorem original_piece_boundaries (q t k z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIncompleteCofinalRate.source z R B A a b)
    (hk : Γ ⊢[PRAAx] le (clock t a b) k)
    (hExt : Γ ⊢[PRAAx] le (GaussianEulerIntegrationByPartsEndpointBudget.cutoff t R) k)
    (hq : Γ ⊢[PRAAx] le t q) : Γ ⊢[PRAAx]
    distanceBounded (boundary q z B b (lowerWidth k A R a b) (denominator k A R b))
      (sample t (shifted z B) B a b) (num 6) (unit t) ⋏
    distanceBounded (boundary q z B (splitPoint k A R a) (upperWidth k A R a b) (denominator k A R b))
      (qnegative (sample t (shifted z B) B a b)) (num 6) (unit t) := by
  let E := etaDen k A R
  let T := top k A R
  let D := denominator k A R b
  let x := splitPoint k A R a
  let L := lowerWidth k A R a b
  let U := upperWidth k A R a b
  let z' := shifted z B
  let F := sample t z' B a b
  have hB := h.andE₁.andE₁.andE₂.andE₁.andE₁
  have hA := h.andE₁.andE₁.andE₁
  have ha := h.andE₂.andE₁
  have hb := h.andE₂.andE₂
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have hT := GaussianGammaIntegralCutoffs.top_positive (Γ := Γ) k A R
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hb hE
  have hx : Γ ⊢[PRAAx] le one x := positive_product _ _ ha hE
  have hl : Γ ⊢[PRAAx] le one (b+L) := le_trans hb (le_add_right _ _)
  have hu : Γ ⊢[PRAAx] le one (x+U) := le_trans hx (le_add_right _ _)
  have hdomain : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A a b :=
    .andI h.andE₁.andE₁.andE₂.andE₁ (.andI hA h.andE₂)
  have leq := (GaussianEulerIncompleteCutoff.original_partition t k z R B A a b hdomain hk).andE₁
  have req := GaussianEulerIncompleteCutoffRefinement.early_upper_endpoint t k R A a b ha hb hA hk
  have lowSplitEq : Γ ⊢[PRAAx] (b+L)*b ≐ D*a :=
    (congrMul leq (.eqRefl _)).eqTrans (by dsimp only [x, D, splitPoint, denominator]; ipra_ring)
  have highSplitEq : Γ ⊢[PRAAx] x*b ≐ D*a := by dsimp only [x, D, splitPoint, denominator]; ipra_ring
  have splitL := pair_to_dyadic q t t _ _ hq (le_refl _)
    (GaussianEulerIntegrandTimeProperness.original_observations q t z' B (b+L) D a b hB (.andI hl hD) (.andI ha hb) lowSplitEq)
  have splitU := pair_to_dyadic q t t _ _ hq (le_refl _)
    (GaussianEulerIntegrandTimeProperness.original_observations q t z' B x D a b hB (.andI hx hD) (.andI ha hb) highSplitEq)
  have leftEq : Γ ⊢[PRAAx] b*E ≐ D*one := by dsimp only [D, denominator]; ipra_ring
  have rightEq : Γ ⊢[PRAAx] (x+U)*one ≐ D*T :=
    (by ipra_ring : Γ ⊢[PRAAx] (x+U)*one ≐ x+U).eqTrans req
  have left := pair_to_dyadic q q t _ _ hq hq
    (GaussianEulerIntegrandTimeProperness.original_observations q q z' B b D one E hB (.andI hb hD) (.andI (le_refl _) hE) leftEq)
  have right := pair_to_dyadic q q t _ _ hq hq
    (GaussianEulerIntegrandTimeProperness.original_observations q q z' B (x+U) D T one hB (.andI hu hD) (.andI hT (le_refl _)) rightEq)
  have ends := GaussianEulerIntegrationByPartsNamedEndpoints.original_endpoint_bounds q t z R B A k h.andE₁ hExt
  have smallL := external_bound q t _ _ hq left
    (GaussianRationalReciprocal.bound_congr (GaussianEulerIntegrandName.sample_at q z' B one E).eqSymm (.eqRefl _) (.eqRefl _) ends.andE₁)
  have smallU := external_bound q t _ _ hq right
    (GaussianRationalReciprocal.bound_congr (GaussianEulerIntegrandName.sample_at q z' B T one).eqSymm (.eqRefl _) (.eqRefl _) ends.andE₂)
  have hUnit := unit_positive (Γ := Γ) t
  have leftRaw := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hUnit splitL smallL
  have rightRaw := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hUnit smallU splitU
  have negZero : Γ ⊢[PRAAx] qnegative qzero ≐ qzero := GaussianEulerBetaPrimitiveEvaluationPascal.negative_zero
  have lowZero : Γ ⊢[PRAAx] qsub F qzero ≐ F :=
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) negZero).eqTrans
      (GaussianRationalLinearProduct.qadd_zero_right F (GaussianEulerIntegrandName.sample_canonical t z' B a b))
  have highZero : Γ ⊢[PRAAx] qsub qzero F ≐ qnegative F :=
    GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _)
  exact .andI (distance_congr (.eqRefl _) lowZero (by ipra_ring) (.eqRefl _) leftRaw)
    (distance_congr (.eqRefl _) highZero (by ipra_ring) (.eqRefl _) rightRaw)

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteBoundary
