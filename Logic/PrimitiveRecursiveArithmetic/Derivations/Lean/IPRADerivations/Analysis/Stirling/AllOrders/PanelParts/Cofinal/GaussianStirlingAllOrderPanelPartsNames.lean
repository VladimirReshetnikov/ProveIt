import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.OuterSums.GaussianStirlingAllOrderPanelPartsSolve
import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.GaussianStirlingAllOrderFirstPanelPrefix
import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderPowerIntegralMeshCells
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianBoundedConstantProductName

/-!
# Named arithmetic for the centered Bernoulli integral recurrence

Each fixed order has a primitive-recursive regular expression.
The initial value is twice the original Stirling remainder.
The recurrence uses the exact rational primitive of the
inverse-power weight, the actual Bernoulli coefficient, and
the derivative ratio from finite integration by parts.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsNames

open_ipra
open GaussianStirlingAllOrderPanelPartsSolve (ratio)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingGlobalBounds (remainderF remainderData remainder_regular)
open GaussianStirlingNames (source)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalHorner (qmul)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianNameBounds (U sample_bound)
open GaussianEuclideanDistanceName (pointCN fraction)
open RationalArithmetic (multiply)
open RationalGaussianEmbedding (embed)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "scaleF" => GaussianBoundedConstantProductName.nameF
local notation "scaleData" => GaussianBoundedConstantProductName.data
local notation "subF" => GaussianNamedDifference.nameF
local notation "subData" => GaussianNamedDifference.data

def initial : PTm n := embed (fraction two one)
def derivativeRatio (m : ℕ) : PTm n := embed (ratio (m+1) (2*m+2))
def weightedPrimitive (m : ℕ) (A B : PTm n) : PTm n :=
  embed (multiply (signedMean (m+1)) (primitive (2*m+2) A B))

def constantCap (q : PTm n) : PTm n := U constantF q

def nameF : ℕ → PR 2
  | 0 => scaleF remainderF
  | m+1 => scaleF (subF constantF (nameF m))

def nameData : ℕ → PTm n → PTm n → PTm n → PTm n
  | 0,A,B,x => scaleData (constantCap initial) initial (remainderData A B x)
  | m+1,A,B,x => scaleData (constantCap (derivativeRatio m)) (derivativeRatio m)
      (subData (weightedPrimitive m A B) (nameData m A B x))

@[simp] theorem subst_initial {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (initial : PTm n) = (initial : PTm l) := by simp [initial]
@[simp] theorem subst_derivativeRatio {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (derivativeRatio m : PTm n) = (derivativeRatio m : PTm l) := by
  simp [derivativeRatio,ratio,GaussianStirlingAllOrderPanelPartsSolve.inverseHigh,
    GaussianStirlingAllOrderPanelPartsDensities.lowScalar,GaussianStirlingAllOrderReciprocalWeightError.coefficient]
ipra_subst weightedPrimitive [signedMean, GaussianStirlingAllOrderPanelDerivative.meanNumerator, BernoulliBounds.zint]
ipra_subst constantCap
@[simp] theorem subst_nameData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B x : PTm n) :
    Syn.subst σ (nameData m A B x) = nameData m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by
  induction m with
  | zero => simp [nameData]
  | succ m ih => simp [nameData,ih]

theorem constant_bound (q : PTm n) : Γ ⊢[PRAAx] bounded q (constantCap q) one :=
  bound_congr (constant_at zero q) (.eqRefl _) (.eqRefl _)
    (sample_bound constantF q zero (constant_regular q))

theorem name_regular (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    pointCN (nameF m) (nameData m A B x) := by
  induction m with
  | zero =>
    exact GaussianBoundedConstantProductName.name_regular _ _ _ _
      (.andI (remainder_regular A B x hs) (constant_bound _))
  | succ m ih =>
    apply GaussianBoundedConstantProductName.name_regular
    exact .andI (GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) ih) (constant_bound _)

theorem fixed_product_distance (c a b N D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded a b N D) : Γ ⊢[PRAAx]
    distanceBounded (qmul c a) (qmul c b) (constantCap c*N) D := by
  have q := GaussianNameArithmetic.product_distance c c a b zero N D (constantCap a) (constantCap c) hD
    (distance_refl_zero c D hD) h (constant_bound a) (constant_bound c)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) q

theorem normalized_product_error (f : PR 2) (c x p : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (scaleF f) p (scaleData (constantCap c) c x)) (qmul c (ap2 f p x))
      (constantCap c+one) (unit p) := by
  have h := GaussianBoundedConstantProductName.raw_name_regular f (constantCap c) c x (.andI hf (constant_bound c))
  exact distance_congr (.eqRefl _) (GaussianBoundedConstantProductName.raw_at f p c x) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.normalized_to_sample (GaussianBoundedConstantProductName.rawF f) _ _ p h)

theorem difference_error (m : ℕ) (A B x p : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (subF constantF (nameF m)) p (subData (weightedPrimitive m A B) (nameData m A B x)))
      (qsub (weightedPrimitive m A B) (ap2 (nameF m) p (nameData m A B x))) (LeanProofs.IPRA.PTm.num 6) (unit p) :=
  distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qsub_congr (constant_at p (weightedPrimitive m A B)) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (GaussianNamedDifference.sample_error _ _ _ _ _ (constant_regular _) (name_regular m A B x hs))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsNames
