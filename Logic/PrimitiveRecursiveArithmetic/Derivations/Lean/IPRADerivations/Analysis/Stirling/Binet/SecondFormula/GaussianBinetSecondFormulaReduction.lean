import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseImproperName
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetFirstFormula
import IPRADerivations.Analysis.Names.Scaling.GaussianNaturalScaleProductName

/-!
# The normalized right-hand side of the second Binet formula

The improper Bose integral already uses the original integrand and
both cutoff rates. Multiplying it by two preserves these observations
with the corresponding doubled error. A uniform comparison to the
original first Binet integral then suffices for the Stirling identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondFormulaReduction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseOriginExhaustion (cutData cutoff cutoff_positive)
open GaussianBinetFirstFormulaDecay (laplaceData laplace_regular)
open GaussianBinetBoseImproperName (source)
open GaussianCoefficientNameBounds (unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedInverseRate (rate_at rateDenominator rateNumerator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product)
open GaussianValueNormalizerExtensionality (rawDiagonal)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Bose" => GaussianBinetBoseImproperName.nameF
local notation "boseData" => GaussianBinetBoseImproperName.data
local notation "Compact" => GaussianBinetBoseCompact.nameF
local notation "First" => GaussianBinetLaplaceImproperName.nameF
local notation "Stirling" => GaussianBinetStirlingRemainder.nameF
local notation "remainderData" => GaussianBinetStirlingRemainder.data

def nameF : PR 2 := GaussianNaturalScaleProductName.productF Bose
def data (X Y D sign K : PTm n) : PTm n :=
  GaussianNaturalScaleProductName.productData Bose two (boseData X Y D sign K)
def clock (p X Y D sign K : PTm n) : PTm n :=
  GaussianNaturalScaleProductName.clock Bose p two (boseData X Y D sign K)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (X Y D sign K : PTm n) :
    Syn.subst σ (data X Y D sign K) = data (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D)
      (Syn.subst σ sign) (Syn.subst σ K) := by simp [data,two]

theorem regular (X Y D sign K : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign K) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign K) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianGammaCanonicalExponent.constant_regular (naturalPoint two))
    (GaussianBinetBoseImproperName.regular X Y D sign K h)

theorem sample_at (p X Y D sign K : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data X Y D sign K) ≐
      natScale two (ap2 Bose (clock p X Y D sign K) (boseData X Y D sign K)) :=
  GaussianNaturalScaleProductName.product_at Bose p two (boseData X Y D sign K)

theorem window_observation (p q X Y D sign K T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K) (hT : Γ ⊢[PRAAx] le one T) :
    let C := cutoff L*(num 4*X)
    let s := clock p X Y D sign K
    Γ ⊢[PRAAx] distanceBounded
      (ap2 nameF p (data X Y D sign K))
      (natScale two (ap2 Compact q (cutData X Y D sign T L)))
      (two*rateNumerator ((two*K)*C+D*T) (T*C) s q) (rateDenominator (T*C) s q) := by
  let C := cutoff L*(num 4*X)
  let s := clock p X Y D sign K
  let A := (two*K)*C+D*T
  let B := T*C
  let x := ap2 Bose s (boseData X Y D sign K)
  let y := ap2 Compact q (cutData X Y D sign T L)
  have hC := positive_product _ _ (cutoff_positive (Γ := Γ) L)
    (positive_product (num 4) X (by ipra_le 3) h.andE₁.andE₁.andE₁)
  have hB := positive_product _ _ hT hC
  have rate := GaussianBinetBoseImproperName.compact_rate X Y D sign K T L h hT
  have old := rate_at Bose Compact (boseData X Y D sign K) (cutData X Y D sign T L) A B s q rate
  have norm := GaussianNamedNaturalScale.natural_point_bound (Γ := Γ) (two : PTm n)
  have mul := GaussianApproximateInverseDistance.multiply_distance (naturalPoint two) x y two
    (rateNumerator A B s q) (rateDenominator B s q) (denominator_positive B s q hB) norm old
  have left := (sample_at (Γ := Γ) p X Y D sign K).eqTrans (natScale_as_product two x)
  exact distance_congr left.eqSymm (natScale_as_product two y).eqSymm (.eqRefl _) (.eqRefl _) mul

/-- The remaining arithmetic comparison can use diagonal observations of
the two original improper samplers at any uniform certified cost. -/
theorem identity_of_improper_comparison (X Y D sign K c z : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K)
    (hEq : Γ ⊢[PRAAx] rawDiagonal First nameF (laplaceData X Y D sign) (data X Y D sign K) c) :
    Γ ⊢[PRAAx] crossEquivalent Stirling nameF (remainderData X Y D sign z) (data X Y D sign K) := by
  have eq := GaussianNameRingLaws.equivalent_of_envelope First nameF (laplaceData X Y D sign)
    (data X Y D sign K) c (laplace_regular X Y D sign h.andE₁) (regular X Y D sign K h) hEq
  exact cross_trans Stirling First nameF _ _ _ (GaussianBinetFirstFormula.equivalent X Y D sign z h.andE₁) eq

theorem actual_second_Binet_scaled_improper_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondFormulaReduction
