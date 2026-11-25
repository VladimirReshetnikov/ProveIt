import IPRADerivations.Analysis.GaussianStirlingAllOrderFirstPanelReadback
import IPRADerivations.Analysis.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.GaussianNamedBoundedProductObservation

/-!
# The first periodic panel approaches the original named Stirling difference

The actual panel uses the harmonic mesh at the logarithm query selected
by the original Stirling difference. Its half-value has an explicit
dyadic error against that very observation. This gives the one-panel
identification used with the native Stirling telescope.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelNamed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianHarmonicLogarithmName (clock observation independent_original sample_at)
open GaussianStirlingAllOrderFirstPanelReadback (halfPanel harmonic_distance)
open GaussianStirlingDifference (nameF data productF productData coefficient logData minusOne)
open GaussianStirlingOddReadback (affine affine_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def logClock (U B p : PTm n) : PTm n :=
  GaussianNamedBoundedProductObservation.clock constantF GaussianPositiveRationalLogarithm.logF
    (GaussianFastValueCut.exponent two p) (coefficient U B) (logData U B)

def mesh (U B p : PTm n) : PTm n := GammaEulerConstantName.mesh (clock (logClock U B p))

def radiusCoefficient (U B : PTm n) : PTm n :=
  U+B+two*GaussianNameBounds.U constantF (coefficient U B)

private theorem log_clock_large (U B p : PTm n) : Γ ⊢[PRAAx] le p (logClock U B p) := by
  unfold logClock GaussianNamedBoundedProductObservation.clock GaussianFastValueCut.exponent
  exact le_trans (le_add_right _ _) (le_add_right _ _)

theorem mesh_large (U B p : PTm n) : Γ ⊢[PRAAx] le (unit p) (mesh U B p) := by
  let t := logClock U B p
  have hl : Γ ⊢[PRAAx] le p (clock t) := le_trans (log_clock_large U B p) (le_add_right t (num 9))
  have hm := GaussianExponentialReference.unit_monotone hl
  have hd : Γ ⊢[PRAAx] le (unit (clock t)) (mesh U B p) := by
    change Γ ⊢[PRAAx] le (unit (clock t)) (num 4*unit (clock t))
    ipra_le 3*𝔞 (unit (clock t))
  exact le_trans hm hd

private theorem native_affine (U B p : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data U B) ≐
    affine U B (GaussianPositiveRationalLogarithm.sample (logClock U B p) (U+B) U) := by
  let s := GaussianFastValueCut.exponent two p
  let t := logClock U B p
  let f := GaussianPositiveRationalLogarithm.logF
  let x := coefficient U B
  let y := logData U B
  have e := GaussianExponentialReference.add_sample (Γ := Γ) productF constantF (productData U B) minusOne p
  have hp := (GaussianNamedBoundedProductObservation.name_at (Γ := Γ) constantF f s x y).eqTrans
    (qmul_congr (constant_at t x) (.eqRefl _))
  exact e.eqTrans (qadd_congr hp (constant_at s minusOne))

private theorem harmonic_affine_distance (U B p : PTm n) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] distanceBounded (affine U B (observation (logClock U B p) (U+B) U))
      (ap2 nameF p (data U B)) (two*GaussianNameBounds.U constantF (coefficient U B)) (unit p) := by
  let t := logClock U B p
  let g := GaussianHarmonicLogarithmName.nameF
  let d := GaussianHarmonicLogarithmName.data (U+B) U
  let x := coefficient U B
  let a := GaussianHarmonicLogarithmName.sample t (U+B) U
  let b := GaussianPositiveRationalLogarithm.sample t (U+B) U
  let R := GaussianNameBounds.U constantF x
  let S := GaussianNameBounds.U g d
  have src : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (U+B) U := .andI (le_trans hU (le_add_right _ _)) hU
  have ht := unit_positive (Γ := Γ) t
  have hprod := positive_product _ _ ht ht
  have htRef := independent_original t t (U+B) U src
  have hd : Γ ⊢[PRAAx] distanceBounded a b two (unit t) :=
    distance_symmetric _ _ _ _ ht
      (distance_radius_mono _ _ _ _ _ _ hprod ht (by ipra_le 0) htRef)
  have hc : Γ ⊢[PRAAx] bounded x R one :=
    GaussianRationalReciprocal.bound_congr (constant_at t x) (.eqRefl _) (.eqRefl _)
      (GaussianNameBounds.sample_bound constantF x t (constant_regular x))
  have hs : Γ ⊢[PRAAx] bounded a S one :=
    GaussianNameBounds.sample_bound g d t (GaussianHarmonicLogarithmName.name_regular (U+B) U src)
  have hp := GaussianNameArithmetic.product_distance x x a b zero two (unit t) S R ht
    (distance_refl_zero x (unit t) ht) hd hs hc
  have h := GaussianNameArithmetic.sum_distance _ _ minusOne minusOne _ zero (unit t) ht hp
    (distance_refl_zero _ _ ht)
  have e₁ := affine_congr (Γ := Γ) U B (sample_at t (U+B) U)
  have h' : Γ ⊢[PRAAx] distanceBounded (affine U B (observation t (U+B) U))
      (ap2 nameF p (data U B)) (two*R) (unit t) :=
    distance_congr e₁ (native_affine U B p).eqSymm (by ipra_ring) (.eqRefl _) h
  have ht' := GaussianExponentialReference.unit_monotone (log_clock_large (Γ := Γ) U B p)
  exact distance_radius_mono _ _ _ _ _ _ ht (unit_positive p) (by ipra_le 2*𝔞 R*sl ht') h'

theorem observation_distance (A B k p : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (halfPanel A B (mesh (A+B*k) B p) k)
      (ap2 nameF p (data (A+B*k) B)) (radiusCoefficient (A+B*k) B) (unit p) := by
  let U := A+B*k
  let Q := mesh U B p
  let D := two*(B*(PTm.succ (Q*U)))
  let N := U+B
  have hU : Γ ⊢[PRAAx] le one U := le_trans hA (le_add_right A (B*k))
  have qLarge := mesh_large (Γ := Γ) U B p
  have hQ := le_trans (unit_positive p) qLarge
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (by ipra_le 1) (positive_product _ _ hB (zero_lt_succ _))
  have hqU : Γ ⊢[PRAAx] le Q (Q*U) := by ipra_le 𝔞 Q*sl hU
  have hS : Γ ⊢[PRAAx] le (Q*U) (PTm.succ (Q*U)) := le_succ_self _
  have hBD : Γ ⊢[PRAAx] le (PTm.succ (Q*U)) D := by
    unfold D
    ipra_le 𝔞 (PTm.succ (Q*U))*(2*sl hB+1)
  have hLarge := le_trans qLarge (le_trans hqU (le_trans hS hBD))
  have e : Γ ⊢[PRAAx] distanceBounded (halfPanel A B Q k)
      (affine U B (RationalGaussianEmbedding.embed (RationalHarmonicInterval.interval (U+B) U Q))) N D :=
    harmonic_distance A B Q k hA hB hQ
  have first := distance_radius_mono _ _ _ _ N (unit p) hD (unit_positive p)
    (by ipra_le 𝔞 N*sl hLarge) e
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) first (harmonic_affine_distance U B p hU)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelNamed
