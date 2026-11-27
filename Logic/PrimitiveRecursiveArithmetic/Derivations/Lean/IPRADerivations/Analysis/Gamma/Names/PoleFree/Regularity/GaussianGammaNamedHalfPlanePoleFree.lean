import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaNamedPoleFreeProperness

/-!
# Agreement of half-plane and pole-free named Gamma

At a shared late input observation the programs use the same raw
Gaussian numerator and denominator. Native certificate overlap
identifies the resulting Gamma values. The two original freeze rates
then identify the named outputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedHalfPlanePoleFree

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianNamedGamma.nameF
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "hd" => GaussianNamedGamma.data
local notation "pd" => GaussianGammaNamedPoleFree.data
local notation "hs" => GaussianNamedRightHalfPlane.source
local notation "ps" => GaussianGammaNamedPoleFree.source
local notation "he" => GaussianNamedGammaLateInput.encodedData
local notation "pe" => GaussianGammaNamedPoleFree.encodedData

theorem frozen_cross (f : PR 2) (s k x A R E : PTm n)
    (hHalf : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s k x A) (hPole : Γ ⊢[PRAAx] ps f x R E) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (he f k x A) (pe f k x R E) := by
  let z := GaussianNamedRightHalfPlane.numerator f k x
  let B := GaussianNamedRightHalfPlane.denominator f k x
  let S := GaussianNamedRightHalfPlane.radius f x
  have h := GaussianNamedGammaLateInput.encoded_source f s k x A hHalf
  exact GaussianGammaRadiusOverlap.original_Gamma_overlap z S R B one (two*A) one E
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source z S B (two*A) h)
    (GaussianGammaNamedPoleFree.source_at f k x R E hPole)

theorem original_rate (f : PR 2) (s x A R E : PTm n)
    (hHalf : Γ ⊢[PRAAx] hs f x A) (hPole : Γ ⊢[PRAAx] ps f x R E) :
    Γ ⊢[PRAAx] independentRate (H f) (P f) (hd x A) (pd x R E) two (unit s) := by
  let r := GaussianNamedGamma.clock f s x A
  let t := GaussianGammaNamedPoleFree.clock s R E
  let k := r+t
  let u := hd x A
  let v := pd x R E
  let z := he f k x A
  let w := pe f k x R E
  have hr : Γ ⊢[PRAAx] le r k := le_add_right r t
  have ht : Γ ⊢[PRAAx] le t k := le_add_left t r
  have h : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s k x A :=
    .andI hHalf (.andI (le_trans (GaussianNamedGamma.clock_margin f s x A) hr)
      (le_trans (GaussianNamedGamma.clock_demand f s x A s (le_succ_self s)) hr))
  have hU := unit_positive (Γ := Γ) s
  have left := GaussianNamedGammaLateInput.original_independent_rate f s k x A h
  have right := GaussianGammaNamedPoleFreeFrozen.original_frozen_rate f s k x R E hPole ht
  have aligned := GaussianNamedRateTransport.transport (P f) gammaF (P f) gammaF v w v z one (unit s) hU right
    (cross_refl _ _ (GaussianGammaNamedPoleFree.name_regular f x R E hPole)) (frozen_cross f s k x A R E h hPole)
  have back := symmetric (P f) gammaF v z one (unit s) hU aligned
  exact GaussianNamedDifferenceRate.rate_parameters_congr (H f) (P f) u v (one+one) (unit s) two (unit s)
    (by ipra_ring) (.eqRefl _) (same_denominator (H f) gammaF (P f) u z v one (unit s) one hU left back)

theorem original_observation (f : PR 2) (p x A R E : PTm n)
    (hHalf : Γ ⊢[PRAAx] hs f x A) (hPole : Γ ⊢[PRAAx] ps f x R E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (H f) p (hd x A)) (ap2 (P f) p (pd x R E)) (num 4) (unit p) := by
  have hU := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hU
    (le_of_eq_add (d := zero) (by ipra_ring))
    (diagonal_rate (H f) (P f) (hd x A) (pd x R E) two (unit p) p hU (original_rate f p x A R E hHalf hPole))

theorem original_cross (f : PR 2) (x A R E : PTm n)
    (hHalf : Γ ⊢[PRAAx] hs f x A) (hPole : Γ ⊢[PRAAx] ps f x R E) :
    Γ ⊢[PRAAx] crossEquivalent (H f) (P f) (hd x A) (pd x R E) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4)
    (GaussianNamedGamma.name_regular f x A hHalf) (GaussianGammaNamedPoleFree.name_regular f x R E hPole) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (y : PTm n) := Syn.shift y
  have left : Δ ⊢[PRAAx] hs f (sh x) (sh A) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hHalf.shift
  have right : Δ ⊢[PRAAx] ps f (sh x) (sh R) (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hPole.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianNamedGamma.subst_data,
    GaussianGammaNamedPoleFree.subst_data,LeanProofs.IPRA.PTm.subst_num,sh,Syn.shift] using
    original_observation f (var 0) (sh x) (sh A) (sh R) (sh E) left right

theorem actual_named_Gamma_half_plane_pole_free_agreement_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((hs f (var 0) (var 1) ⋏ ps f (var 0) (var 2) (var 3)) ⟶
        crossEquivalent (H f) (P f) (hd (var 0) (var 1)) (pd (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_cross f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedHalfPlanePoleFree
