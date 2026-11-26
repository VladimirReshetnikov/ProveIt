import IPRADerivations.Analysis.Gamma.BohrMollerup.FiniteBrackets.GaussianBohrMollerupChords
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference

/-!
# Named logarithmic increment squeeze for a fixed presentation

The two chords and the exact recurrence put the scaled increment
between a log(j) and a log(j+1+a/b). These two comparison names are
independent of the presentation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1850000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupSqueeze

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupChords (base translated base_source translated_source scaled_regular scale_cross)
open GaussianBohrMollerupPresentation (Presentation argument scaledF scaledData
  observe_value observe_recurrence values recurrence rescaling convexity)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaRationalFractionalChord (scale_sum)
open GaussianGammaStrongLogConvexityAlgebra (cancel_common swap_first)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative negativeF negativeData negative_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderTransport (transport)
open GaussianNamedStrictOrderDifference (sum_sub_right)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => productF H

def logData (w a b : PTm n) : PTm n := productData H w (hd a b)

def incrementF (P : Presentation) : PR 2 := GaussianNamedDifference.nameF (scaledF P) (scaledF P)
def incrementData (P : Presentation) (a b j : PTm n) : PTm n :=
  GaussianNamedDifference.data (scaledData P b (translated a b j) b) (scaledData P b (base b j) b)

theorem log_regular (w a b : PTm n) (s : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN L (logData w a b) :=
  scaled_regular H w _ (GaussianHarmonicLogarithmName.name_regular a b s)

theorem weighted_recurrence (P : Presentation) (a b w : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P) (s : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (scaledF P) (addF L (scaledF P)) (scaledData P w (a+b) b)
      (addData (logData w a b) (scaledData P w a b)) := by
  let q := naturalPoint w
  have hq := constant_regular (Γ := Γ) q
  have hh := GaussianHarmonicLogarithmName.name_regular a b s
  have hx := (observe_value P a b hv s).andE₁
  have hy := (observe_value P (a+b) b hv (GaussianStirlingGammaLogarithm.source_shift a b s)).andE₁
  have step := GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ q q (argument P (a+b) b)
    (addData (hd a b) (argument P a b)) hq hq hy (add_fast _ _ _ _ hh hx) (cross_refl _ _ hq)
    (observe_recurrence P a b hr s)
  exact cross_trans _ _ _ _ _ _ step (GaussianNameRingLaws.distributive _ _ _ _ _ _ hq hh hx)

private theorem weak_difference_order (F H' J : PR 2) (x y z : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN H' y) (hz : Γ ⊢[PRAAx] pointCN J z)
    (ord : Γ ⊢[PRAAx] realOrder F (addF H' J) x (addData y z)) : Γ ⊢[PRAAx]
    realOrder (GaussianNamedDifference.nameF F J) H' (GaussianNamedDifference.data x z) y := by
  let N := negativeF J
  let Z := negativeData z
  have reg := negative_fast J z hz
  have hh := add_order F (addF H' J) N N x (addData y z) Z Z ord (order_refl _ _ reg)
  exact transport _ _ _ _ _ _ _ _ (cross_refl _ _ (add_fast _ _ _ _ hx reg))
    (sum_sub_right H' J y z hy hz) hh

private theorem order_weak_difference (F H' J : PR 2) (x y z : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN H' y) (hz : Γ ⊢[PRAAx] pointCN J z)
    (ord : Γ ⊢[PRAAx] realOrder (addF F J) H' (addData x z) y) : Γ ⊢[PRAAx]
    realOrder F (GaussianNamedDifference.nameF H' J) x (GaussianNamedDifference.data y z) := by
  let N := negativeF J
  let Z := negativeData z
  have reg := negative_fast J z hz
  have hh := add_order (addF F J) H' N N (addData x z) y Z Z ord (order_refl _ _ reg)
  exact transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (sum_sub_right F J x z hx hz))
    (cross_refl _ _ (add_fast _ _ _ _ hy reg)) hh

theorem increment_regular (P : Presentation) (a b j : PTm n) (hv : Γ ⊢[PRAAx] values P)
    (s : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN (incrementF P) (incrementData P a b j) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (scaled_regular _ _ _ (observe_value P (translated a b j) b hv (translated_source a b j s.andE₂)).andE₁)
    (scaled_regular _ _ _ (observe_value P (base b j) b hv (base_source b j s.andE₂)).andE₁)

theorem lower_increment (P : Presentation) (a b j : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P)
    (hs : Γ ⊢[PRAAx] rescaling P) (hc : Γ ⊢[PRAAx] convexity P)
    (s : Γ ⊢[PRAAx] source a b) (hj : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx]
    realOrder L (incrementF P) (logData a (b*j) b) (incrementData P a b j) := by
  let G := scaledF P
  let u := scaledData P a (b*j) b
  let v := scaledData P b (base b j) b
  let w := scaledData P b (translated a b j) b
  let h := logData a (b*j) b
  let z := scaledData P a (base b j) b
  have sourceU : Γ ⊢[PRAAx] source (b*j) b := .andI (positive_product _ _ s.andE₂ hj) s.andE₂
  have ru : Γ ⊢[PRAAx] pointCN G u := scaled_regular _ _ _ (observe_value P _ _ hv sourceU).andE₁
  have r0 := (observe_value P _ _ hv (base_source b j s.andE₂)).andE₁
  have rv : Γ ⊢[PRAAx] pointCN G v := scaled_regular _ _ _ r0
  have rw : Γ ⊢[PRAAx] pointCN G w :=
    scaled_regular _ _ _ (observe_value P _ _ hv (translated_source a b j s.andE₂)).andE₁
  have rh := log_regular a (b*j) b sourceU
  have rz : Γ ⊢[PRAAx] pointCN G z := scaled_regular _ _ _ r0
  have current := (observe_value P _ _ hv (GaussianStirlingGammaLogarithm.source_shift _ _ sourceU)).andE₁
  have change := scale_cross P.nameF a a _ _ (.eqRefl _) r0 current
    (cross_data_congr P.nameF P.nameF _ _ _ _ (.eqRefl _)
      (GaussianBohrMollerupChords.argument_congr P (base b j) b (b*j+b) b (by unfold base; ipra_ring) (.eqRefl _))
      (cross_refl _ _ r0))
  have expand := cross_trans _ _ _ _ _ _ change (weighted_recurrence P (b*j) b a hv hr sourceU)
  have left0 := GaussianBohrMollerupChords.lower_chord P a b j hv hs hc s hj
  have col := scale_sum P.nameF a b (a+b) (argument P (base b j) b) (.eqRefl _) r0
  have replace := add_cross G (addF L G) G G z (addData h u) v v rz (add_fast _ _ _ _ rh ru)
    rv rv expand (cross_refl _ _ rv)
  have flip := cross_trans _ _ _ _ _ _ (add_associative L G G h u v rh ru rv)
    (swap_first L G G h u v rh ru rv)
  have left := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ col) (cross_trans _ _ _ _ _ _ replace flip)
  have applied := transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_refl _ _ (add_fast _ _ _ _ ru rw)) left0
  exact order_weak_difference L G G h w v rh rw rv
    (cancel_common G (addF L G) G u (addData h v) w ru (add_fast _ _ _ _ rh rv) rw applied)

theorem upper_increment (P : Presentation) (a b j : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P)
    (hs : Γ ⊢[PRAAx] rescaling P) (hc : Γ ⊢[PRAAx] convexity P)
    (s : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    realOrder (incrementF P) L (incrementData P a b j) (logData a (translated a b j) b) := by
  let G := scaledF P
  let t := translated a b j
  let u := scaledData P a t b
  let v := scaledData P b (base b j) b
  let w := scaledData P b t b
  let h := logData a t b
  let z := scaledData P a (t+b) b
  have st := translated_source a b j s.andE₂
  have r0 := (observe_value P _ _ hv st).andE₁
  have ru : Γ ⊢[PRAAx] pointCN G u := scaled_regular _ _ _ r0
  have rv : Γ ⊢[PRAAx] pointCN G v :=
    scaled_regular _ _ _ (observe_value P _ _ hv (base_source b j s.andE₂)).andE₁
  have rw : Γ ⊢[PRAAx] pointCN G w := scaled_regular _ _ _ r0
  have rh := log_regular a t b st
  have rz : Γ ⊢[PRAAx] pointCN G z :=
    scaled_regular _ _ _ (observe_value P _ _ hv (GaussianStirlingGammaLogarithm.source_shift _ _ st)).andE₁
  have col := scale_sum P.nameF a b (b+a) (argument P t b) (add_comm a b) r0
  have replace := add_cross G G G (addF L G) v v z (addData h u) rv rv rz (add_fast _ _ _ _ rh ru)
    (cross_refl _ _ rv) (weighted_recurrence P t b a hv hr st)
  have flip := cross_trans _ _ _ _ _ _
    (add_commutative G (addF L G) v (addData h u) rv (add_fast _ _ _ _ rh ru))
    (cross_trans _ _ _ _ _ _ (add_associative L G G h u v rh ru rv) (swap_first L G G h u v rh ru rv))
  have applied := transport _ _ _ _ _ _ _ _ col (cross_trans _ _ _ _ _ _ replace flip)
    (GaussianBohrMollerupChords.upper_chord P a b j hv hs hc s)
  exact weak_difference_order G L G w h v rw rh rv
    (cancel_common G G (addF L G) u w (addData h v) ru rw (add_fast _ _ _ _ rh rv) applied)

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupSqueeze
