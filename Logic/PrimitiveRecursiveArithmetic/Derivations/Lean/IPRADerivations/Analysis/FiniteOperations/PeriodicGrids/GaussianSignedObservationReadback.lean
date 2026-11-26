import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianSignedObservationGrid
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut

/-!
# Readback of signed grid bounds to original real observations

The real projection of an observation lies within one lattice unit of
the actual rounded point. A signed grid difference bounded by E
therefore gives an original projected distance of at most (E+2)/S.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianSignedObservationReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (re im code scale normSq normSq_eval eval_re_code eval_im_code)
open GaussianRootAlgebra (sub re_sub im_sub re_scale im_scale equal_refl)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive)
open GaussianRationalHorner (ofGaussian_represents represents_rescale represents_congr positive_product)
open GaussianRationalMetric (distanceBounded bounded_difference_iff)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianSignedObservationGrid (rounded realPoint clearedError rounding_error body data wrapped_sample_mod)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open PeriodicThirdDifferenceConstancy (band cubicBudget)
open PolynomialBisection (zle_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def realProjection (q : PTm n) : PTm n := realPoint (re (rawGaussian q)) (rawDen q)

@[simp] theorem subst_realProjection {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (realProjection q) = realProjection (Syn.subst σ q) := by
  simp [realProjection]

private theorem absolute_of_band (a : ZT n) (E : PTm n)
    (h : Γ ⊢[PRAAx] band a E) :
    Γ ⊢[PRAAx] le (zabs a) E := by
  have upper : Γ ⊢[PRAAx] le (a.pos+zero) (E+a.neg) := h.andE₂
  have lower : Γ ⊢[PRAAx] le (zero+a.neg) (a.pos+E) := h.andE₁
  exact ad_le_of (le_congr (add_zero _) (add_comm _ _) upper)
    (le_congr (zero_add _) (.eqRefl _) lower)

private theorem norm_from_real (a : PTm n) (u : ZT n)
    (hr : ZT.toZ Γ (re a) = ZT.toZ Γ u) (hi : ZT.toZ Γ (im a) = 0) :
    Γ ⊢[PRAAx] normSq a ≐ zabs u*zabs u := by
  apply deriveNat
  rw [normSq_eval,zabs_sq,hr,hi]
  ring

theorem lattice_distance (a b : ZT n) (S E : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (h : Γ ⊢[PRAAx] band (a-b) E) :
    Γ ⊢[PRAAx] distanceBounded (realPoint a S) (realPoint b S) E S := by
  let u := code a (ZT.ofNat zero)
  let v := code b (ZT.ofNat zero)
  have sq := norm_from_real (Γ := Γ) (sub u v) (a-b)
    (by simp only [u,v,re_sub,eval_re_code,ZT.toZ_sub])
    (by simp only [u,v,im_sub,eval_im_code,sub_self])
  have r := absolute_of_band _ _ h
  apply (bounded_difference_iff _ _ _ _ _ _ _ hS hS
    (ofGaussian_represents u S hS) (ofGaussian_represents v S hS)).iffMpr
  exact le_congr (congrMul (.eqRefl (S*S)) sq.eqSymm) (mul_comm _ _)
    (le_mul_mono (le_refl (S*S)) (le_mul_mono r r))

/-- Compare the rounded point to the projected real value of the same observation. -/
theorem rounded_distance (q S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] distanceBounded (realPoint (rounded q S) S) (realProjection q) one S := by
  let D := rawDen q
  let u := code (rounded q S) (ZT.ofNat zero)
  let v := code (re (rawGaussian q)) (ZT.ofNat zero)
  let d := sub (scale D u) (scale S v)
  have hD := raw_den_positive (Γ := Γ) q
  have hu := represents_rescale _ u S D (ofGaussian_represents u S hS)
  have hv := represents_rescale _ v D S (ofGaussian_represents v D hD)
  have hv' := represents_congr (.eqRefl _) (equal_refl _) (mul_comm D S) hv
  have sq := norm_from_real (Γ := Γ) d (clearedError q S)
    (by simp only [d,D,u,v,clearedError,re_sub,re_scale,eval_re_code,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat])
    (by simp only [d,u,v,im_sub,im_scale,eval_im_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]; ring)
  have r := rounding_error (Γ := Γ) q S
  apply (bounded_difference_iff _ _ _ _ _ _ _ (positive_product S D hS hD) hS hu hv').iffMpr
  exact le_congr (congrMul (.eqRefl (S*S)) sq.eqSymm) (by ipra_ring)
    (le_mul_mono (le_refl (S*S)) (le_mul_mono r r))

theorem projected_distance (q r S E : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (h : Γ ⊢[PRAAx] band (rounded q S-rounded r S) E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection q) (realProjection r) (E+two) S := by
  have first := distance_symmetric _ _ _ _ hS (rounded_distance q S hS)
  have middle := lattice_distance _ _ S E hS h
  have last := rounded_distance r S hS
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hS (distance_triangle_same _ _ _ _ _ _ hS first middle) last)

theorem wrapped_projected_distance (f : PTm 2) (x S i j N E : PTm n)
    (hS : Γ ⊢[PRAAx] le one S)
    (h : let b := PeriodicThirdDifferenceModulo.wrapped (body f)
         let d := PeriodicThirdDifferenceModulo.data (data x S) N
         Γ ⊢[PRAAx] band (b.val i d-b.val j d) E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (inst2 f (rem i N) x))
      (realProjection (inst2 f (rem j N) x)) (E+two) S := by
  have ei := ZT.toZ_eq (wrapped_sample_mod (Γ := Γ) f x S i N)
  have ej := ZT.toZ_eq (wrapped_sample_mod (Γ := Γ) f x S j N)
  apply projected_distance _ _ S E hS
  exact .andI (zle_congr rfl (by simp only [ZT.toZ_sub,ei,ej]) h.andE₁)
    (zle_congr (by simp only [ZT.toZ_sub,ei,ej]) rfl h.andE₂)

def cyclicThirdLower (f : PTm 2) (x S N E : PTm n) : Fm PTm n :=
  PeriodicThirdDifferenceModulo.thirdLower (PeriodicThirdDifferenceModulo.wrapped (body f))
    (PeriodicThirdDifferenceModulo.data (data x S) N) N E

theorem cyclic_distance (f : PTm 2) (x S N E i : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (h : Γ ⊢[PRAAx] cyclicThirdLower f x S N E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (inst2 f (rem i N) x))
      (realProjection (inst2 f (rem zero N) x)) (cubicBudget N E+two) S :=
  wrapped_projected_distance f x S i zero N (cubicBudget N E) hS
    (PeriodicThirdDifferenceModulo.range _ _ N E i hN hi h)

def observationClock (N E p : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (cubicBudget N E+two) p

theorem observation_clock_budget (N E p : PTm n) :
    Γ ⊢[PRAAx] le ((cubicBudget N E+two)*unit p) (unit (observationClock N E p)) :=
  GaussianFastValueCut.query_budget _ _

theorem cyclic_dyadic_distance (f : PTm 2) (x N E i p : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (h : Γ ⊢[PRAAx] cyclicThirdLower f x (unit (observationClock N E p)) N E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (inst2 f (rem i N) x))
      (realProjection (inst2 f (rem zero N) x)) one (unit p) := by
  let S := unit (observationClock N E p)
  have hS : Γ ⊢[PRAAx] le one S := unit_positive _
  exact distance_radius_mono _ _ (cubicBudget N E+two) S one (unit p) hS (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (observation_clock_budget N E p))
    (cyclic_distance f x S N E i hS hN hi h)

theorem actual_signed_grid_projected_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let q := var 0
     let r := var 1
     let S := var 2
     let E := var 3
     le one S ⟶ band (rounded q S-rounded r S) E ⟶
       distanceBounded (realProjection q) (realProjection r) (E+two) S) :=
  closeUniv 4 (.impI (.impI (projected_distance _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSignedObservationReadback
