import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseFrozenMatrix
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetArctangentTimeRate
import IPRADerivations.Analysis.Integration.GaussianCompactRiemannSplit

/-!
# Frozen Bose observations under positive time recoding

Scaling the rational time code leaves the actual frozen real decay
observation equal. The two original arctangent observations have a
zero-leading-term comparison on that same physical time.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenTimeRescale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetSecondDecayPointwise (angle row fullDecay subst_row)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (fraction_congr)
open GaussianEulerDecayMesh (observation subst_observation observation_rescale)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data

theorem coordinates (p X Y D sign a a' b b' H J : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    row p X Y D sign a b H J ≐ row p X Y D sign a' b' H J := by
  let s (v : PTm n) := Syn.shift v
  have first : Γ ⊢[PRAAx] row p X Y D sign a b H J ≐ row p X Y D sign a' b H J := by
    simpa only [s,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (row (s p) (s X) (s Y) (s D) (s sign) (var 0) (s b) (s H) (s J)) ha
  have second : Γ ⊢[PRAAx] row p X Y D sign a' b H J ≐ row p X Y D sign a' b' H J := by
    simpa only [s,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (row (s p) (s X) (s Y) (s D) (s sign) (s a') (var 0) (s H) (s J)) hb
  exact first.eqTrans second

private theorem observation_congr (p a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx] observation a b p ≐ observation c d p := by
  simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![a,b,p]) (σ' := ![c,d,p]) (fun i => by fin_cases i; exact ha; exact hb; exact .eqRefl p)

theorem decay_rescale (p a b H J c : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hJ : Γ ⊢[PRAAx] le one J) (hc : Γ ⊢[PRAAx] le one c) : Γ ⊢[PRAAx]
    fullDecay p (c*a) (c*b) H J ≐ fullDecay p a b H J :=
  (observation_congr p (two*((c*a)*H)) ((c*b)*J) ((two*(a*H))*c) ((b*J)*c) (by ipra_ring) (by ipra_ring)).eqTrans
    (observation_rescale (two*(a*H)) (b*J) c p (positive_product _ _ hb hJ) hc)

theorem rescale_error (p X Y D sign a b c d H J T : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) (hJ : Γ ⊢[PRAAx] le one J) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (row p X Y D sign (c*a) (c*b) H J) (row p X Y D sign (d*a) (d*b) H J) (num 4) (unit p) := by
  let x := atanData X Y D sign (c*a) (c*b)
  let y := atanData X Y D sign (d*a) (d*b)
  let u := angle p X Y D sign (c*a) (c*b)
  let v := angle p X Y D sign (d*a) (d*b)
  let w := fullDecay p a b H J
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have hcb := positive_product _ _ hc hb
  have hdb := positive_product _ _ hd hb
  have hu := GaussianCompactRiemannSplit.fraction_cancel c a b hc hb
  have hv := GaussianCompactRiemannSplit.fraction_cancel d a b hd hb
  have hT : Γ ⊢[PRAAx] le (d*a) (T*(d*b)) :=
    le_congr (mul_comm a d) (by ipra_ring) (mul_le_mul_right d ht)
  have less := distance_congr hu.eqSymm hv.eqSymm (.eqRefl zero) (.eqRefl one)
    (GaussianRationalPowerDifference.distance_refl_zero (fraction a b) one (le_refl one))
  have raw := rate_at Atan Atan x y (GaussianBinetArctangentTimeRate.gain D T*zero) one p p
    (GaussianBinetArctangentTimeRate.independent_rate X Y D sign (c*a) (c*b) (d*a) (d*b) T zero one
      hz hcb hdb hT (le_refl one) less)
  have angleNear : Γ ⊢[PRAAx] distanceBounded u v two U :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive one p p (le_refl one)) hp
      (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)) raw
  have wBound : Γ ⊢[PRAAx] bounded w two one :=
    bounded_radius_mono _ _ _ _ _ hp (le_refl one) (by ipra_le sl hp)
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound p (two*(a*H)) (b*J) (positive_product _ _ hb hJ))
  have product := GaussianApproximateInverseDistance.multiply_distance w u v two two U hp wBound angleNear
  have first := (qmul_congr (.eqRefl u) (decay_rescale p a b H J c hb hJ hc)).eqTrans (qmul_commutative u w)
  have second := (qmul_congr (.eqRefl v) (decay_rescale p a b H J d hb hJ hd)).eqTrans (qmul_commutative v w)
  exact distance_congr first.eqSymm second.eqSymm (by ipra_ring) (.eqRefl _) product

end LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenTimeRescale
