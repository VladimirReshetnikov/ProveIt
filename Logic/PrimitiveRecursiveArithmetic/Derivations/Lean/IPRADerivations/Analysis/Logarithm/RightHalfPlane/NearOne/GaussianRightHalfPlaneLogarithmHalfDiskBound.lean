import IPRADerivations.Analysis.Logarithm.RightHalfPlane.NearOne.GaussianRightHalfPlaneLogarithmMercatorHalfDisk
import IPRADerivations.Analysis.Logarithm.PositiveAxis.Bounds.GaussianPositiveRationalLogarithmFactorFourBound
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualRadius

/-!
# Admit the entire radius-one-half disk to the canonical logarithm bound

Its real numerator is between half and three halves of the denominator,
and its imaginary numerator is at most half the denominator. Bound the
radial part by one using the actual positive harmonic logarithm. The
original arctangent sampler also has norm at most one on this disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmHalfDiskBound

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq normSq_eval oneCode scale)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianRationalHorner (ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (bounded_sum bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithmMercatorHalfDisk (source lateLogBound)
open GaussianRightHalfPlaneLogarithmOffset (offset)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "absGap" => Probability.Variance.ad
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "radialF" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "phaseF" => GaussianRightHalfPlaneArgument.nameF
local notation "halfPoint" => GaussianEulerSquareFactorInverse.half

private theorem offset_norm (A B D neg : PTm n)
    (h : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] normSq (offset A B D neg) ≐ absGap A D*absGap A D+B*B := by
  have real := natEq (Probability.Variance.ad_sq (Γ := Γ) A D)
  have eq : Γ ⊢[PRAAx] normSq (offset A B D neg) ≐ absGap A D*absGap A D+normSq (native zero B neg) := by
    apply deriveNat
    rw [normSq_eval,IPRA.Q.mk_add,map_add,normSq_eval]
    simp only [offset,GaussianLogGammaEulerResidualDomain.native,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat]
    simp only [IPRA.Q.mk_add,IPRA.Q.mk_mul,map_add,map_mul] at real
    ipra_simps
    linear_combination -real
  exact eq.eqTrans (congrAdd (.eqRefl _)
    ((GaussianLogGammaEulerResidualRadius.native_norm zero B neg h).eqTrans (by ipra_ring)))

private theorem box (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] le D (two*A) ⋏ (le (two*A) (num 3*D) ⋏ le (two*B) D) := by
  have hb : Γ ⊢[PRAAx] le (absGap A D*absGap A D+B*B) (R*R) :=
    le_congr (offset_norm A B D neg h.andE₁.andE₁.andE₂) (.eqRefl _) h.andE₂.andE₁
  have u := nat_sqrt_mono (le_trans (le_add_right (absGap A D*absGap A D) (B*B)) hb)
  have v := nat_sqrt_mono (le_trans (le_add_left (B*B) (absGap A D*absGap A D)) hb)
  have e : Γ ⊢[PRAAx] absGap D A ≐ absGap A D := by unfold Probability.Variance.ad; exact add_comm _ _
  have a := Probability.MedianWeighted.le_add_ad (Γ := Γ) A D
  have d := le_congr (.eqRefl _) (congrAdd (.eqRefl A) e) (Probability.MedianWeighted.le_add_ad D A)
  exact .andI (by ipra_le 2*sl d+2*sl u+sl h.andE₂.andE₂)
    (.andI (by ipra_le 2*sl a+2*sl u+sl h.andE₂.andE₂)
      (le_trans (le_mul_mono (le_refl two) v) h.andE₂.andE₂))

private theorem norm_range (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] le (normNum A B) (num 4*normDen D) ⋏ le (normDen D) (num 4*normNum A B) := by
  have hQ := box A B D neg R h
  have a := le_mul_mono hQ.andE₂.andE₁ hQ.andE₂.andE₁
  have b := le_mul_mono hQ.andE₂.andE₂ hQ.andE₂.andE₂
  have lower := le_mul_mono hQ.andE₁ hQ.andE₁
  have h4 : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  refine .andI (RationalValueBounds.positive_cancel h4 ?_) ?_
  · unfold normNum normDen
    ipra_le sl a+sl b+6*(Groth.ι (IPRA.Q.mk Γ D))^2
  · unfold normNum normDen
    ipra_le sl lower+4*(Groth.ι (IPRA.Q.mk Γ B))^2

private theorem half_bound : Γ ⊢[PRAAx] bounded (halfPoint : PTm n) one two := by
  let z : PTm n := scale one oneCode
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hn : Γ ⊢[PRAAx] normSq z ≐ one :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  apply bounded_of_cleared _ z two one two ht ht (ofGaussian_represents z two ht)
  exact le_congr
    ((by ipra_ring : Γ ⊢[PRAAx] two*two ≐ (two*two)*one).eqTrans (congrMul (.eqRefl _) hn.eqSymm))
    (by ipra_ring) (le_refl (two*two))

private theorem radial_bound (p A B D neg R : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hp : Γ ⊢[PRAAx] le (num 5) p) :
    Γ ⊢[PRAAx] bounded (ap2 radialF p (GaussianRightHalfPlaneRadialLogarithm.data A B D)) one one := by
  let logF := GaussianPositiveRationalLogarithm.logF
  let x := GaussianPositiveRationalLogarithm.data (normNum A B) (normDen D)
  let j := GaussianNamedBoundedProductObservation.clock constantF logF p halfPoint x
  have k : Γ ⊢[PRAAx] le p j := le_add_right _ _
  have g := norm_range A B D neg R h
  have hs := GaussianRightHalfPlaneRadialLogarithm.log_source A B D h.andE₁.andE₁.andE₁ h.andE₁.andE₂
  have boundedLog := GaussianPositiveRationalLogarithmFactorFourBound.sample_bound j (normNum A B) (normDen D)
    hs g.andE₁ g.andE₂ (le_trans hp k)
  have eq := (GaussianNamedBoundedProductObservation.name_at (Γ := Γ) constantF logF p halfPoint x).eqTrans
    (qmul_congr (constant_at j halfPoint) (.eqRefl _))
  have product := bounded_product halfPoint (ap2 logF j x) one two two one (le_succ_self one)
    (le_refl one) half_bound boundedLog
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_succ_self one) (le_refl one)) (le_refl one)
    (le_of_eq_add (d := zero) (by ipra_ring)) (bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) product)

theorem sample_bound (p A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hp : Γ ⊢[PRAAx] le (num 5) p) :
    Γ ⊢[PRAAx] bounded (ap2 L p (GaussianRightHalfPlaneLogarithm.data A B D neg)) two one := by
  let j := GaussianFastValueCut.exponent two p
  let x := GaussianRightHalfPlaneRadialLogarithm.data A B D
  let y := GaussianRightHalfPlaneArgument.data A B neg
  have bp := box A B D neg R h
  have bA : Γ ⊢[PRAAx] le B A := RationalValueBounds.positive_cancel (le_succ_self one)
    (le_trans bp.andE₂.andE₂ bp.andE₁)
  have phase := GaussianRightHalfPlaneArgumentLocalBound.sample_bound j A B neg h.andE₁.andE₁.andE₁ bA h.andE₁.andE₁.andE₂
  have upper : Γ ⊢[PRAAx] bounded (ap2 phaseF j y) one one :=
    bounded_radius_mono _ _ _ _ _ h.andE₁.andE₁.andE₁ (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) bA) phase
  have r := radial_bound j A B D neg R h (le_trans hp (le_add_right _ _))
  exact bound_congr (GaussianExponentialReference.add_sample radialF phaseF x y p).eqSymm
    (succ_eq_add_one one).eqSymm (.eqRefl _) (GaussianRationalPowerDifference.bounded_sum_one r upper)

/-- The same canonical logarithm and same Mercator name coincide on the
original native half disk, including its boundary. -/
theorem coincidence (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent L GaussianLocalLogarithmName.pointF
      (GaussianRightHalfPlaneLogarithm.data A B D neg) (GaussianLocalLogarithmName.data (offset A B D neg) R D) := by
  refine GaussianRightHalfPlaneLogarithmMercatorHalfDisk.coincidence A B D neg R (num 5) h (.allI (.impI ?_))
  let sh (a : PTm n) := Syn.shift a
  let Δ := le (num 5) (var 0) :: Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh R) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  simpa only [lateLogBound,Syn.shift,LeanProofs.IPRA.PTm.subst_num,sh,Δ] using
    sample_bound (var 0) (sh A) (sh B) (sh D) (sh neg) (sh R) h' Prf.hyp0

theorem actual_canonical_logarithm_matches_Mercator_half_disk_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        GaussianNameEquivalence.crossEquivalent L GaussianLocalLogarithmName.pointF
          (GaussianRightHalfPlaneLogarithm.data (var 0) (var 1) (var 2) (var 3))
          (GaussianLocalLogarithmName.data (offset (var 0) (var 1) (var 2) (var 3)) (var 4) (var 2))) :=
  closeUniv 5 (.impI (coincidence _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmHalfDiskBound
