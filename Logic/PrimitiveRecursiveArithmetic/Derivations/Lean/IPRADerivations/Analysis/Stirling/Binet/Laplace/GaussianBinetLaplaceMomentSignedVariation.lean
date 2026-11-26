import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentVariation
import IPRADerivations.Analysis.Names.GaussianNamedRightHalfPlaneSigned
import IPRADerivations.Analysis.Names.GaussianLinearDistanceName

/-!
# Variation between actual positive real projections of signed samples

A certified right half-plane sample has a positive rational real part.
Its exact real numerator and denominator select the original real
moment evaluator. The Gaussian distance controls the displacement of
these real parts, so the moment gain is uniform in both raw denominators.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentSignedVariation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentImproper (nameF data regular)
open GaussianBinetLaplaceMomentVariation (gain ordered_observations)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianNamedRightHalfPlaneSigned (certificate point realNumerator imagNumerator denominator sign)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianRationalHorner (ofGaussian_represents scalar_congr positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num monus)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

def pointData (j q : PTm n) : PTm n :=
  data j (realNumerator q) (denominator q) (radius (realNumerator q) zero)

@[simp] theorem subst_pointData {m : ℕ} (σ : Fin n → PTm m) (j q : PTm n) :
    Syn.subst σ (pointData j q) = pointData (Syn.subst σ j) (Syn.subst σ q) := by
  simp [pointData]

theorem projected_source (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] realSource (realNumerator q) zero (denominator q) zero (radius (realNumerator q) zero) :=
  source_of_right_half_plane _ _ _ _
    (.andI (.andI h.andE₁.andE₁.andE₁.andE₁ (.orI₁ (.eqRefl zero))) h.andE₁.andE₁.andE₂)

theorem real_representation (q : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (point q)) (ZT.ofNat (realNumerator q)) (denominator q) := by
  let w := native (realNumerator q) (imagNumerator q) (sign q)
  have hD := GaussianRationalL1.raw_den_positive (Γ := Γ) q
  apply scalar_congr (.eqRefl _) _ (.eqRefl _) (ofGaussian_represents w (denominator q) hD).andE₁
  apply ZT.derive
  simp only [w,native,ComplexLogarithmRemainder.eval_re_code]

private theorem ordered_signed_observations (p j x y R K A B : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (hxy : Γ ⊢[PRAAx] le (realNumerator x*denominator y) (realNumerator y*denominator x))
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (pointData j y)) (ap2 nameF p (pointData j x))
      (diagonalNumerator (gain j K*A) B (num 12) p) (diagonalDenominator B p) := by
  let X := realNumerator x
  let Y := realNumerator y
  let D := denominator x
  let E := denominator y
  let Q := D*E
  let H := monus (Y*D) (X*E)
  have hD := hx.andE₁.andE₁.andE₂
  have hE := hy.andE₁.andE₁.andE₂
  have hQ : Γ ⊢[PRAAx] le one Q := positive_product _ _ hD hE
  have hp := unit_positive (Γ := Γ) p
  have r := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ A B hB
    (distance_symmetric _ _ _ _ hB near)
  have raw := GaussianLinearDistanceName.upper_to_cleared (fstT (point y)) (fstT (point x)) Y E X D A B
    (real_representation y) (real_representation x) (RationalValueBounds.upper_of_radius _ _ _ _ r)
  have gap : Γ ⊢[PRAAx] X*E+H ≐ Y*D := (eq_add_of_le hxy).eqSymm
  have compare : Γ ⊢[PRAAx] le (B*H) (A*Q) := by
    apply le_of_add_le_add_right (c := B*(X*E))
    have ea : Γ ⊢[PRAAx] B*D*Y ≐ B*H+B*(X*E) :=
      (by ipra_ring : Γ ⊢[PRAAx] B*D*Y ≐ B*(Y*D)).eqTrans
        ((congrMul (.eqRefl B) gap.eqSymm).eqTrans (by ipra_ring))
    exact le_congr ea (by dsimp only [Q]; ipra_ring) raw
  have smaller : Γ ⊢[PRAAx] le H Q :=
    RationalValueBounds.positive_cancel hB (le_trans compare (le_mul_mono hA (le_refl Q)))
  have enc : Γ ⊢[PRAAx] (X*Q+H*D)*E ≐ Y*(D*Q) := by
    have e := natEq gap
    apply deriveNat
    dsimp only [Q]
    ipra_simps
    linear_combination 𝔞(D)*𝔞(E)*e
  have secant := ordered_observations p j X D (radius X zero) Y E (radius Y zero) K H Q
    (.andI (.andI (projected_source x R K hx) (projected_source y R K hy))
      (.andI (.andI hK hx.andE₂.andE₁) (.andI hQ (.andI smaller enc))))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hQ hp) (positive_product _ _ hB hp)
    (by
      unfold diagonalNumerator diagonalDenominator
      dsimp only [Q] at compare ⊢
      ipra_le 𝔞(gain j K)*𝔞(unit p)*𝔞(unit p)*sl compare)
    secant

theorem signed_observations (p j x y R K A B : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (pointData j x)) (ap2 nameF p (pointData j y))
      (diagonalNumerator (gain j K*A) B (num 12) p) (diagonalDenominator B p) := by
  refine (le_total (realNumerator x*denominator y) (realNumerator y*denominator x)).orE ?_ ?_
  · exact distance_symmetric _ _ _ _ (positive_product _ _ hB.wk (unit_positive p))
      (ordered_signed_observations p j x y R K A B hx.wk hy.wk hK.wk hB.wk hA.wk Prf.hyp0 near.wk)
  · exact ordered_signed_observations p j y x R K A B hy.wk hx.wk hK.wk hB.wk hA.wk Prf.hyp0
      (distance_symmetric _ _ _ _ hB.wk near.wk)

theorem signed_rate (j x y R K A B : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) A B) :
    Γ ⊢[PRAAx] independentRate nameF nameF (pointData j x) (pointData j y) (gain j K*A) B := by
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF (pointData j x) (pointData j y)
    (gain j K*A) B (num 12) hB (regular _ _ _ _ (projected_source x R K hx))
    (regular _ _ _ _ (projected_source y R K hy))
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have xs : Δ ⊢[PRAAx] certificate (s x) (s R) (s K) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianNamedRightHalfPlaneSigned.subst_certificate] using hx.shift
  have ys : Δ ⊢[PRAAx] certificate (s y) (s R) (s K) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianNamedRightHalfPlaneSigned.subst_certificate] using hy.shift
  have ks : Δ ⊢[PRAAx] le one (s K) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hK.shift
  have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift
  have a : Δ ⊢[PRAAx] le (s A) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hA.shift
  have close : Δ ⊢[PRAAx] distanceBounded (point (s x)) (point (s y)) (s A) (s B) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianRationalMetric.subst_distanceBounded,
      GaussianNamedRightHalfPlaneSigned.subst_point] using near.shift
  change Δ ⊢[PRAAx] distanceBounded (ap2 nameF (var 0) (Syn.shift (pointData j x)))
    (ap2 nameF (var 0) (Syn.shift (pointData j y)))
    (diagonalNumerator (Syn.shift (gain j K*A)) (s B) (Syn.shift (num 12)) (var 0))
    (diagonalDenominator (s B) (var 0))
  rw [show Syn.shift (pointData j x) = pointData (s j) (s x) from subst_pointData _ _ _,
    show Syn.shift (pointData j y) = pointData (s j) (s y) from subst_pointData _ _ _,
    show Syn.shift (gain j K*A) = gain (s j) (s K)*s A by
      simp only [Syn.shift,s,GaussianBinetLaplaceMomentVariation.subst_gain,PTm.subst_mul],
    show Syn.shift (num 12 : PTm n) = num 12 by simp only [Syn.shift,PTm.subst_num]]
  exact signed_observations (var 0) (s j) (s x) (s y) (s R) (s K) (s A) (s B) xs ys ks bs a close

theorem actual_improper_Binet_moment_signed_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let j := var 0
     let x := var 1
     let y := var 2
     let R := var 3
     let K := var 4
     let A := var 5
     let B := var 6
     (certificate x R K ⋏ certificate y R K) ⟶ (le one K ⋏ (le one B ⋏ le A B)) ⟶
       distanceBounded (point x) (point y) A B ⟶
       independentRate nameF nameF (pointData j x) (pointData j y) (gain j K*A) B) :=
  closeUniv 7 (.impI (.impI (.impI (signed_rate _ _ _ _ _ _ _ hyp2.andE₁ hyp2.andE₂
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentSignedVariation
