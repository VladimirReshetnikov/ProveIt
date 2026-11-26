import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicParameterTaylor
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerPowerCoefficients

/-!
# Actual finite native parameter paths inside the right half-plane

The path numerator is (D*n)z+(B*i)h and its denominator is B*D*n.
The original disk and margin, and the genuine bound |h/D|<=1/(4A),
give radius R+1 and margin 1/(2A) at every i<=n. Exact endpoint and
successor fractions concern the original canonical rational operations;
no equality of raw Gaussian codes or path output guards is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativeParameterPath

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale add neg normSq re im)
open GaussianRationalHorner (ofGaussian qadd positive_product canonical_unique represents_congr)
open GaussianRationalMetric (bounded bounded_to_cleared bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEulerLowerPowerCoefficients (realLower)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def numerator (z B h D N i : PTm n) : PTm n := add (scale (D*N) z) (scale (B*i) h)
def denominator (B D N : PTm n) : PTm n := B*D*N
def point (z B h D N i : PTm n) : PTm n := ofGaussian (numerator z B h D N i) (denominator B D N)
def increment (h D N : PTm n) : PTm n := ofGaussian h (D*N)
def source (z R B A h D : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    (le one D ⋏ bounded (ofGaussian h D) one (num 4*A))

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (z B h D N i : PTm n) :
    Syn.subst σ (numerator z B h D N i) = numerator (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ h)
      (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ i) := by simp [numerator,add,scale]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (B D N : PTm n) :
    Syn.subst σ (denominator B D N) = denominator (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ N) := by simp [denominator]
@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (z B h D N i : PTm n) :
    Syn.subst σ (point z B h D N i) = point (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ h)
      (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ i) := by simp [point]
@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (h D N : PTm n) :
    Syn.subst σ (increment h D N) = increment (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N) := by simp [increment]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A h D : PTm n) :
    (source z R B A h D).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) := by simp [source]

theorem denominator_positive (B D N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (denominator B D N) :=
  positive_product _ _ (positive_product _ _ hB hD) hN

private theorem scale_bound (g S C : PTm n) (h : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded g S) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (scale C g) (C*S) := by
  have raw := mul_le_mul_right (C*C) h
  exact le_congr ((mul_comm _ _).eqTrans (ComplexLogarithmRemainder.normSq_scale C g).eqSymm) (by ipra_ring) raw

theorem half_increment_disk (z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (scale (two*A) h) D := by
  have h2 := positive_product _ _ (le_succ_self one) hs.andE₁.andE₁
  have h4 := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (num 4)) hs.andE₁.andE₁
  have bound : Γ ⊢[PRAAx] bounded (ofGaussian h D) one (two*A) :=
    bounded_radius_mono _ _ _ _ _ h4 h2 (le_of_eq_add (d := two*A) (by ipra_ring)) hs.andE₂.andE₂
  have clear := bounded_to_cleared _ _ D one (two*A) hs.andE₂.andE₁ h2
    (GaussianRationalHorner.ofGaussian_represents h D hs.andE₂.andE₁) bound
  exact le_congr (ComplexLogarithmRemainder.normSq_scale (two*A) h).eqSymm (by ipra_ring) clear

theorem increment_native_disk (z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded h D := by
  have h2 := positive_product _ _ (le_succ_self one) hs.andE₁.andE₁
  have h4 := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (num 4)) hs.andE₁.andE₁
  have bound : Γ ⊢[PRAAx] bounded (ofGaussian h D) one one :=
    bounded_radius_mono _ _ _ _ _ h4 (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) h4) hs.andE₂.andE₂
  have clear := bounded_to_cleared _ _ D one one hs.andE₂.andE₁ (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents h D hs.andE₂.andE₁) bound
  exact le_congr (by ipra_ring) (by ipra_ring) clear

theorem path_disk (z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (numerator z B h D N i) ((R+one)*denominator B D N) := by
  have first := scale_bound z (R*B) (D*N) hs.andE₁.andE₂.andE₁.andE₂
  have second := scale_bound h D (B*i) (increment_native_disk z R B A h D hs)
  have sum := ComplexLogarithmRemainder.bounded_add first second
  have larger := add_le_add₂ (le_refl ((D*N)*(R*B))) (mul_le_mul_right (B*D) hi)
  have grow : Γ ⊢[PRAAx] le ((D*N)*(R*B)+(B*i)*D) ((R+one)*denominator B D N) :=
    le_congr (by ipra_ring) (by unfold denominator; ipra_ring) larger
  exact le_trans sum (sq_le_sq grow)

theorem path_margin (z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    realLower (numerator z B h D N i) (two*A) (denominator B D N) := by
  let u := ZT.ofNat B
  let v := ZT.ofNat A*re z
  let baseGap := monus (v.pos+u.neg) (u.pos+v.neg)
  have base : ZT.toZ Γ u+𝔞(baseGap) = ZT.toZ Γ v := zle_toZ hs.andE₁.andE₂.andE₂
  let w := re (ComplexLogarithmRemainder.neg (scale (two*A) h))
  let d := ZT.ofNat D
  let shiftGap := monus (d.pos+w.neg) (w.pos+d.neg)
  have signed := GaussianEulerUpperPowerCoefficients.native_real_upper (ComplexLogarithmRemainder.neg (scale (two*A) h)) D
    (ComplexLogarithmRemainder.bounded_neg (half_increment_disk z R B A h D hs))
  have step : ZT.toZ Γ w+𝔞(shiftGap) = ZT.toZ Γ d := zle_toZ signed
  have rest := natEq (eq_add_of_le hi)
  apply zle_of_toZ (two*(D*N)*baseGap+B*(D*monus N i+i*shiftGap))
  dsimp only [u,v,w,d] at base step
  simp only [ZT.toZ_ofNat,ZT.toZ_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale] at base step
  simp only [numerator,denominator,ZT.toZ_ofNat,ZT.toZ_mul,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale]
  ipra_simps
  linear_combination (2*𝔞 D*𝔞 N)*base+(𝔞 B*𝔞 i)*step-(𝔞 B*𝔞 D)*rest

theorem path_source (z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.source (numerator z B h D N i) (R+one) (denominator B D N) (two*A) :=
  .andI (positive_product _ _ (le_succ_self one) hs.andE₁.andE₁)
    (.andI (.andI (denominator_positive B D N hs.andE₁.andE₂.andE₁.andE₁ hs.andE₂.andE₁ hN)
      (path_disk z R B A h D N i hs hi)) (path_margin z R B A h D N i hs hi))

theorem point_zero (z B h D N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    point z B h D N zero ≐ ofGaussian z B := by
  have den := denominator_positive B D N hB hD hN
  have right := GaussianRationalSyntheticDivision.rescale_to _ _ _ (D*N) (denominator B D N)
    (GaussianRationalHorner.ofGaussian_represents z B hB) (by unfold denominator; ipra_ring)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ den)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hB) den (hrv := right)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents _ _ den)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [numerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

theorem point_last (z B h D N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    point z B h D N N ≐ ofGaussian (GaussianEulerParameterExponentialIncrement.shifted z B h D) (B*D) := by
  have den := denominator_positive B D N hB hD hN
  have bd := positive_product _ _ hB hD
  have right := GaussianRationalHorner.represents_rescale _ _ _ N
    (GaussianRationalHorner.ofGaussian_represents (GaussianEulerParameterExponentialIncrement.shifted z B h D) (B*D) bd)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ den)
    (GaussianRationalHorner.ofGaussian_canonical _ _ bd) den (hrv := right)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents _ _ den)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [numerator,GaussianEulerParameterExponentialIncrement.shifted,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

theorem point_succ (z B h D N i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    point z B h D N (succ i) ≐ qadd (point z B h D N i) (increment h D N) := by
  have den := denominator_positive B D N hB hD hN
  have dn := positive_product _ _ hD hN
  have left := GaussianRationalHorner.ofGaussian_represents (numerator z B h D N (succ i)) (denominator B D N) den
  have current := GaussianRationalHorner.ofGaussian_represents (numerator z B h D N i) (denominator B D N) den
  have step := GaussianRationalSyntheticDivision.rescale_to _ _ _ B (denominator B D N)
    (GaussianRationalHorner.ofGaussian_represents h (D*N) dn) (by unfold denominator; ipra_ring)
  have right := GaussianRationalHorner.qadd_represents _ _ _ _ _ den current step
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ den)
    (GaussianRationalHorner.qadd_canonical _ _) den (hrv := right)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) left
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [numerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

theorem increment_bound (h D N X Y : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N)
    (hY : Γ ⊢[PRAAx] le one Y) (hh : Γ ⊢[PRAAx] bounded (ofGaussian h D) X Y) : Γ ⊢[PRAAx]
    bounded (increment h D N) X (Y*N) := by
  have dn := positive_product _ _ hD hN
  have yn := positive_product _ _ hY hN
  have clear := bounded_to_cleared _ _ D X Y hD hY (GaussianRationalHorner.ofGaussian_represents h D hD) hh
  apply bounded_of_cleared _ _ (D*N) X (Y*N) dn yn (GaussianRationalHorner.ofGaussian_represents h (D*N) dn)
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (N*N) clear)

theorem point_split (z B h D N i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    point z B h D N i ≐ qadd (ofGaussian z B) (ofGaussian (scale i h) (D*N)) := by
  have den := denominator_positive B D N hB hD hN
  have dn := positive_product _ _ hD hN
  have first := GaussianRationalSyntheticDivision.rescale_to _ _ _ (D*N) (denominator B D N)
    (GaussianRationalHorner.ofGaussian_represents z B hB) (by unfold denominator; ipra_ring)
  have second := GaussianRationalSyntheticDivision.rescale_to _ _ _ B (denominator B D N)
    (GaussianRationalHorner.ofGaussian_represents (scale i h) (D*N) dn) (by unfold denominator; ipra_ring)
  have right := GaussianRationalHorner.qadd_represents _ _ _ _ _ den first second
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ den)
    (GaussianRationalHorner.qadd_canonical _ _) den (hrv := right)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents _ _ den)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [numerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

theorem point_distance (z B h D N i X Y : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) (hY : Γ ⊢[PRAAx] le one Y)
    (hi : Γ ⊢[PRAAx] le i N) (hh : Γ ⊢[PRAAx] bounded (ofGaussian h D) X Y) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (point z B h D N i) (ofGaussian z B) X Y := by
  have dn := positive_product _ _ hD hN
  have clear := bounded_to_cleared _ _ D X Y hD hY (GaussianRationalHorner.ofGaussian_represents h D hD) hh
  have scaled : Γ ⊢[PRAAx] bounded (ofGaussian (scale i h) (D*N)) X Y := by
    apply bounded_of_cleared _ _ (D*N) X Y dn hY (GaussianRationalHorner.ofGaussian_represents _ _ dn)
    have norm := natEq (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) i h)
    ipra_le (𝔞 i)^2*sl clear+(𝔞 X)^2*(𝔞 D)^2*sl (sq_le_sq hi) using rw [norm]; ring
  exact bound_congr ((GaussianRationalSyntheticDivision.qadd_sub_cancel (ofGaussian z B) _
    (GaussianRationalHorner.ofGaussian_canonical _ _ dn)).eqSymm.eqTrans
      (GaussianRationalSyntheticDivision.qsub_congr (point_split z B h D N i hB hD hN).eqSymm (.eqRefl _)))
    (.eqRefl _) (.eqRefl _) scaled

theorem point_difference (z B h D N i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (point z B h D N (succ i)) (point z B h D N i) ≐ increment h D N :=
  (GaussianRationalSyntheticDivision.qsub_congr (point_succ z B h D N i hB hD hN) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _
      (GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ hD hN)))

theorem local_step_fraction (z B h D N i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    ofGaussian (GaussianEulerParameterExponentialIncrement.shifted (numerator z B h D N i) (denominator B D N) h (D*N))
      (denominator B D N*(D*N)) ≐ point z B h D N (succ i) :=
  (GaussianEulerLogarithmicParameterTaylor.encoded_sum _ _ _ _ (denominator_positive B D N hB hD hN)
    (positive_product _ _ hD hN)).eqTrans (point_succ z B h D N i hB hD hN).eqSymm

theorem actual_native_derivative_parameter_path_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏ (le one (var 6) ⋏ le (var 7) (var 6))) ⟶
      GaussianEulerLowerPowerCoefficients.source (numerator (var 0) (var 2) (var 4) (var 5) (var 6) (var 7))
        (var 1+one) (denominator (var 2) (var 5) (var 6)) (two*var 3)) :=
  closeUniv 8 (.impI (path_source _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_native_derivative_parameter_path_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 1) ⋏ (le one (var 3) ⋏ le one (var 4))) ⟶
      (point (var 0) (var 1) (var 2) (var 3) (var 4) zero ≐ ofGaussian (var 0) (var 1) ⋏
       point (var 0) (var 1) (var 2) (var 3) (var 4) (var 4) ≐
         ofGaussian (GaussianEulerParameterExponentialIncrement.shifted (var 0) (var 1) (var 2) (var 3)) (var 1*var 3))) :=
  closeUniv 5 (.impI (.andI (point_zero _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (point_last _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

theorem actual_native_derivative_parameter_path_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ (le one (var 3) ⋏ le one (var 4))) ⟶
      point (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) ≐
        qadd (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (increment (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (point_succ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativeParameterPath
