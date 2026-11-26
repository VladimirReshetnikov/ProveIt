import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalPositiveHeadLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalPositiveFirstDerivativeRow
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmSignedIncrement
import IPRADerivations.Analysis.Series.SignedTelescope

/-!
# Linear estimate for a literal kept positive Barnes logarithm row

The original weighted logarithm evaluates k·Log((A+(k−1)B)/(kB)).
Its original normalized increment has linear term equal to the physical
step times the reciprocal of the original Barnes base. Rounding costs
are uniform on a fixed finite head, with each row keeping its clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Common (mul_le_mul le_of_sq_le add_le_add)
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open ComplexLogarithmRemainder (bounded normSq)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalDerivativeRow (offset)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (source step base_lower)
open GaussianBarnesCanonicalThirdLogarithmRows (base_at center shiftedNumerator shifted_positive)
open GaussianBarnesCanonicalPositiveHeadLogarithm (rowData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusNumerator radiusPoint radius_represents)
open GaussianHarmonicIntegerExponential (originalExponentF)
open GaussianPositiveRationalLogarithm (data fraction logF)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (canonical canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents
  qmul positive_product represents_congr)
open GaussianRationalMetric (distanceBounded qsub qsub_canonical)
open GaussianRationalNaturalScale (naturalPoint natScale_as_product)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone reciprocal reciprocal_canonical reciprocal_identity)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRootAlgebra (equal equal_of_values sub)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "clock" => GaussianNaturalScaleProductName.clock logF

def rowLinear (A C B i : PTm n) : PTm n :=
  qmul (ofGaussian (step A C) B) (reciprocal (base (center A B) B (succ i)))

def numerator (K H : PTm n) : PTm n := two*((K*H)*(K*H))

@[simp] theorem subst_rowLinear {m : ℕ} (σ : Fin n → PTm m) (A C B i : PTm n) :
    Syn.subst σ (rowLinear A C B i) = rowLinear (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ i) :=
  by simp [rowLinear]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (K H : PTm n) :
    Syn.subst σ (numerator K H) = numerator (Syn.subst σ K) (Syn.subst σ H) := by simp [numerator,two,one]

theorem native_norm (A C : PTm n) : Γ ⊢[PRAAx] normSq (step A C) ≐ ad A C*ad A C := by
  have e := natEq (ad_sq (Γ := Γ) A C)
  apply deriveNat
  unfold step
  rw [ComplexLogarithmRemainder.normSq_code]
  simp only [ZT.toZ_ofNat,ZT.toZ_sub]
  ipra_simps
  linear_combination -e

theorem row_shift_bound (A C B H i : PTm n) (h : Γ ⊢[PRAAx] bounded (step A C) H) :
    Γ ⊢[PRAAx] le (ad (shiftedNumerator A B i) (shiftedNumerator C B i)) H := by
  have eq : Γ ⊢[PRAAx] ad (shiftedNumerator A B i) (shiftedNumerator C B i) ≐ ad A C :=
    LeanProofs.IPRA.Analysis.SignedTelescope.ad_eq_of_cross (by unfold shiftedNumerator; ipra_ring)
  exact le_congr eq.eqSymm (.eqRefl _) (le_of_sq_le (le_congr (native_norm A C) (.eqRefl _) h))

theorem row_margin (A B K i : PTm n) (hK : Γ ⊢[PRAAx] le one K) (hA : Γ ⊢[PRAAx] le B (K*A)) :
    Γ ⊢[PRAAx] le (B*succ i) (K*shiftedNumerator A B i) := by
  have grow : Γ ⊢[PRAAx] le (i*B) (K*(i*B)) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul hK (le_refl (i*B)))
  exact le_congr (by ipra_ring) (by unfold shiftedNumerator; ipra_ring) (add_le_add hA grow)

private theorem scaled_argument (A C B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    let D := B*succ i
    Γ ⊢[PRAAx] qsub (fraction (shiftedNumerator C B i) D) (fraction (shiftedNumerator A B i) D) ≐
      offset (step A C) B (succ i) := by
  let a := shiftedNumerator A B i
  let c := shiftedNumerator C B i
  let D := B*succ i
  let h := step A C
  have hD := positive_product B (succ i) hB (zero_lt_succ i)
  have ea := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) a D hD
  have ec := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) c D hD
  have same : Γ ⊢[PRAAx] equal (sub (radiusNumerator c) (radiusNumerator a)) h := by
    apply equal_of_values <;> simp only [a,c,h,radiusNumerator,step,shiftedNumerator,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,ZT.toZ_sub] <;> (try ipra_simps) <;> ring
  have raw := GaussianRationalMetric.qsub_represents (Γ := Γ) (radiusPoint c D) (radiusPoint a D)
    (radiusNumerator c) (radiusNumerator a) D hD (radius_represents c D hD) (radius_represents a D hD)
  exact (qsub_congr ec ea).eqTrans
    (canonical_unique _ _ h D (qsub_canonical _ _) (ofGaussian_canonical _ _ hD) hD
      (represents_congr (.eqRefl _) same (.eqRefl _) raw) (ofGaussian_represents h D hD))

private theorem inverse_at (A B K i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hK : Γ ⊢[PRAAx] le one K) (hM : Γ ⊢[PRAAx] le B (K*A)) :
    Γ ⊢[PRAAx] fraction (B*succ i) (shiftedNumerator A B i) ≐ reciprocal (base (center A B) B (succ i)) := by
  let a := shiftedNumerator A B i
  let D := B*succ i
  let b := base (center A B) B (succ i)
  have ha := shifted_positive A B i hA
  have hD := positive_product B (succ i) hB (zero_lt_succ i)
  have h := base_lower A B i K hB hK hM
  have hn := GaussianNameReciprocal.lower_norm_positive b K hK h
  have e := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) D a ha
  have f : Γ ⊢[PRAAx] qmul b (fraction D a) ≐ qone :=
    (qmul_congr (base_at A B i hB) e).eqTrans
      ((qmul_commutative _ _).eqTrans (GaussianRationalTravelScaling.inverse_radius a D ha hD))
  exact GaussianEulerBetaProductPascal.inverse_unique _ _ _ (ofGaussian_canonical _ _ ha) (reciprocal_canonical _)
    f (reciprocal_identity b hn)

theorem linear_at (A C B H K i : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    let D := B*succ i
    Γ ⊢[PRAAx] qmul (naturalPoint (succ i))
      (GaussianPositiveRationalLogarithmSignedIncrement.linear (shiftedNumerator A B i) D (shiftedNumerator C B i) D) ≐
      rowLinear A C B i := by
  let k := succ i
  let hB := h.andE₁
  let s := ofGaussian (step A C) B
  let d := offset (step A C) B k
  let u := naturalPoint k
  let j := GaussianBarnesCanonicalDeflatedFactor.inverseInteger k
  let v := reciprocal (base (center A B) B k)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ i
  have step_eq : Γ ⊢[PRAAx] qmul u d ≐ s :=
    (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalSecondDerivativeStep.step_factor (step A C) B k hB hk).eqSymm).eqTrans
      ((qmul_commutative u (qmul s j)).eqTrans ((qmul_associative s j u).eqTrans
        ((qmul_congr (.eqRefl _) ((qmul_commutative j u).eqTrans
          (GaussianBetaUpperEndpointInverse.natural_reciprocal_one k hk))).eqTrans
          (qmul_one_right s (ofGaussian_canonical _ _ hB)))))
  have rat := qmul_congr (scaled_argument A C B i hB) (inverse_at A B K i h.andE₂.andE₁ hB
    h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁)
  exact (qmul_congr (.eqRefl u) rat).eqTrans ((qmul_associative u d v).eqSymm.eqTrans (qmul_congr step_eq (.eqRefl _)))

theorem observation (p A C B H K N i : PTm n) (h : Γ ⊢[PRAAx] source A C B H K)
    (hi : Γ ⊢[PRAAx] le (succ i) N) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 originalExponentF p (rowData C B i)) (ap2 originalExponentF p (rowData A B i)))
      (rowLinear A C B i) (numerator K H*unit p+two*N*(B*B)) ((B*B)*unit p) := by
  let k := succ i
  let D := B*k
  let W := B*B
  let a := shiftedNumerator A B i
  let c := shiftedNumerator C B i
  let s := clock p k (data c D)
  let t := clock p k (data a D)
  let U := unit p
  let P := unit s
  let Q := unit t
  let V := numerator K H
  let m := naturalPoint k
  let obs := GaussianPositiveRationalLogarithmSignedIncrement.observed s t a D c D
  let target := GaussianPositiveRationalLogarithmSignedIncrement.linear a D c D
  have hB := h.andE₁
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ i
  have hD := positive_product B k hB hk
  have hW := positive_product B B hB hB
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hP : Γ ⊢[PRAAx] le one P := unit_positive s
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive t
  have hE := positive_product _ _ (positive_product _ _ hD hD) (positive_product _ _ hP hQ)
  have hK := h.andE₂.andE₂.andE₂.andE₁
  have shift := row_shift_bound A C B H i h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have core := GaussianPositiveRationalLogarithmSignedIncrement.common_denominator s t a c D K H D
    (shifted_positive A B i h.andE₂.andE₁) (shifted_positive C B i h.andE₂.andE₂.andE₁) hD hD
    (row_margin A B K i hK h.andE₂.andE₂.andE₂.andE₂.andE₁)
    (row_margin C B K i hK h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁)
    (le_congr (by ipra_ring) (.eqRefl _) (Common.mul_le_mul shift (le_refl D)))
  have scaled := GaussianNamedDifferenceQuotient.scale_distance m obs target k _ _ hE
    (GaussianNamedNaturalScale.natural_point_bound k) core
  have su : Γ ⊢[PRAAx] le U P := GaussianExponentialReference.unit_monotone
    (GaussianNaturalScaleProductName.clock_later logF p k (data c D))
  have tu : Γ ⊢[PRAAx] le U Q := GaussianExponentialReference.unit_monotone
    (GaussianNaturalScaleProductName.clock_later logF p k (data a D))
  have su' : Γ ⊢[PRAAx] le (k*U) (N*P) := mul_le_mul hi su
  have tu' : Γ ⊢[PRAAx] le (k*U) (N*Q) := mul_le_mul hi tu
  have capK : Γ ⊢[PRAAx] le (W*k) (D*D) := le_congr (by ipra_ring) (by dsimp only [D,W]; ipra_ring)
    (mul_le_mul (le_refl (W*k)) hk)
  have radius : Γ ⊢[PRAAx] le ((k*(V*(P*Q)+(D*D)*(P+Q)))*(W*U))
      ((V*U+two*N*W)*((D*D)*(P*Q))) := by
    ipra_le 𝔞 V*𝔞 U*𝔞 P*𝔞 Q*sl capK +
      𝔞 W*𝔞(D*D)*𝔞 Q*sl su' + 𝔞 W*𝔞(D*D)*𝔞 P*sl tu'
  have fixed := distance_radius_mono _ _ _ _ _ _ hE (positive_product _ _ hW hU) radius
    (distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [V,numerator,P,Q,
      GaussianPositiveRationalLogarithmSignedIncrement.budget]; ipra_ring) (.eqRefl _) scaled)
  have ec := (GaussianNaturalScaleProductName.product_at (Γ := Γ) logF p k (data c D)).eqTrans (natScale_as_product k _)
  have ea := (GaussianNaturalScaleProductName.product_at (Γ := Γ) logF p k (data a D)).eqTrans (natScale_as_product k _)
  have e := (qsub_congr ec ea).eqTrans (multiplication_difference m _ _)
  exact distance_congr e.eqSymm (linear_at A C B H K i h) (.eqRefl _) (.eqRefl _) fixed

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative
