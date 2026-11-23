import IPRADerivations.AnalyticNumberTheory.Doubling
import IPRADerivations.AnalyticNumberTheory.PsiModulus
import IPRADerivations.Analysis.GaussianPositiveRationalLogarithmSign
import IPRADerivations.Analysis.GaussianGammaIntegralCutoffs

/-!
# Actual logarithmic cutoff endpoints escape every signed integer box

At k >= 2^(2(t+1)), the unchanged original logarithm observations
at top_k and 1/eta_k lie beyond t and -t, respectively, with only their
requested dyadic allowance. The original finite harmonic denominator
and dyadic block lower bound supply the endpoint order internally.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialEndpointEscape

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open RationalHarmonicInterval (horizon interval numerator common_value)
open GaussianGammaIntegralCutoffs (height top etaDen)
open GaussianPositiveRationalLogarithm (logF data sample name_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open RationalValueBounds (upper upper_of_radius upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def exponent (t : PTm n) : PTm n := two*(t+one)
def minimumCutoff (t : PTm n) : PTm n := unit (exponent t)
def largePoint (t : PTm n) : PTm n := two*unit (exponent t)
def negativeInteger (t : PTm n) : PTm n := RationalArithmetic.negative (natCode t)

@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) : Syn.subst σ (exponent t) = exponent (Syn.subst σ t) := by simp [exponent]
@[simp] theorem subst_minimumCutoff {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) : Syn.subst σ (minimumCutoff t) = minimumCutoff (Syn.subst σ t) := by simp [minimumCutoff]
@[simp] theorem subst_largePoint {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) : Syn.subst σ (largePoint t) = largePoint (Syn.subst σ t) := by simp [largePoint]
@[simp] theorem subst_negativeInteger {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) : Syn.subst σ (negativeInteger t) = negativeInteger (Syn.subst σ t) := by simp [negativeInteger]

theorem point_positive (t x : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) : Γ ⊢[PRAAx] le one x :=
  le_trans (positive_product _ _ (zero_lt_succ one) (unit_positive (exponent t))) hx

/-- Genuine dyadic blocks inside the actual factorial harmonic sum. -/
theorem finite_numerator_lower (t x Q : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    le (t*Products.fact (horizon x one Q))
      (monus (S (Q*x) (Products.fact (horizon x one Q))) (S (Q*one) (Products.fact (horizon x one Q)))) := by
  let F := Products.fact (horizon x one Q)
  let V := unit (exponent t)
  let δ := monus (S (Q*x) F) (S (Q*one) F)
  have hV := unit_positive (Γ := Γ) (exponent t)
  have vx : Γ ⊢[PRAAx] le V x := le_trans (le_of_eq_add (d := V) (by dsimp only [V,largePoint]; ipra_ring)) hx
  have scaled : Γ ⊢[PRAAx] le (two*(Q*V)) (Q*x) := le_congr (by dsimp only [largePoint,V]; ipra_ring) (by ipra_ring) (mul_le_mul_right Q hx)
  have budget : Γ ⊢[PRAAx] le (two*(Q*V)) F :=
    le_trans scaled (le_trans (RationalHarmonicInterval.left_horizon x one Q) (AnalyticNumberTheory.PsiModulus.le_fact _))
  have up : Γ ⊢[PRAAx] le (Q*V) (Q*x) := le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right Q vx)
  have order : Γ ⊢[PRAAx] le (S (Q*one) F) (S (Q*x) F) :=
    S_mono F (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right Q (point_positive t x hx)))
  have step := AnalyticNumberTheory.Doubling.S_pow2_lower F (exponent t) hQ
  have mono := S_mono F up
  have gap := natEq (eq_add_of_le order)
  have qone := natEq (congrAp2 (sumF hB) (by ipra_ring : Γ ⊢[PRAAx] Q*one ≐ Q) (.eqRefl F))
  have twice : Γ ⊢[PRAAx] le (two*(t*F)) (two*δ) := by
    dsimp only [δ,V,F,exponent,unit] at *
    ipra_le sl step+2*sl mono+sl budget+𝔞(Products.fact (horizon x one Q)) with 2*gap+2*qone
  exact RationalValueBounds.positive_cancel (zero_lt_succ (Γ := Γ) one) twice

theorem interval_lower (t x Q : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (natCode t) (interval x one Q) := by
  let L := horizon x one Q
  let F := Products.fact L
  let δ := monus (S (Q*x) F) (S (Q*one) F)
  have bound := natEq (eq_add_of_le (finite_numerator_lower t x Q hx hQ))
  have increasing : Γ ⊢[PRAAx] le (Q*one) (Q*x) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right Q (point_positive t x hx))
  have order := natEq (eq_add_of_le (S_mono F increasing))
  apply RationalArithmetic.order_of_representations _ _ (ZT.ofNat t) (numerator x one Q L) one F
    (natCode_represents t) (common_value x one Q L) (le_refl one) (GammaEulerMesh.factorial_positive L)
  apply zle_of_toZ (monus δ (t*F))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  dsimp only [δ,F,L] at bound order ⊢
  ipra_simps
  linear_combination -bound-order

theorem reciprocal_interval_upper (t x Q : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (interval one x Q) (negativeInteger t) := by
  let L := horizon one x Q
  let F := Products.fact L
  let δ := monus (S (Q*x) F) (S (Q*one) F)
  have same : Γ ⊢[PRAAx] horizon x one Q ≐ L := by dsimp only [L,horizon]; ipra_ring
  have lower := finite_numerator_lower t x Q hx hQ
  have sf := congrAp2 (Γ := Γ) factF same (.eqRefl zero)
  have low : Γ ⊢[PRAAx] le (t*F) δ := le_congr (congrMul (.eqRefl _) sf)
    (congrMonus (congrAp2 (sumF hB) (.eqRefl _) sf) (congrAp2 (sumF hB) (.eqRefl _) sf)) lower
  have bound := natEq (eq_add_of_le low)
  have increasing : Γ ⊢[PRAAx] le (Q*one) (Q*x) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right Q (point_positive t x hx))
  have order := natEq (eq_add_of_le (S_mono F increasing))
  apply RationalArithmetic.order_of_representations _ _ (numerator one x Q L) (-ZT.ofNat t) F one
    (common_value one x Q L) (RationalRepresentations.represents_negative _ _ _ (natCode_represents t))
    (GammaEulerMesh.factorial_positive L) (le_refl one)
  apply zle_of_toZ (monus δ (t*F))
  simp only [ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  dsimp only [δ,F,L] at bound order ⊢
  ipra_simps
  linear_combination -bound-order

private theorem embedded_lower (t x Q : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (natCode t) (fstT (RationalGaussianEmbedding.embed (interval x one Q))) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (fst_pair _ _).eqSymm
    (RationalArgmin.transitive (interval_lower t x Q hx hQ) (RationalArgmin.eq_le (RationalArithmetic.recode_equal _).eqSymm))

private theorem embedded_upper (t x Q : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (RationalGaussianEmbedding.embed (interval one x Q))) (negativeInteger t) :=
  RationalArgmin.rationalLE_congr (fst_pair _ _).eqSymm (.eqRefl _)
    (RationalArgmin.transitive (RationalArgmin.eq_le (RationalArithmetic.recode_equal _)) (reciprocal_interval_upper t x Q hx hQ))

private theorem lower_budget (p s t x : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (natCode t) (fstT (sample p x one)) one (unit p) (num 9) s := by
  have hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source x one := .andI (point_positive t x hx) (le_refl one)
  have err := GaussianPositiveRationalLogarithmProperness.sample_interval_error s x one hs
  have first := RationalValueBounds.upper_order_left _ _ _ _ _ (embedded_lower t x (GammaEulerConstantName.mesh s) hx (GammaEulerConstantName.mesh_positive s))
    (upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive s) err)))
  have near := GaussianNameEquivalence.point_at logF (data x one) s p (name_regular x one hs)
  have second := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive p)) near)
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (positive_product _ _ (unit_positive s) (unit_positive p)))
    (upper_triangle _ _ _ _ _ _ _ first second) (le_of_eq_add (d := zero) (by ipra_ring))

private theorem upper_budget (p s t x : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (fstT (sample p one x)) (negativeInteger t) one (unit p) (num 9) s := by
  have hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one x := .andI (le_refl one) (point_positive t x hx)
  have near := GaussianNameEquivalence.point_at logF (data one x) p s (name_regular one x hs)
  have first := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive s)) near)
  have err := GaussianPositiveRationalLogarithmProperness.sample_interval_error s one x hs
  have second := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive s) err)
  have joined := RationalValueBounds.upper_order_right _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ first second)
    (embedded_upper t x (GammaEulerConstantName.mesh s) hx (GammaEulerConstantName.mesh_positive s))
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive s)) (unit_positive s))
    joined (le_of_eq_add (d := zero) (by ipra_ring))

theorem original_large_log_lower (p t x : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) : Γ ⊢[PRAAx]
    upper (natCode t) (fstT (sample p x one)) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ (num 9)
    (lower_budget p (GaussianNamedRealOrderTransport.precision (natCode t) (fstT (sample p x one)) (unit p) (num 9)) t x hx)

theorem original_reciprocal_log_upper (p t x : PTm n) (hx : Γ ⊢[PRAAx] le (largePoint t) x) : Γ ⊢[PRAAx]
    upper (fstT (sample p one x)) (negativeInteger t) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ (num 9)
    (upper_budget p (GaussianNamedRealOrderTransport.precision (fstT (sample p one x)) (negativeInteger t) (unit p) (num 9)) t x hx)

theorem top_escape (t k A R : PTm n) (hk : Γ ⊢[PRAAx] le (minimumCutoff t) k) : Γ ⊢[PRAAx] le (largePoint t) (top k A R) := by
  have later : Γ ⊢[PRAAx] le k (height k A R) := le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 10) (by unfold height; ipra_ring)
  exact le_congr (by unfold minimumCutoff largePoint; ipra_ring) (by unfold top; ipra_ring) (mul_le_mul_right two (le_trans hk later))

theorem eta_escape (t k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hk : Γ ⊢[PRAAx] le (minimumCutoff t) k) : Γ ⊢[PRAAx] le (largePoint t) (etaDen k A R) := by
  have small : Γ ⊢[PRAAx] le (exponent t) k := le_trans (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self (exponent t)) hk
  have heightStep : Γ ⊢[PRAAx] le (k+one) (height k A R) :=
    le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 9) (by unfold height; ipra_ring)
  have before : Γ ⊢[PRAAx] le (succ (exponent t)) (height k A R) :=
    le_congr (succ_eq_add_one (exponent t)).eqSymm (.eqRefl _) (le_trans (add_le_add_right one small) heightStep)
  have amplify : Γ ⊢[PRAAx] le (height k A R) (A*height k A R) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (height k A R) hA)
  have next := le_trans before amplify
  exact le_congr ((pw_succ two (exponent t)).eqTrans (mul_comm _ _)) (.eqRefl _) (GaussianExponentialReference.unit_monotone next)

theorem original_right_endpoint (p t k A R : PTm n) (hk : Γ ⊢[PRAAx] le (minimumCutoff t) k) : Γ ⊢[PRAAx]
    upper (natCode t) (fstT (sample p (top k A R) one)) one (unit p) := original_large_log_lower p t _ (top_escape t k A R hk)

theorem original_left_endpoint (p t k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hk : Γ ⊢[PRAAx] le (minimumCutoff t) k) : Γ ⊢[PRAAx]
    upper (fstT (sample p one (etaDen k A R))) (negativeInteger t) one (unit p) := original_reciprocal_log_upper p t _ (eta_escape t k A R hA hk)

theorem actual_original_logarithmic_cutoff_endpoint_escape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ le (minimumCutoff (var 1)) (var 2)) ⟶
      (upper (fstT (sample (var 0) one (etaDen (var 2) (var 3) (var 4)))) (negativeInteger (var 1)) one (unit (var 0)) ⋏
        upper (natCode (var 1)) (fstT (sample (var 0) (top (var 2) (var 3) (var 4)) one)) one (unit (var 0)))) :=
  closeUniv 5 (.impI (.andI (original_left_endpoint _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂) (original_right_endpoint _ _ _ _ _ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialEndpointEscape
