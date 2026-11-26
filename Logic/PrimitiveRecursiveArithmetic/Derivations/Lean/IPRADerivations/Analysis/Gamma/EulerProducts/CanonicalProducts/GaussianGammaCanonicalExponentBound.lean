import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent
import IPRADerivations.AnalyticNumberTheory.FactorialError
import IPRADerivations.Core.IntCertificates

/-!
# The numerical disk for the original Gamma C7 exponent

The exact bound (2R^2+2R) holds at every observation of the
original C7 exponent. The bound uses the Euler sample in ([0,1]),
the actual harmonic sum at (2R), and the C6 tail radius including
its observation rounding error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalExponentBound

open_ipra
open RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalArgmin (denominator_positive rationalLE to_zle)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRationalHorner (ofGaussian qmul qadd ofGaussian_represents)
open GaussianRationalMetric (bounded qsub qnegative)
open GaussianRationalReciprocal (bounded_sum bounded_product bounded_negative bound_congr)
open RationalGaussianEmbedding (native embed embed_from_representation)
open GaussianGammaCanonicalExponent

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem numerator_range (q A : PTm n) (lo : Γ ⊢[PRAAx] rationalLE (natCode zero) q)
    (hi : Γ ⊢[PRAAx] rationalLE q (natCode A)) :
    Γ ⊢[PRAAx] zle (ZT.ofNat zero) (numeratorOf q) ⋏
      zle (numeratorOf q) (ZT.ofNat (A*denominatorOf q)) := by
  have l := to_zle _ _ lo
  have u := to_zle _ _ hi
  have e₀ := ZT.toZ_eq (natCode_represents (Γ := Γ) zero)
  have e₁ := ZT.toZ_eq (natCode_represents (Γ := Γ) A)
  simp only [ZT.toZ_mul, ZT.toZ_ofNat] at e₀ e₁
  refine .andI ?_ ?_
  · apply PolynomialBisection.zle_scale_cancel (denominator_positive (natCode zero))
    refine zle_of_comb (zsl l) ?_ (nn_zsl l)
    zsimp
    ipra_simps
    linear_combination -𝔞(denominatorOf q)*e₀
  · apply PolynomialBisection.zle_scale_cancel (denominator_positive (natCode A))
    refine zle_of_comb (zsl u) ?_ (nn_zsl u)
    zsimp
    ipra_simps
    linear_combination 𝔞(denominatorOf q)*e₁

theorem scalar_representation_bound (q A E : PTm n) (a : ZT n)
    (hE : Γ ⊢[PRAAx] le one E) (hq : Γ ⊢[PRAAx] RationalArithmetic.represents q a E)
    (lo : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a) (hi : Γ ⊢[PRAAx] zle a (ZT.ofNat (A*E))) :
    Γ ⊢[PRAAx] bounded (embed q) A one := by
  let m := PolynomialBisection.slack (ZT.ofNat zero) a
  have hm : ZT.toZ Γ a = 𝔞 m := by
    simpa only [m, PolynomialBisection.slack, ZT.toZ_ofNat, Q.mk_zero, map_zero, _root_.zero_add] using
      (zle_toZ lo).symm
  have upper : Γ ⊢[PRAAx] le m (A*E) := by
    apply le_of_eq_add (d := PolynomialBisection.slack a (ZT.ofNat (A*E)))
    have e := zle_toZ hi
    apply deriveNat
    simp only [ZT.toZ_ofNat, hm] at e
    unfold PolynomialBisection.slack
    ipra_simps
    linear_combination -e
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (native a) ≐ m*m := by
    apply deriveNat
    rw [native, ComplexLogarithmRemainder.normSq_code, hm]
    simp only [ZT.toZ_ofNat, Q.mk_zero, map_zero, Q.mk_mul, map_mul]
    ring
  have e : Γ ⊢[PRAAx] (one*one)*ComplexLogarithmRemainder.normSq (native a) ≐ m*m :=
    (by ipra_ring : Γ ⊢[PRAAx] (one*one)*ComplexLogarithmRemainder.normSq (native a) ≐
      ComplexLogarithmRemainder.normSq (native a)).eqTrans norm
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hE (le_refl _)
    (embed_from_representation q a E hq)
    (le_congr e.eqSymm (by ipra_ring) (le_mul_mono upper upper))

theorem gamma_observation_bound (p : PTm n) :
    Γ ⊢[PRAAx] bounded (embed (GammaEulerConstantName.gammaSample p zero)) one one := by
  let q := GammaEulerConstantName.gammaSample p zero
  have inside := GammaEulerConstantName.gamma_sample_range (Γ := Γ) p zero
  have numBound := numerator_range q one inside.andE₁ inside.andE₂
  exact scalar_representation_bound q one (denominatorOf q) (numeratorOf q)
    (denominator_positive q) (RationalRepresentations.represents_self q) numBound.andE₁ numBound.andE₂

theorem harmonic_point_bound (K : PTm n) : Γ ⊢[PRAAx] bounded (harmonicPoint K) K one := by
  let F := Products.fact K
  let H := AnalyticNumberTheory.Harmonic.S K F
  refine scalar_representation_bound (harmonic K) K F (ZT.ofNat H)
    (GammaEulerMesh.factorial_positive K) (harmonic_represents K) ?_ ?_
  · apply zle_of_toZ H
    simp only [ZT.toZ_ofNat, Q.mk_zero, map_zero, _root_.zero_add]
  · have h : Γ ⊢[PRAAx] le H (K*F) := AnalyticNumberTheory.FactorialError.S_le K F
    apply zle_of_toZ (monus (K*F) H)
    simpa only [ZT.toZ_ofNat, Q.mk_add, map_add] using (natEq (eq_add_of_le h)).symm

theorem tail_point_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (GaussianGammaCanonicalTailName.value p z R B (two*R)) R one := by
  let U := DyadicComplexLogarithm.unit p
  have h₄ : Γ ⊢[PRAAx] le (num 4) U := le_trans
    (le_of_eq_add (d := num 12) (by ipra_ring)) (GaussianLocalLogarithmName.unit_lower p)
  have hU : Γ ⊢[PRAAx] le (R*R*U+two*(two*R)) (R*((two*R)*U)) := by
    have hR := h.andE₁
    ipra_le 𝔞 R*sl h₄+𝔞 (R*U)*sl hR
  have hT := tail_source z R B h
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianGammaCanonicalTailName.denominator_positive p (two*R) hT.andE₂.andE₁) (le_refl _)
    (le_congr (by unfold GaussianGammaCanonicalTailName.radius; ipra_ring) (.eqRefl _) hU)
    (GaussianGammaCanonicalTailName.value_bound p z R B (two*R) hT)

def numericalRadius (R : PTm n) : PTm n := two*R*R+two*R

ipra_subst numericalRadius

theorem difference_value_bound (p K : PTm n) :
    Γ ⊢[PRAAx] bounded (differenceValue p K) (one+K) one := by
  apply (GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl _)).iffMpr
  have h := bounded_sum (Γ := Γ) _ _ _ _ _ _ (le_refl _) (le_refl _)
    (gamma_observation_bound (addPrecision p))
    (bounded_negative _ _ _ (le_refl _) (harmonic_point_bound K))
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) h

theorem product_value_bound (p z R B K : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (productValue p z B K) ((one+K)*R) one := by
  apply (GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl _)).iffMpr
  have hB := h.andE₂.andE₁
  have hz := h.andE₂.andE₂
  have hb : Γ ⊢[PRAAx] bounded (ofGaussian z B) R one :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hB (le_refl _) (ofGaussian_represents _ _ hB)
      (le_congr (by ipra_ring) (by ipra_ring) hz)
  exact bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _)
      (difference_value_bound (productPrecision z B K p) K) hb)

theorem exponent_point_numerical_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (exponentPoint p z R B) (numericalRadius R) one := by
  apply bound_congr (exponent_sample_at _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
  apply (GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl _)).iffMpr
  have main := bounded_sum _ _ _ _ _ _ (le_refl _) (le_refl _)
    (product_value_bound (addPrecision p) z R B (two*R) h)
    (tail_point_bound (addPrecision p) z R B h)
  exact bound_congr (.eqRefl _) (by unfold numericalRadius; ipra_ring) (by ipra_ring) main

theorem exact_exponential_input (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input exponentF (numericalRadius R) (exponentData z R B) := by
  refine .andI (exponent_regular z R B h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by
    simpa only [Syn.shift, Fm.shift, subst_source] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples, exponentPoint, Syn.shift,
    subst_exponentData, subst_numericalRadius] using
    exponent_point_numerical_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hs

theorem original_gamma_C7_exact_exponent_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶
      bounded (exponentPoint (var 0) (var 1) (var 2) (var 3)) (numericalRadius (var 2)) one) :=
  closeUniv 4 (.impI (exponent_point_numerical_bound _ _ _ _ Prf.hyp0))

theorem original_gamma_C7_exact_exponential_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ GaussianRadiusExponentialName.input exponentF
      (numericalRadius (var 1)) (exponentData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (exact_exponential_input _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalExponentBound
