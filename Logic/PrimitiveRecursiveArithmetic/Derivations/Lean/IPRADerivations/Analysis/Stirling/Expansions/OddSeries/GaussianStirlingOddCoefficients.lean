import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddSeries
import IPRADerivations.Analysis.Logarithm.Robin.GaussianRobinOddLogarithm
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift

/-!
# Exact coefficients of the normalized Stirling odd series

Multiplying a Robin odd logarithm coefficient by ((2A+B)/(2B))
removes one power of its odd-series argument. The constant term becomes
one. This normalization also applies to the exact geometric tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 560000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingOddCoefficients

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Pv)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner
  (ofGaussian qadd qmul canonical_unique represents_congr represents_rescale represents ofGaussian_represents ofGaussian_canonical
    qadd_represents qmul_represents qadd_canonical qmul_canonical positive_product qzero)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone qone_canonical qzero_add)
open GaussianStirlingDifference (coefficient minusOne)
open GaussianStirlingOddSeries (baseDenominator degree)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_mul im_mul re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_equal (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] a*d ≐ c*b) : Γ ⊢[PRAAx] fraction a b ≐ fraction c d := by
  let u := scale a oneCode
  let v := scale c oneCode
  have ru := represents_rescale (fraction a b) u b d (ofGaussian_represents u b hb)
  have rv := represents_rescale (fraction c d) v d b (ofGaussian_represents v d hd)
  have e : Γ ⊢[PRAAx] equal (scale d u) (scale b v) := by
    have p := natEq h
    apply equal_of_values <;> simp only [u,v,re_scale,im_scale,re_one,im_one] <;>
      (try ipra_simps) <;> (try linear_combination p) <;> ring
  exact canonical_unique _ _ _ _ (ofGaussian_canonical u b hb) (ofGaussian_canonical v d hd)
    (positive_product _ _ hb hd) (represents_congr (.eqRefl _) e (.eqRefl _) ru)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _) rv)

theorem fraction_product (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] qmul (fraction a b) (fraction c d) ≐ fraction (a*c) (b*d) := by
  let u := scale a oneCode
  let v := scale c oneCode
  have den := positive_product _ _ hb hd
  have rep := qmul_represents (fraction a b) (fraction c d) u v b d hb hd
    (ofGaussian_represents u b hb) (ofGaussian_represents v d hd)
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul u v) (scale (a*c) oneCode) := by
    apply equal_of_values <;> simp only [u,v,re_mul,im_mul,re_scale,im_scale,re_one,im_one,IPRA.Q.mk_mul,map_mul] <;> ring
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ den) den
    (represents_congr (.eqRefl _) e (.eqRefl _) rep) (ofGaussian_represents _ _ den)

theorem fraction_add_same (a c b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qadd (fraction a b) (fraction c b) ≐ fraction (a+c) b := by
  let u := scale a oneCode
  let v := scale c oneCode
  have rep := qadd_represents (fraction a b) (fraction c b) u v b hb (ofGaussian_represents u b hb) (ofGaussian_represents v b hb)
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.add u v) (scale (a+c) oneCode) := by
    apply equal_of_values <;> simp only [u,v,re_add,im_add,re_scale,im_scale,re_one,im_one,IPRA.Q.mk_add,map_add] <;> ring
  exact canonical_unique _ _ _ _ (qadd_canonical _ _) (ofGaussian_canonical _ _ hb) hb
    (represents_congr (.eqRefl _) e (.eqRefl _) rep) (ofGaussian_represents _ _ hb)

theorem fraction_embed (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    RationalGaussianEmbedding.embed (GaussianEuclideanDistanceName.fraction a b) ≐ fraction a b := by
  have rr := RationalGaussianEmbedding.embed_from_representation _ _ _
    (GaussianEuclideanDistanceName.fraction_represents a b hb)
  have e : Γ ⊢[PRAAx] equal (RationalGaussianEmbedding.native (ZT.ofNat a)) (scale a oneCode) := by
    apply equal_of_values <;>
      simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
        re_scale,im_scale,re_one,im_one,ZT.toZ_ofNat] <;> (try ipra_simps) <;> ring
  exact canonical_unique _ _ _ _ (RationalGaussianEmbedding.embed_canonical _) (ofGaussian_canonical _ _ hb) hb
    (represents_congr (.eqRefl _) e (.eqRefl _) rr) (ofGaussian_represents _ _ hb)

private theorem fraction_one (a : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] fraction a a ≐ qone :=
  canonical_unique _ _ _ a (ofGaussian_canonical _ _ ha) qone_canonical ha
    (ofGaussian_represents _ _ ha) (GaussianRationalReciprocal.qone_represents_scaled a)

alias coefficient_denominator_positive := Common.one_le_two_mul

theorem base_positive (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (baseDenominator A B) := by
  dsimp [baseDenominator]
  ipra_le 2*sl hA+1+Groth.ι (IPRA.Q.mk Γ B)

theorem first_term (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (coefficient A B) (GaussianRobinOddLogarithm.term B (baseDenominator A B) zero) ≐ qone := by
  let s := baseDenominator A B
  let P := two*B
  have hs := base_positive A B hA
  have hP := coefficient_denominator_positive B hB
  have eval (x : PTm n) : Γ ⊢[PRAAx] Pv zero x ≐ x := by
    have e : Γ ⊢[PRAAx] succ (two*(zero : PTm n)) ≐ one := by ipra_ring
    exact (congrAp2 powF e (.eqRefl _)).eqTrans (pw_one _)
  have term : Γ ⊢[PRAAx] GaussianRobinOddLogarithm.term B s zero ≐ fraction P s := by
    have ea : Γ ⊢[PRAAx] two*Pv zero B ≐ P := congrMul (.eqRefl _) (eval B)
    have eb : Γ ⊢[PRAAx] GaussianRobinOddLogarithm.oddIndex zero*Pv zero s ≐ s := by
      dsimp [GaussianRobinOddLogarithm.oddIndex]
      apply deriveNat
      ipra_simps
      linear_combination natEq (eval s)
    exact GaussianRationalHorner.real_fraction_congr ea eb
  have e : Γ ⊢[PRAAx] fraction (s*P) (P*s) ≐ fraction (P*s) (P*s) :=
    fraction_equal _ _ _ _ (positive_product _ _ hP hs) (positive_product _ _ hP hs) (by ipra_ring)
  exact (qmul_congr (.eqRefl _) term).eqTrans ((fraction_product s P P s hP hs).eqTrans
    (e.eqTrans (fraction_one (P*s) (positive_product _ _ hP hs))))

theorem scaled_odd_fraction (A B j C D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qmul (coefficient A B) (fraction (two*Pv (succ j) B*C) (succ (degree j)*D*Pv (succ j) (baseDenominator A B))) ≐
      fraction (pw B (degree j)*C) (succ (degree j)*pw (baseDenominator A B) (degree j)*D) := by
  let s := baseDenominator A B
  let J := degree j
  let P := two*B
  have hs := base_positive A B hA
  have hP := coefficient_denominator_positive B hB
  have p := GaussianFactorBudget.power_positive s (succ J) hs
  have pt := GaussianFactorBudget.power_positive s J hs
  have ds := positive_product _ _ (positive_product _ _ (zero_lt_succ J) hD) p
  have dt := positive_product _ _ (positive_product _ _ (zero_lt_succ J) pt) hD
  apply (fraction_product s P _ _ hP ds).eqTrans
  apply fraction_equal _ _ _ _ (positive_product _ _ hP ds) dt
  have eB := natEq (pw_succ (Γ := Γ) B J)
  have es := natEq (pw_succ (Γ := Γ) s J)
  change Γ ⊢[PRAAx] (s*(two*pw B (succ J)*C))*(succ J*pw s J*D) ≐
    (pw B J*C)*(P*(succ J*D*pw s (succ J)))
  apply deriveNat
  dsimp only [P]
  ipra_simps
  rw [eB,es]
  ring

theorem scaled_term (A B j : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (coefficient A B) (GaussianRobinOddLogarithm.term B (baseDenominator A B) (succ j)) ≐
      GaussianStirlingOddSeries.term A B j := by
  let s := baseDenominator A B
  let P := GaussianRobinOddLogarithm.term B s (succ j)
  let T := GaussianStirlingOddSeries.term A B j
  have hs := base_positive A B hA
  have h0 := GaussianFactorBudget.power_positive s (succ (degree j)) hs
  have h1 := GaussianFactorBudget.power_positive s (degree j) hs
  have pD : Γ ⊢[PRAAx] le one (succ (degree j)*Pv (succ j) s) := positive_product _ _ (zero_lt_succ _) h0
  have tD : Γ ⊢[PRAAx] le one (succ (degree j)*pw s (degree j)) := positive_product _ _ (zero_lt_succ _) h1
  have a : Γ ⊢[PRAAx] P ≐ fraction (two*Pv (succ j) B*one) (succ (degree j)*one*Pv (succ j) s) :=
    fraction_equal _ _ _ _ pD (positive_product _ _ (positive_product _ _ (zero_lt_succ _) (le_refl one)) h0) (by
      dsimp [GaussianRobinOddLogarithm.oddIndex,degree]
      ipra_ring)
  have b : Γ ⊢[PRAAx] fraction (pw B (degree j)*one) (succ (degree j)*pw s (degree j)*one) ≐ T :=
    fraction_equal _ _ _ _ (positive_product _ _ tD (le_refl one)) tD (by ipra_ring)
  exact (qmul_congr (.eqRefl _) a).eqTrans ((scaled_odd_fraction A B j one one hA hB (le_refl one)).eqTrans b)

theorem additive_constant_zero : Γ ⊢[PRAAx] qadd (qone : PTm n) minusOne ≐ qzero := by
  have e := GaussianRationalSyntheticDivision.qzero_add (Γ := Γ) (GaussianRationalMetric.qnegative qone)
    (GaussianRationalMetric.qnegative_canonical _)
  exact (qadd_congr (.eqRefl _) e.eqSymm).eqTrans (GaussianNameRingLaws.additive_inverse_value qone)

end LeanProofs.IPRA.Analysis.GaussianStirlingOddCoefficients
