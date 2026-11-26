import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalBase
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherRows
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaProductPascal
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialTermBound
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalTravelScaling
import IPRADerivations.Analysis.RationalArithmetic.GaussianScalarColumnSelection
import IPRADerivations.Core.CommonLemmas

/-!
# Positive-axis cubic rows of the original Barnes logarithm

At x=A/B, the Barnes product center is x−1. The original
factorially scaled cubic row at index i+1 is the positive fraction
2(i+1)B³/(A+iB)³. On x≥1 its size is bounded by the corresponding
inverse square.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalHigherRows (derivative)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_congr radius_represents radius_numerator_norm
  radius_multiply radius_power radius_bounded)
open GaussianEulerIncompleteFactorialDenominator (radius_rescale)
open GaussianPositiveRealArithmetic (positive)
open GaussianRationalHorner (canonical canonical_unique ofGaussian_canonical positive_product qadd_canonical
  qmul qmul_canonical represents_congr)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (power power_succ reciprocal reciprocal_canonical reciprocal_identity)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values)
open LeanProofs.IPRA.Analysis.Products (fact)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def center (A B : PTm n) : PTm n := code (ZT.ofNat A-ZT.ofNat B) (ZT.ofNat zero)
def shiftedNumerator (A B i : PTm n) : PTm n := A+i*B
def numerator (B i : PTm n) : PTm n := two*succ i*pw B (succ two)
def denominator (A B i : PTm n) : PTm n := pw (shiftedNumerator A B i) (succ two)
def row (A B i : PTm n) : PTm n := radiusPoint (numerator B i) (denominator A B i)

@[simp] theorem subst_center {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (center A B) = center (Syn.subst σ A) (Syn.subst σ B) := by simp [center]

@[simp] theorem subst_shiftedNumerator {m : ℕ} (σ : Fin n → PTm m) (A B i : PTm n) :
    Syn.subst σ (shiftedNumerator A B i) = shiftedNumerator (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ i) :=
  by simp [shiftedNumerator]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (B i : PTm n) :
    Syn.subst σ (numerator B i) = numerator (Syn.subst σ B) (Syn.subst σ i) := by simp [numerator,two,one]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (A B i : PTm n) :
    Syn.subst σ (denominator A B i) = denominator (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ i) :=
  by simp [denominator]

@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (A B i : PTm n) :
    Syn.subst σ (row A B i) = row (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ i) := by simp [row]

theorem shifted_positive (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (shiftedNumerator A B i) :=
  le_trans hA (le_add_right A (i*B))

theorem denominator_positive (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (denominator A B i) :=
  GaussianFactorBudget.power_positive _ _ (shifted_positive A B i hA)

theorem base_at (A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] base (center A B) B (succ i) ≐ radiusPoint (shiftedNumerator A B i) (B*succ i) := by
  let d := B*succ i
  let c := shiftedNumerator A B i
  have hd := positive_product B (succ i) hB (zero_lt_succ i)
  have same : Γ ⊢[PRAAx] equal (GaussianGammaEulerHeadLower.translated (center A B) B (succ i))
      (radiusNumerator c) := by
    apply equal_of_values
    · simp only [GaussianGammaEulerHeadLower.translated,center,c,shiftedNumerator,radiusNumerator,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,
        ComplexLogarithmRemainder.eval_re_code,ZT.toZ_sub,ZT.toZ_ofNat]
      ipra_simps
      ring
    · simp only [GaussianGammaEulerHeadLower.translated,center,c,radiusNumerator,
        GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,
        ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
      ring
  exact canonical_unique _ _ _ d (qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) same (.eqRefl _) (GaussianBarnesCanonicalBase.base_represents _ _ _ hB (zero_lt_succ i)))
    (radius_represents c d hd)

private theorem radius_floor (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] lower (radiusPoint a b) one b := by
  apply lower_from_representation _ _ _ _ _ hb hb (radius_represents a b hb)
  exact le_congr (mul_comm (b*b) (one*one)) (congrMul (.eqRefl (b*b)) (radius_numerator_norm a).eqSymm)
    (LeanProofs.IPRA.Common.mul_le_mul (le_refl (b*b)) (LeanProofs.IPRA.Common.mul_le_mul ha ha))

private theorem reciprocal_radius (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] reciprocal (radiusPoint a b) ≐ radiusPoint b a := by
  have nonzero := GaussianNameReciprocal.lower_norm_positive (radiusPoint a b) b hb (radius_floor a b ha hb)
  exact GaussianEulerBetaProductPascal.inverse_unique _ _ _
    (reciprocal_canonical _) (ofGaussian_canonical _ _ ha)
    (reciprocal_identity _ nonzero)
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianRationalTravelScaling.inverse_radius a b ha hb))

private theorem square_value (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) :
    Γ ⊢[PRAAx] power q two ≐ qmul q q := by
  have first : Γ ⊢[PRAAx] power q one ≐ q :=
    (power_succ q zero).eqTrans
      ((qmul_congr (GaussianRationalReciprocal.power_zero q) (.eqRefl q)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right q hq)))
  exact (power_succ q one).eqTrans (qmul_congr first (.eqRefl q))

private theorem signed_cube (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) :
    Γ ⊢[PRAAx] qnegative (power (qnegative q) (succ two)) ≐ power q (succ two) := by
  let t := qmul q q
  have sq : Γ ⊢[PRAAx] power (qnegative q) two ≐ t := (square_value (qnegative q) (GaussianRationalMetric.qnegative_canonical q)).eqTrans
    (GaussianScalarColumnSelection.negative_both_product q q)
  have cube : Γ ⊢[PRAAx] power (qnegative q) (succ two) ≐ qnegative (qmul t q) :=
    (power_succ (qnegative q) two).eqTrans ((qmul_congr sq (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative t (qnegative q)).eqTrans
        ((GaussianInverseBinomialRows.negative_product q t).eqSymm.eqTrans
          (GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative q t)))))
  exact (GaussianInverseBinomialRows.negative_congr cube).eqTrans
    ((GaussianDeterminantSignTransport.negative_involution _ (qmul_canonical t q)).eqTrans
      ((power_succ q two).eqTrans (qmul_congr (square_value q hq) (.eqRefl q))).eqSymm)

private theorem fact_two : Γ ⊢[PRAAx] fact (two : PTm n) ≐ two := by
  have first : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl one)).eqTrans (one_mul one))
  exact (fact_succ one zero).eqTrans ((congrMul first (.eqRefl two)).eqTrans (one_mul two))

theorem derivative_at (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] derivative (center A B) B (succ i) zero ≐ row A B i := by
  let k := succ i
  let c := shiftedNumerator A B i
  let d := B*k
  let q := reciprocal (base (center A B) B k)
  let X := pw k two
  let Y := denominator A B i
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ i
  have hc := shifted_positive A B i hA
  have hd := positive_product B k hB hk
  have hX : Γ ⊢[PRAAx] le one X := GaussianFactorBudget.power_positive _ _ hk
  have hY := denominator_positive A B i hA
  have hv : Γ ⊢[PRAAx] q ≐ radiusPoint d c := by
    have move : Γ ⊢[PRAAx] q ≐ reciprocal (radiusPoint c d) :=
      GaussianNameReciprocal.reciprocal_congr (base_at A B i hB)
    exact move.eqTrans (reciprocal_radius c d hc hd)
  have cube : Γ ⊢[PRAAx] qnegative (power (qnegative q) (succ two)) ≐ radiusPoint (pw d (succ two)) Y :=
    (signed_cube q (reciprocal_canonical _)).eqTrans
      ((congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) hv).eqTrans (radius_power d c (succ two) hc))
  have scale : Γ ⊢[PRAAx] pw d (succ two)*fact (two : PTm n) ≐ numerator B i*X := by
    have separate := natEq (AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) B k (succ two))
    have powers := natEq (pw_succ (Γ := Γ) k two)
    apply LeanProofs.IPRA.deriveNat
    dsimp only [d,X,numerator]
    ipra_simps
    rw [natEq (fact_two (Γ := Γ)), separate, powers]
    dsimp only [k]
    ipra_simps
    ring
  exact (qmul_congr cube (.eqRefl (radiusPoint (fact two) X))).eqTrans
    ((radius_multiply _ _ _ _ hY hX).eqTrans
      ((radius_congr scale (.eqRefl (Y*X))).eqTrans (radius_rescale (numerator B i) Y X hY hX)))

theorem positive_floor (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] positive (row A B i) ⋏ lower (row A B i) one (denominator A B i) := by
  have hD := denominator_positive A B i hA
  have hP : Γ ⊢[PRAAx] le one (numerator B i) :=
    positive_product _ _ (positive_product _ _ (le_succ_self one) (zero_lt_succ i))
      (GaussianFactorBudget.power_positive _ _ hB)
  exact .andI (GaussianPositiveExponentialTermBound.actual_positive_fraction _ _ hD) (radius_floor _ _ hP hD)

theorem square_bound (A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A) :
    let c := shiftedNumerator A B i
    Γ ⊢[PRAAx] bounded (row A B i) (two*pw B two) (pw c two) := by
  let c := shiftedNumerator A B i
  have hA := le_trans hB hBA
  have hD := denominator_positive A B i hA
  have hC := GaussianFactorBudget.power_positive c two (shifted_positive A B i hA)
  have clear : Γ ⊢[PRAAx] le (succ i*B) c :=
    le_congr (by ipra_ring) (.eqRefl _) (add_le_add_right (i*B) hBA)
  have cubeB := natEq (pw_succ (Γ := Γ) B two)
  have cubeC := natEq (pw_succ (Γ := Γ) c two)
  have compare : Γ ⊢[PRAAx] le (numerator B i*pw c two) ((two*pw B two)*denominator A B i) := by
    change Γ ⊢[PRAAx] le (numerator B i*pw c two) ((two*pw B two)*pw c (succ two))
    ipra_le 2*𝔞(pw B two)*𝔞(pw c two)*sl clear using
      dsimp only [numerator]
      ipra_simps
      rw [cubeB, cubeC]
      ring
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hD hC compare (radius_bounded _ _ hD)

theorem actual_Barnes_positive_cubic_logarithm_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let A := var 0
     let B := var 1
     let i := var 2
     (le one A ⋏ le one B) ⟶
       (derivative (center A B) B (succ i) zero ≐ row A B i) ⋏
       (positive (row A B i) ⋏ lower (row A B i) one (denominator A B i))) :=
  closeUniv 3 (.impI (.andI (derivative_at _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (positive_floor _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmRows
