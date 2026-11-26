import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialProduct
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTail
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds

/-!
# A selected term bounds the original positive exponential sum below

Every included term is bounded by the actual finite factorial sum at a
nonnegative rational argument. At a positive rational argument, taking
the original Gaussian rational reciprocal then proves
`|(a/b)^j / S_K(a/b)| ≤ j!` for every internal cutoff `K ≥ j`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveExponentialTermBound

open_ipra
open GaussianPositiveRealArithmetic
  (positive positiveTerms positive_congr positive_sum natural_representation)
open GaussianPositiveExponentialProduct (positive_coefficient positive_scalar_sum scalar_le_add)
open GaussianRationalPolynomialExponential (scalarSum scalarBody inverseFactorial factorial_positive)
open GaussianRationalExponentialTail (scalarPrefix shiftedBody tail prefix_split prefix_succ)
open GaussianScalarExponentialDiagonal (coefficient)
open GaussianRationalHorner (qadd qmul represents canonical represents_congr positive_product scalar_congr)
open GaussianRationalFiniteSum (sum_canonical sum_index_congr)
open GaussianDominantPairAlgebra
  (radiusPoint radiusNumerator radius_represents radius_numerator_norm radius_multiply radius_power radius_bounded)
open RationalGaussianEmbedding (axis_roundtrip embed_from_representation)
open GaussianRationalReciprocal (power reciprocal bounded_product bound_congr)
open GaussianRationalLowerBounds (lower lower_from_representation inverse_bound)
open GaussianRationalMetric (bounded)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalSupMetric (denominatorOf)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem positive_prefix (q K : PTm n) (hq : Γ ⊢[PRAAx] positive q) :
    Γ ⊢[PRAAx] positive (scalarPrefix q K) := by
  apply positive_sum
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift q) :=
    by simpa [Fm.shift, Syn.shift] using hq.shift
  simpa only [positiveTerms, GaussianRationalPolynomialExponential.scalar_body_at, coefficient] using
    positive_coefficient (Syn.shift q) (var 0) hs.wk

theorem positive_suffix (q i K : PTm n) (hq : Γ ⊢[PRAAx] positive q) :
    Γ ⊢[PRAAx] positive (tail q i K) := by
  apply positive_sum
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift q) :=
    by simpa [Fm.shift, Syn.shift] using hq.shift
  have entry := GaussianRationalExponentialTail.body_at
    (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) (Syn.shift q) (Syn.shift i) (var 0)
  simpa only [positiveTerms, GaussianRationalExponentialTail.subst_data, Syn.shift] using
    positive_congr entry.eqSymm (positive_coefficient (Syn.shift q) (Syn.shift i+var 0) hs.wk)

theorem prefix_real_mono (q i j : PTm n) (hq : Γ ⊢[PRAAx] positive q) (hij : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] rationalLE (fstT (scalarPrefix q i)) (fstT (scalarPrefix q j)) := by
  let k := monus j i
  have e := (sum_index_congr scalarBody (eq_add_of_le hij) (.eqRefl q)).eqTrans (prefix_split q i k)
  have rep := (congrFst e).eqTrans (RationalGaussianRealPart.real_add _ _)
  exact rationalLE_congr (.eqRefl _) rep.eqSymm (scalar_le_add _ _
    (sum_canonical scalarBody i q).andE₂.andE₁ (positive_suffix q i k hq).andE₂)

theorem original_term_le (q i K : PTm n) (hq : Γ ⊢[PRAAx] positive q) (hi : Γ ⊢[PRAAx] le i K) :
    Γ ⊢[PRAAx] rationalLE (fstT (coefficient q i)) (fstT (scalarSum q K)) := by
  let t := coefficient q i
  let a := scalarPrefix q i
  have rep := congrFst ((prefix_succ (Γ := Γ) q i).eqTrans
    (GaussianRationalLinearProduct.qadd_commutative a t))
  have monotone : Γ ⊢[PRAAx] le (succ i) (succ K) := (succ_monus_succ i K).eqTrans hi
  have first := scalar_le_add (fstT t) (fstT a)
    (GaussianRationalHorner.qmul_canonical (Γ := Γ) (inverseFactorial i) (power q i)).andE₂.andE₁
    (positive_prefix q i hq).andE₂
  exact transitive
    (rationalLE_congr (.eqRefl _) (rep.eqTrans (RationalGaussianRealPart.real_add t a)).eqSymm first)
    (prefix_real_mono q (succ i) (succ K) hq monotone)

private theorem as_lower_bound (q A B : PTm n) (hq : Γ ⊢[PRAAx] positive q)
    (can : Γ ⊢[PRAAx] canonical q) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint A B)) (fstT q)) :
    Γ ⊢[PRAAx] lower q A B := by
  let a := fstT q
  let D := denominatorOf a
  let M := GaussianPositiveRealArithmetic.numerator a
  have hD : Γ ⊢[PRAAx] le one D := RationalArgmin.denominator_positive a
  have real := natural_representation a hq.andE₂
  have exactA : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (radiusPoint A B)) (ZT.ofNat A) B :=
    scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [radiusNumerator, ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _)
      (radius_represents A B hB).andE₁
  have cmp : Γ ⊢[PRAAx] le (D*A) (M*B) :=
    GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ exactA real h
  have eq := (GaussianTranslatedNonconstant.recode_eq q can).eqSymm.eqTrans (axis_roundtrip q hq.andE₁)
  have rep : Γ ⊢[PRAAx] represents q (radiusNumerator M) D :=
    represents_congr eq.eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
      (embed_from_representation _ _ _ real)
  apply lower_from_representation _ _ _ _ _ hD hB rep
  exact le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] M*B*(M*B) ≐ B*B*(M*M)).eqTrans
    (congrMul (.eqRefl _) (radius_numerator_norm M).eqSymm)) (sq_le_sq cmp)

theorem actual_positive_fraction (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] positive (radiusPoint a b) :=
  GaussianPositiveRealArithmetic.positive_from_representation _ _ _
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb) hb (radius_represents a b hb)

theorem term_fraction (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] coefficient (radiusPoint a b) j ≐ radiusPoint (pw a j) (fact j*pw b j) := by
  unfold coefficient
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (radius_power a b j hb)).eqTrans
    ((radius_multiply one (fact j) (pw a j) (pw b j) (factorial_positive j)
      (GaussianPolynomialPerturbation.power_positive b j hb)).eqTrans
      (GaussianDominantPairAlgebra.radius_congr (one_mul _) (.eqRefl _)))

theorem original_monomial_lower (a b j K : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] lower (scalarSum (radiusPoint a b) K) (pw a j) (fact j*pw b j) := by
  have hp := actual_positive_fraction a b hb
  exact as_lower_bound _ _ _ (positive_scalar_sum _ _ hp) (sum_canonical _ _ _)
    (positive_product _ _ (factorial_positive j) (GaussianPolynomialPerturbation.power_positive b j hb))
    (rationalLE_congr (congrFst (term_fraction a b j hb)) (.eqRefl _) (original_term_le _ _ _ hp hj))

theorem finite_monomial_decay (a b j K : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] bounded (qmul (power (radiusPoint a b) j) (reciprocal (scalarSum (radiusPoint a b) K)))
      (fact j) one := by
  let X := pw a j
  let Y := pw b j
  let u := power (radiusPoint a b) j
  let v := reciprocal (scalarSum (radiusPoint a b) K)
  have hx : Γ ⊢[PRAAx] le one X := GaussianPolynomialPerturbation.power_positive a j ha
  have hy : Γ ⊢[PRAAx] le one Y := GaussianPolynomialPerturbation.power_positive b j hb
  have hv : Γ ⊢[PRAAx] bounded v (fact j*Y) X :=
    inverse_bound _ _ _ hx (positive_product _ _ (factorial_positive j) hy) (original_monomial_lower a b j K hb hj)
  have hu : Γ ⊢[PRAAx] bounded u X Y :=
    bound_congr (radius_power a b j hb).eqSymm (.eqRefl _) (.eqRefl _) (radius_bounded X Y hy)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hy hx) (le_refl one) (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))
    (bounded_product u v X Y (fact j*Y) X hy hx hu hv)

theorem original_finite_exponential_monomial_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 1) ⟶ le (var 2) (var 3) ⟶
      bounded (qmul (power (radiusPoint (var 0) (var 1)) (var 2))
        (reciprocal (scalarSum (radiusPoint (var 0) (var 1)) (var 3)))) (fact (var 2)) one) :=
  closeUniv 4 (.impI (.impI (.impI (finite_monomial_decay _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPositiveExponentialTermBound
