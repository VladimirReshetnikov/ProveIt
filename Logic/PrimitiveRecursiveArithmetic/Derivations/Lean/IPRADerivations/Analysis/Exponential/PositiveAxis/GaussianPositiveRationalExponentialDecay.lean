import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialTermBound
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialInverse
import IPRADerivations.Analysis.Names.Arithmetic.GaussianBoundedInverseApartness
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# A monomial times the negative exponential at a positive rational

The original positive exponential observations include the requested
factorial term at every precision. Reciprocating the actual observations
gives a named inverse with the exact weighted bound `j!`.
The original independently clocked negative exponential is this inverse,
so its own weighted observations have only the explicit dyadic slack.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalExponentialDecay

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded radius_power radius_multiply radius_congr)
open GaussianPositiveExponentialTermBound (original_monomial_lower finite_monomial_decay)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalReciprocal (power reciprocal bound_congr bounded_sum)
open GaussianRationalLowerBounds (lower lower_congr)
open GaussianRationalHorner (qmul qmul_canonical)
open GaussianRationalMetric (bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_diagonal_at)
open GaussianNameRingLaws (negativeF negativeData oneF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ subst_zero subst_succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def expF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def negF : PR 2 := GaussianRadiusExponentialName.nameF (negativeF constantF)
def expData (a b j : PTm n) : PTm n := GaussianRadiusExponentialName.data (a+j) (radiusPoint a b)
def negData (a b j : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (a+j) (negativeData (radiusPoint a b))
def inverseData (a b j : PTm n) : PTm n := GaussianNameReciprocal.nameData zero (expData a b j)

theorem input_bound (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (radiusPoint a b) (a+j) one := by
  have bound : Γ ⊢[PRAAx] le a ((a+j)*b) :=
    le_trans (le_add_right _ _) (le_congr (one_mul _)
      (mul_comm _ _) (mul_le_mul_right (a+j) hb))
  exact bounded_radius_mono _ _ _ _ _ hb (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) bound) (radius_bounded a b hb)

theorem actual_positive_input (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF (a+j) (radiusPoint a b) := by
  refine .andI (constant_regular _) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by
    simpa [Fm.shift, Syn.shift, one] using hb.shift
  have raw := bound_congr (constant_at (var 0) (radiusPoint (Syn.shift a) (Syn.shift b))).eqSymm
    (.eqRefl _) (.eqRefl _) (input_bound (Syn.shift a) (Syn.shift b) (Syn.shift j) hs)
  simpa only [GaussianRadiusExponentialName.boundedSamples, Syn.shift, GaussianDominantPairAlgebra.subst_radiusPoint,
    PTm.subst_add, one, subst_succ, subst_zero] using raw

theorem degree_in_cutoff (a j p : PTm n) :
    Γ ⊢[PRAAx] le j (GaussianRadiusExponentialName.index (a+j) p) := by
  let R := a+j
  let K := GaussianRadiusExponentialName.index R p
  have covers : Γ ⊢[PRAAx] le (succ R) (GaussianRationalExponentialTail.cutoff R (p+num 4)) := by
    unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le 𝔞 R+2*𝔞 R*𝔞 R+𝔞 p+7
  have hs : Γ ⊢[PRAAx] le (succ R) (succ K) := le_congr (.eqRefl _)
    (GaussianRationalExponentialTail.last_successor R (p+num 4)).eqSymm covers
  exact le_trans (le_add_left j a) ((succ_monus_succ R K).eqSymm.eqTrans hs)

theorem positive_sample_at (a b j p : PTm n) : Γ ⊢[PRAAx]
    ap2 expF p (expData a b j) ≐ scalarSum (radiusPoint a b) (GaussianRadiusExponentialName.index (a+j) p) :=
  (GaussianRadiusExponentialName.sample_at constantF (a+j) p (radiusPoint a b)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _)
      (constant_at (GaussianRadiusExponentialName.inputPrecision (a+j) p) (radiusPoint a b)))

theorem positive_apart (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart expF zero (expData a b j) := by
  let p := GaussianNameReciprocal.anchor (zero : PTm n)
  let K := GaussianRadiusExponentialName.index (a+j) p
  have first := original_monomial_lower a b zero K hb (zero_le K)
  have e : Γ ⊢[PRAAx] fact (zero : PTm n)*pw b zero ≐ one :=
    (congrMul (fact_zero zero) (pw_zero b)).eqTrans (one_mul one)
  have low : Γ ⊢[PRAAx] lower (ap2 expF p (expData a b j)) one one :=
    lower_congr (positive_sample_at a b j p).eqSymm (pw_zero a) e first
  exact GaussianNameReciprocal.lower_congr (.eqRefl _) (pw_zero two).eqSymm low

theorem named_negative_is_reciprocal (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameReciprocal.nameF expF) negF (inverseData a b j) (negData a b j) := by
  let x := radiusPoint a b
  let R := a+j
  let f := expData a b j
  let g := negData a b j
  have hi := actual_positive_input a b j hb
  have hn := GaussianExponentialInverse.negative_input constantF R x hi
  have product : Γ ⊢[PRAAx] crossEquivalent (multiplyF expF negF) oneF (multiplyData expF negF f g) x :=
    GaussianExponentialInverse.exponential_inverse constantF R x hi
  have product' := cross_trans (multiplyF expF negF) oneF oneF (multiplyData expF negF f g) x f
    product (GaussianBoundedInverseApartness.ones_equivalent x f)
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse expF negF zero f g
    (GaussianRadiusExponentialName.name_regular constantF R x hi)
    (GaussianRadiusExponentialName.name_regular (negativeF constantF) R (negativeData x) hn)
    (positive_apart a b j hb) product'

def inverseQuery (p : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus zero) p+GaussianNameReciprocal.anchor zero

theorem inverse_sample_at (a b j p : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianNameReciprocal.nameF expF) p (inverseData a b j) ≐
      reciprocal (scalarSum (radiusPoint a b) (GaussianRadiusExponentialName.index (a+j) (inverseQuery p))) := by
  let q := scalarSum (radiusPoint a b) (GaussianRadiusExponentialName.index (a+j) (inverseQuery p))
  let v := reciprocal q
  have e := GaussianNameReciprocal.reciprocal_congr (positive_sample_at (Γ := Γ) a b j (inverseQuery p))
  have code : Γ ⊢[PRAAx] GaussianFastValueCut.recode v ≐ v :=
    GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical v)
      (GaussianRationalReciprocal.reciprocal_canonical q) (GaussianRationalL1.raw_den_positive v)
      (GaussianFastValueCut.recode_represents v) (GaussianRationalL1.raw_represents v)
  exact (GaussianNameReciprocal.name_at expF zero (expData a b j) p).eqTrans
    ((GaussianNameArithmetic.recode_congr e).eqTrans code)

theorem exact_reciprocal_weighted_decay (a b j p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (qmul (power (radiusPoint a b) j) (ap2 (GaussianNameReciprocal.nameF expF) p (inverseData a b j)))
      (fact j) one :=
  bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (inverse_sample_at a b j p)).eqSymm
    (.eqRefl _) (.eqRefl _) (finite_monomial_decay a b j _ ha hb (degree_in_cutoff a j (inverseQuery p)))

theorem original_negative_weighted_decay (a b j p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (qmul (power (radiusPoint a b) j) (ap2 negF p (negData a b j)))
      (fact j*unit p+two*pw a j) (unit p) := by
  let w := power (radiusPoint a b) j
  let x := ap2 negF p (negData a b j)
  let y := ap2 (GaussianNameReciprocal.nameF expF) p (inverseData a b j)
  have eq := cross_symm _ _ _ _ (named_negative_is_reciprocal a b j hb)
  have d := cross_diagonal_at p eq
  have den := GaussianPolynomialPerturbation.power_positive b j hb
  have raw := radius_bounded (pw a j) (pw b j) den
  have wBound : Γ ⊢[PRAAx] bounded w (pw a j) one :=
    bound_congr (radius_power a b j hb).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_radius_mono _ _ _ _ _ den (le_refl one)
        (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right (pw a j) den)) raw)
  have near := GaussianApproximateInverseDistance.multiply_distance w x y (pw a j) two (unit p)
    (unit_positive p) wBound d
  have sum := bounded_sum (qmul w y) _ (fact j) one (pw a j*two) (unit p)
    (le_refl one) (unit_positive p) (exact_reciprocal_weighted_decay a b j p ha hb) near
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right (qmul w y) (qmul w x) (qmul_canonical w x))
    (by ipra_ring) (one_mul _) sum

theorem original_negative_rational_exponential_monomial_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 1) ⟶
      bounded (qmul (power (radiusPoint (var 0) (var 1)) (var 2))
        (ap2 negF (var 3) (negData (var 0) (var 1) (var 2))))
        (fact (var 2)*unit (var 3)+two*pw (var 0) (var 2)) (unit (var 3))) :=
  closeUniv 4 (.impI (.impI (original_negative_weighted_decay _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem doubled_monomial (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] power (radiusPoint (two*a) b) j ≐ qmul (radiusPoint (unit j) one) (power (radiusPoint a b) j) := by
  have hB := GaussianPolynomialPerturbation.power_positive b j hb
  have prod := (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (radius_power a b j hb)).eqTrans
    ((radius_multiply (unit j) one (pw a j) (pw b j) (le_refl one) hB).eqTrans
      (radius_congr (.eqRefl _) (one_mul _)))
  have e := AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) two a j
  exact (radius_power (two*a) b j hb).eqTrans ((radius_congr e (.eqRefl _)).eqTrans prod.eqSymm)

theorem original_half_exponential_monomial_bound (a b j p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (qmul (power (radiusPoint (two*a) b) j) (ap2 negF p (negData a b j)))
      (unit j*fact j*unit p+two*unit j*pw a j) (unit p) := by
  let A := radiusPoint (unit j) one
  let w := power (radiusPoint a b) j
  let x := ap2 negF p (negData a b j)
  have exactProduct : Γ ⊢[PRAAx] qmul (power (radiusPoint (two*a) b) j) x ≐ qmul A (qmul w x) :=
    (GaussianRationalSyntheticDivision.qmul_congr (doubled_monomial a b j hb) (.eqRefl x)).eqTrans
      (GaussianReciprocalHorner.qmul_associative A w x)
  exact bound_congr exactProduct.eqSymm (by ipra_ring) (one_mul _)
    (GaussianRationalReciprocal.bounded_product A (qmul w x) (unit j) one
      (fact j*unit p+two*pw a j) (unit p) (le_refl one) (unit_positive p)
      (radius_bounded (unit j) one (le_refl one)) (original_negative_weighted_decay a b j p ha hb))

theorem original_half_exponential_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 1) ⟶
      bounded (qmul (power (radiusPoint (two*var 0) (var 1)) (var 2))
        (ap2 negF (var 3) (negData (var 0) (var 1) (var 2))))
        (unit (var 2)*fact (var 2)*unit (var 3)+two*unit (var 2)*pw (var 0) (var 2)) (unit (var 3))) :=
  closeUniv 4 (.impI (.impI (original_half_exponential_monomial_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalExponentialDecay
