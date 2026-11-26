import IPRADerivations.Analysis.Names.GaussianNamedSqrtFive
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartCorrectedImage

/-!
# The named positive solution of x²=x+1

The observations are the exact fractions obtained by adding one to the
observations of the independent dyadic square-root name and dividing by
two. The finite square-root bracket pays for the residual in the actual
named quadratic identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatio

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedSqrtFive (clock root)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaHalfSqrtBrackets (fraction_gap fraction_first_represents)
open GaussianGammaHalfWallisRate (fraction_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianNameEquivalence (crossEquivalent)
open LeanProofs.IPRA.Geometry.IsoperimetricDyadicSquareRoot (index_bracket)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def numerator (p : PTm n) : PTm n := unit (clock p)+root (clock p)
def denominator (p : PTm n) : PTm n := two*unit (clock p)
def sample (p : PTm n) : PTm n := fraction (numerator p) (denominator p)
def nameF : PR 2 := PTm.toPR (sample (var 0) : PTm 2)
def nameData : PTm n := zero
def onePoint : PTm n := fraction one one

theorem sample_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p := by
  simpa [nameF,ap2,sample,numerator,denominator,clock,root] using
    toPR_eq (Γ := Γ) (sample (var 0) : PTm 2) ![p,x]

theorem denominator_positive (p : PTm n) : Γ ⊢[PRAAx] le one (denominator p) :=
  positive_product _ _ (le_succ_self one) (unit_positive (clock p))

theorem sample_positive (p x : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (fraction (num 3) two)) (fstT (ap2 nameF p x)) := by
  have clear : Γ ⊢[PRAAx] le (denominator p*num 3) (numerator p*two) := by
    unfold numerator denominator
    ipra_le 2*sl (GaussianNamedSqrtFive.numerator_bounds (Γ := Γ) (clock p)).andE₁
  have h := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_succ_self one) (denominator_positive p)
    (fraction_first_represents (num 3) two (le_succ_self one))
    (fraction_first_represents _ _ (denominator_positive p)) clear
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (congrFst (sample_at p x)).eqSymm h

theorem observations (p q x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p x) (ap2 nameF q x) (unit p+unit q) (unit p*unit q) := by
  let P := unit (clock p)
  let Q := unit (clock q)
  let j := root (clock p)
  let l := root (clock q)
  let M := unit p+unit q
  let D := unit p*unit q
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive p) (unit_positive q)
  have sqrt_dist := distance_congr (Γ := Γ) (GaussianNamedSqrtFive.sample_at p x) (GaussianNamedSqrtFive.sample_at q x)
    (.eqRefl _) (.eqRefl _) (GaussianNamedSqrtFive.observations p q x)
  have gap := fraction_gap j P l Q M D (unit_positive _) (unit_positive _) hD sqrt_dist
  apply distance_congr (sample_at p x).eqSymm (sample_at q x).eqSymm (.eqRefl _) (.eqRefl _)
  apply fraction_distance _ _ _ _ _ _ (denominator_positive p) (denominator_positive q) hD
  · change Γ ⊢[PRAAx] le (D*((P+j)*(two*Q))) (D*((Q+l)*(two*P))+M*(two*P)*(two*Q))
    ipra_le 2*sl gap.andE₁+𝔞(two*M*P*Q)
  · change Γ ⊢[PRAAx] le (D*((Q+l)*(two*P))) (D*((P+j)*(two*Q))+M*(two*Q)*(two*P))
    ipra_le 2*sl gap.andE₂+𝔞(two*M*P*Q)

theorem name_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN nameF x := by
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit] using
    (observations (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0) (Syn.shift (Syn.shift x)))

private theorem bracket_error (t : PTm n) : Γ ⊢[PRAAx]
    le (root t*root t) (num 5*(unit t*unit t)) ⋏ le (num 5*(unit t*unit t)) (root t*root t+num 7*unit t) := by
  have base := index_bracket (Γ := Γ) (num 5) one t (le_refl one)
  have upper : Γ ⊢[PRAAx] le (num 5*(unit t*unit t)) (succ (root t)*succ (root t)) :=
    le_congr (.eqRefl _) (one_mul _) (le_of_lt base.andE₂)
  have j := (GaussianNamedSqrtFive.numerator_bounds (Γ := Γ) t).andE₂
  exact .andI (le_congr (one_mul _) (.eqRefl _) base.andE₁)
    (by ipra_le sl upper+2*sl j+sl (unit_positive (Γ := Γ) t))

theorem raw_quadratic (p x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (qmul (ap2 nameF p x) (ap2 nameF p x)) (qadd (ap2 nameF p x) (onePoint : PTm n))
      one (unit p) := by
  let t := clock p
  let P := unit t
  let j := root t
  let A := P+j
  let D := two*P
  let W := unit p
  have hD : Γ ⊢[PRAAx] le one D := denominator_positive p
  have hDD := positive_product D D hD hD
  have rightOne : Γ ⊢[PRAAx] D*one ≐ D := (mul_comm D one).eqTrans (one_mul D)
  have sumNum : Γ ⊢[PRAAx] A*one+one*D ≐ A+D := by ipra_ring
  have squareEq := (GaussianRationalSyntheticDivision.qmul_congr (sample_at p x) (sample_at p x)).eqTrans
    (GaussianEulerDampedTimeRate.fraction_product A D A D hD hD)
  have sumEq := (GaussianRationalSyntheticDivision.qadd_congr (sample_at p x) (.eqRefl onePoint)).eqTrans
    ((GaussianEulerPositivePowerChartCorrectedImage.fraction_sum A D one one hD (le_refl one)).eqTrans
      (GaussianEulerPositivePowerChartJacobian.fraction_congr sumNum rightOne))
  have h₇ : Γ ⊢[PRAAx] le (num 7*W) P := GaussianFastValueCut.query_budget (num 7) p
  have hI : Γ ⊢[PRAAx] le (j*j) (num 5*(P*P)) ⋏ le (num 5*(P*P)) (j*j+num 7*P) :=
    bracket_error t
  apply distance_congr squareEq.eqSymm sumEq.eqSymm (.eqRefl _) (.eqRefl _)
  apply fraction_distance _ _ _ _ _ _ hDD hD (unit_positive p)
  · change Γ ⊢[PRAAx] le (W*((A*A)*D)) (W*((A+D)*(D*D))+one*(D*D)*D)
    dsimp only [A,D]
    ipra_le 𝔞(W*two*P)*sl hI.andE₁+𝔞(num 8*P*P*P)
  · change Γ ⊢[PRAAx] le (W*((A+D)*(D*D))) (W*((A*A)*D)+one*D*(D*D))
    dsimp only [A,D]
    ipra_le 𝔞(W*two*P)*sl hI.andE₂+𝔞(two*P*P)*sl h₇+𝔞(num 6*P*P*P)

def quadraticAllowance (x : PTm n) : PTm n := (multiplyModulus nameF nameF x x+one)+one+(two+one)

theorem quadratic_observation (p x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF nameF nameF) p (multiplyData nameF nameF x x))
      (ap2 (addF nameF constantF) p (addData x (onePoint : PTm n))) (quadraticAllowance x) (unit p) := by
  let v := ap2 nameF p x
  have hU : Γ ⊢[PRAAx] le one (unit p) := unit_positive p
  have reg := name_regular (Γ := Γ) x
  have first := GaussianNameRingLaws.multiply_sample_error nameF nameF x x p reg reg
  have sum := GaussianNameRingLaws.add_sample_error nameF constantF x (onePoint : PTm n) p reg (constant_regular _)
  have second := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl v)
    (constant_at p onePoint)) (.eqRefl _) (.eqRefl _) sum
  have h := distance_triangle_same _ _ _ _ _ _ hU first (raw_quadratic p x)
  exact distance_triangle_same _ _ _ _ _ _ hU h (distance_symmetric _ _ _ _ hU second)

theorem quadratic_identity (x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF nameF nameF) (addF nameF constantF)
      (multiplyData nameF nameF x x) (addData x (onePoint : PTm n)) := by
  have reg := name_regular (Γ := Γ) x
  have diag : Γ ⊢[PRAAx] diagonalRate (multiplyF nameF nameF) (addF nameF constantF)
      (multiplyData nameF nameF x x) (addData x (onePoint : PTm n)) (quadraticAllowance x) := by
    refine .allI ?_
    simpa [diagonalRate,quadraticAllowance,onePoint,Syn.shift] using
      (quadratic_observation (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x))
  exact cross_of_diagonal_rate _ _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _ reg reg)
    (GaussianNameArithmetic.add_fast _ _ _ _ reg (constant_regular _)) diag

theorem actual_named_golden_ratio_quadratic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    pointCN nameF nameData ⋏
      (crossEquivalent (multiplyF nameF nameF) (addF nameF constantF)
        (multiplyData nameF nameF nameData nameData) (addData nameData onePoint) ⋏
      univ 1 (RationalArgmin.rationalLE (fstT (fraction (num 3) two)) (fstT (ap2 nameF (var 0) nameData)))) :=
  .andI (name_regular _) (.andI (quadratic_identity _) (closeUniv 1 (sample_positive _ _)))

end LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatio
