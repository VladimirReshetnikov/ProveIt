import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSqrtBrackets
import IPRADerivations.Geometry.IsoperimetricDyadicSquareRoot

/-!
# The actual dyadic name for the positive square root of five

The finite square-root bracket gives an exact real, positive observation
at every precision. Its original named square equals the constant five.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSqrtFive

open_ipra
open LeanProofs.IPRA.Geometry.IsoperimetricDyadicSquareRoot (index index_bracket index_greatest)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaHalfWallisRate (fraction_distance)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent diagonalEquivalent diagonal_to_cross)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianFastValueCut (exponent query_budget)
open GaussianExponentialReference (unit_monotone)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def clock (p : PTm n) : PTm n := exponent (num 7) p
def root (p : PTm n) : PTm n := index (num 5) one p
def sample (p : PTm n) : PTm n := fraction (root (clock p)) (unit (clock p))
def nameF : PR 2 := PTm.toPR (sample (var 0) : PTm 2)
def nameData : PTm n := zero
def five : PTm n := fraction (num 5) one

theorem sample_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p := by
  simpa [nameF,ap2,sample,root,clock] using toPR_eq (Γ := Γ) (sample (var 0) : PTm 2) ![p,x]

private theorem square_bracket (p : PTm n) : Γ ⊢[PRAAx]
    le (root p*root p) (num 5*(unit p*unit p)) ⋏
      le (num 5*(unit p*unit p)) (succ (root p)*succ (root p)) := by
  have h := index_bracket (Γ := Γ) (num 5) one p (le_refl one)
  exact .andI (le_congr (one_mul _) (.eqRefl _) h.andE₁)
    (le_congr (.eqRefl _) (one_mul _) (le_of_lt h.andE₂))

theorem numerator_bounds (p : PTm n) : Γ ⊢[PRAAx]
    le (two*unit p) (root p) ⋏ le (root p) (num 3*unit p) := by
  refine .andI (index_greatest _ _ _ _ (le_refl one) ?_) ?_
  · change Γ ⊢[PRAAx] le (one*((two*unit p)*(two*unit p))) (num 5*(unit p*unit p))
    ipra_le 𝔞(unit p*unit p)
  · apply nat_sqrt_mono
    exact le_trans (square_bracket p).andE₁ (by ipra_le 4*𝔞(unit p*unit p))

private theorem numerator_compare (p q : PTm n) : Γ ⊢[PRAAx]
    le (root p*unit q) (succ (root q)*unit p) := by
  apply nat_sqrt_mono
  have pBound := (square_bracket (Γ := Γ) p).andE₁
  have qBound := (square_bracket (Γ := Γ) q).andE₂
  ipra_le 𝔞(unit q*unit q)*sl pBound+𝔞(unit p*unit p)*sl qBound

private theorem tentative_distance (p q : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (fraction (root p) (unit p)) (fraction (root q) (unit q))
      (unit p+unit q) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hq : Γ ⊢[PRAAx] le one Q := unit_positive q
  apply fraction_distance _ _ _ _ _ _ hp hq (positive_product P Q hp hq)
  · have h := numerator_compare (Γ := Γ) p q
    ipra_le 𝔞(P*Q)*sl h+𝔞(P*Q*Q)
  · have h := numerator_compare (Γ := Γ) q p
    ipra_le 𝔞(P*Q)*sl h+𝔞(P*P*Q)

theorem observations (p q x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p x) (ap2 nameF q x) (unit p+unit q) (unit p*unit q) := by
  let P := unit (clock p)
  let Q := unit (clock q)
  have hP : Γ ⊢[PRAAx] le (unit p) P := unit_monotone (le_add_right p _)
  have hQ : Γ ⊢[PRAAx] le (unit q) Q := unit_monotone (le_add_right q _)
  have distance := tentative_distance (Γ := Γ) (clock p) (clock q)
  apply distance_congr (sample_at p x).eqSymm (sample_at q x).eqSymm (.eqRefl _) (.eqRefl _)
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive (clock p)) (unit_positive (clock q)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) _ distance
  ipra_le 𝔞(P*unit p)*sl hQ+𝔞(Q*unit q)*sl hP

theorem positive_sample (p x : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (fraction two one)) (fstT (ap2 nameF p x)) := by
  let t := clock p
  let H := unit t
  let j := root t
  have hH : Γ ⊢[PRAAx] le one H := unit_positive t
  have cleared : Γ ⊢[PRAAx] le (H*two) (j*one) :=
    le_congr (mul_comm _ _) (by ipra_ring) (numerator_bounds t).andE₁
  have h := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl one) hH
    (GaussianGammaHalfSqrtBrackets.fraction_first_represents two one (le_refl one))
    (GaussianGammaHalfSqrtBrackets.fraction_first_represents j H hH) cleared
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (congrFst (sample_at p x)).eqSymm h

theorem name_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN nameF x := by
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit] using
    (observations (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0) (Syn.shift (Syn.shift x)))

private theorem rational_square_distance (p : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (fraction (root p*root p) (unit p*unit p)) (five : PTm n) (num 7) (unit p) := by
  let P := unit p
  let j := root p
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have h₁ := (square_bracket (Γ := Γ) p).andE₁
  have h₂ := (square_bracket (Γ := Γ) p).andE₂
  have up := (numerator_bounds (Γ := Γ) p).andE₂
  have deficit : Γ ⊢[PRAAx] le (num 5*(P*P)) (j*j+num 7*P) := by
    ipra_le sl h₂+2*sl up+sl hp
  apply fraction_distance _ _ _ _ _ _ (positive_product P P hp hp) (le_refl _) hp
  · ipra_le 𝔞 P*sl h₁+𝔞(num 7*P*P)
  · ipra_le 𝔞 P*sl deficit

theorem square_observation (p x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF nameF nameF) p (multiplyData nameF nameF x x))
      (ap2 constantF p (five : PTm n)) two (unit p) := by
  let t := exponent (multiplyModulus nameF nameF x x) p
  let k := clock t
  let H := unit k
  let j := root k
  let w := fraction (j*j) (H*H)
  have hH : Γ ⊢[PRAAx] le one H := unit_positive k
  have exactRaw : Γ ⊢[PRAAx] GaussianNameArithmetic.multiplyRaw nameF nameF t x x ≐ w :=
    (GaussianRationalSyntheticDivision.qmul_congr (sample_at t x) (sample_at t x)).eqTrans
      (GaussianEulerDampedTimeRate.fraction_product j H j H hH hH)
  have exactProduct := (GaussianNameArithmetic.multiply_at nameF nameF x x p).eqTrans
    (GaussianNameArithmetic.recode_congr exactRaw)
  have recoded := distance_radius_mono _ _ _ _ zero H (le_refl _) hH (by ipra_le 0) (GaussianFastValueCut.recode_distance w)
  have joined := distance_triangle_same _ _ _ _ _ H hH recoded (rational_square_distance k)
  have later : Γ ⊢[PRAAx] le p t := le_add_right p _
  have paid : Γ ⊢[PRAAx] le (num 7*unit p) H :=
    le_trans (le_mul_mono (le_refl (num 7)) (unit_monotone later))
      (query_budget (num 7) t)
  apply distance_congr exactProduct.eqSymm (constant_at p five).eqSymm (.eqRefl _) (.eqRefl _)
  apply distance_radius_mono _ _ _ _ _ _ hH (unit_positive p) ?_ joined
  ipra_le sl paid+𝔞 H

theorem square_is_five (x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF nameF nameF) constantF (multiplyData nameF nameF x x) (five : PTm n) := by
  have diag : Γ ⊢[PRAAx] diagonalEquivalent (multiplyF nameF nameF) constantF (multiplyData nameF nameF x x) (five : PTm n) := by
    refine .allI ?_
    simpa [diagonalEquivalent,five,Syn.shift] using
      (square_observation (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x))
  exact diagonal_to_cross _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _ (name_regular x) (name_regular x)) (constant_regular _) diag

theorem actual_positive_square_root_five_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    pointCN nameF nameData ⋏
      (crossEquivalent (multiplyF nameF nameF) constantF (multiplyData nameF nameF nameData nameData) five ⋏
        univ 1 (RationalArgmin.rationalLE (fstT (fraction two one)) (fstT (ap2 nameF (var 0) nameData)))) :=
  .andI (name_regular _) (.andI (square_is_five _) (closeUniv 1 (positive_sample _ _)))

end LeanProofs.IPRA.Analysis.GaussianNamedSqrtFive
