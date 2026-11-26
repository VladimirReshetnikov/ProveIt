import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianScalarSincTaylorBounds
import IPRADerivations.Analysis.Trigonometry.Sine.GaussianNamedSineTaylor
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds

/-!
# Cofinal sinc samples from the original named sine

Both literal factorial polynomials use the argument and cutoff of the
original sine approximation, at a doubled precision. Exact finite
factorization bounds the sinc samples away from a zero argument, while
the finite quadratic estimate includes zero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSincSamples

open_ipra
open GaussianScalarSincTaylor (sincBody sincTaylor sinc_canonical sine_taylor_factors)
open GaussianScalarSincTaylorBounds (unit_disk_sinc_bound)
open GaussianNamedSineTaylor (argumentPrecision imaginaryF imaginary_input finite_taylor_error)
open GaussianNamedSineFromExponential (sineF sineData sine_regular)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone dyadic_weaken)
open GaussianNameEquivalence (point_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded squaredTolerance qnormSq)
open GaussianRationalLowerBounds (lower)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal normNumerator reciprocal_identity bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRadiusExponentialName (input index inputPrecision bounded_samples_at)
open GaussianReciprocalHorner (qmul_associative)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def clock (p : PTm n) : PTm n := two*succ p
def argumentClock (R p : PTm n) : PTm n := argumentPrecision R (clock p)
def argument (f : PR 2) (R x p : PTm n) : PTm n := ap2 f (argumentClock R p) x
def cutoff (R p : PTm n) : PTm n := index R (clock p)
def value (f : PR 2) (R x p : PTm n) : PTm n := sincTaylor (argument f R x p) (cutoff R p)
def sineValue (f : PR 2) (R x p : PTm n) : PTm n := GaussianNamedSineTaylor.taylorValue f R x (clock p)
def sineBudget (f : PR 2) (R x : PTm n) : PTm n := GaussianNamedSineTaylor.budget f R x
def sineSize (f : PR 2) (R x : PTm n) : PTm n :=
  GaussianNameBounds.U (sineF (imaginaryF f)) (sineData (imaginaryF f) R x)
def sampleSize (f : PR 2) (R x : PTm n) : PTm n := sineSize f R x+sineBudget f R x+two

ipra_subst clock
ipra_subst argumentClock
ipra_subst argument
ipra_subst cutoff
ipra_subst value
ipra_subst sineBudget
ipra_subst sampleSize [sineSize]

theorem clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (clock p) :=
  le_of_eq_add (d := p+two) (by unfold clock; ipra_ring)

theorem clock_mono (p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (clock p) (clock q) := by
  unfold clock
  ipra_le 2*sl hpq

theorem clock_unit (p : PTm n) : Γ ⊢[PRAAx] unit (clock p) ≐ unit (succ p)*unit (succ p) := by
  have e : Γ ⊢[PRAAx] clock p ≐ succ p+succ p := by unfold clock; ipra_ring
  exact (congrAp2 powF e (.eqRefl two)).eqTrans (pw_add two (succ p) (succ p))

theorem next_unit_lower (p : PTm n) : Γ ⊢[PRAAx] le two (unit (succ p)) :=
  le_congr (one_mul two) (pw_succ two p).eqSymm (le_mul_mono (unit_positive p) (le_refl two))

theorem argument_clock_later (R p : PTm n) : Γ ⊢[PRAAx] le (clock p) (argumentClock R p) := by
  unfold argumentClock argumentPrecision inputPrecision GaussianFastValueCut.exponent
  exact le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)

theorem cutoff_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (cutoff R p) := by
  let c := clock p+num 4
  have h : Γ ⊢[PRAAx] le two (GaussianRationalExponentialTail.cutoff R c) :=
    le_of_eq_add (d := R+R+R*(R+R)+c+two)
      (by unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt; ipra_ring)
  exact (succ_monus_succ one (cutoff R p)).eqSymm.eqTrans
    (le_congr (.eqRefl two) (GaussianRationalExponentialTail.last_successor R c).eqSymm h)

theorem value_nonempty (f : PR 2) (R x p : PTm n) :
    Γ ⊢[PRAAx] value f R x p ≐ sincTaylor (argument f R x p) (succ (pred (cutoff R p))) :=
  GaussianRationalFiniteSum.sum_index_congr sincBody
    (RationalIntegerNormalization.positive_form (cutoff_positive R p)) (.eqRefl _)

theorem value_canonical (f : PR 2) (R x p : PTm n) : Γ ⊢[PRAAx] canonical (value f R x p) :=
  sinc_canonical _ _

theorem argument_bound (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (argument f R x p) R one :=
  bounded_samples_at f R x _ h.andE₂

theorem product_at (f : PR 2) (R x p : PTm n) : Γ ⊢[PRAAx]
    qmul (argument f R x p) (value f R x p) ≐ sineValue f R x p :=
  (sine_taylor_factors _ _).eqSymm

theorem sine_sample_error (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (sineF (imaginaryF f)) (clock p) (sineData (imaginaryF f) R x))
      (sineValue f R x p) (sineBudget f R x) (unit (clock p)) :=
  finite_taylor_error f R x (clock p) h

theorem norm_cases (a A B : PTm n) : Γ ⊢[PRAAx] bounded a A B ⋎ lower a A B :=
  RationalArgmin.total (qnormSq a) (squaredTolerance A B)

theorem cancel_factor (a c U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (ha : Γ ⊢[PRAAx] lower a one U) (hc : Γ ⊢[PRAAx] canonical c) :
    Γ ⊢[PRAAx] qmul (reciprocal a) (qmul a c) ≐ c := by
  have low := GaussianRationalLowerBounds.name_lower a one U (le_refl one) hU ha
  have e := (qmul_commutative (Γ := Γ) (reciprocal a) a).eqTrans
    (reciprocal_identity a (GaussianNameReciprocal.lower_norm_positive a U hU low))
  exact (qmul_associative (reciprocal a) a c).eqSymm.eqTrans
    ((qmul_congr e (.eqRefl c)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical c hc))

private theorem sine_value_bound (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (sineValue f R x p) (sineSize f R x+sineBudget f R x) one := by
  let s := clock p
  let E := unit s
  let A := sineSize f R x
  let B := sineBudget f R x
  have hE := unit_positive (Γ := Γ) s
  have hs := sine_regular (imaginaryF f) R x (imaginary_input f R x h)
  have hreg := GaussianNameBounds.sample_bound _ _ s hs
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ B E A one hE (le_refl one)
    (distance_symmetric _ _ _ _ hE (sine_sample_error f R x p h)) hreg
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hE (le_refl one)) (le_refl one)
    (by ipra_le 𝔞 B*sl hE) raw

theorem sample_bound (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (value f R x p) (sampleSize f R x) one := by
  let a := argument f R x p
  let v := value f R x p
  let A := sineSize f R x+sineBudget f R x
  refine .orE (norm_cases a one one) ?_ ?_
  · have b := unit_disk_sinc_bound (Γ := bounded a one one :: Γ) a (pred (cutoff R p)) Prf.hyp0
    have near := bound_congr (value_nonempty f R x p).eqSymm (.eqRefl _) (.eqRefl _) b
    exact bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
      (le_congr (by ipra_ring) (by unfold sampleSize; dsimp only [A]; ipra_ring) (le_add_left two A)) near
  · have inv := GaussianRationalLowerBounds.inverse_bound (Γ := lower a one one :: Γ)
      a one one (le_refl one) (le_refl one) Prf.hyp0
    have prod := bounded_product (reciprocal a) (sineValue f R x p) one one A one
      (le_refl one) (le_refl one) inv (sine_value_bound f R x p h.wk)
    have e : lower a one one :: Γ ⊢[PRAAx] qmul (reciprocal a) (sineValue f R x p) ≐ v :=
      (qmul_congr (.eqRefl _) (product_at f R x p).eqSymm).eqTrans
      (cancel_factor a v one (le_refl one) Prf.hyp0 (value_canonical f R x p))
    exact bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
      (le_congr (by ipra_ring) (by unfold sampleSize; dsimp only [A]; ipra_ring) (le_add_right A two))
      (bound_congr e (one_mul A) (one_mul one) prod)

theorem common_late_distance (f : PR 2) (x p r s : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] le p r) (hs : Γ ⊢[PRAAx] le p s) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f r x) (ap2 f s x) two (unit p) := by
  have order := add_le_add₂ (le_mul_mono (le_refl (unit r)) (unit_monotone hs))
    (le_mul_mono (le_refl (unit s)) (unit_monotone hr))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive r) (unit_positive s))
    (unit_positive p) (le_congr (by ipra_ring) (by ipra_ring) order) (point_at f x r s h)

theorem argument_pair_error (f : PR 2) (R x p q : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (argument f R x p) (argument f R x q) two (unit (clock p)) :=
  common_late_distance f x (clock p) _ _ h.andE₁ (argument_clock_later R p)
    (le_trans (clock_mono p q hpq) (argument_clock_later R q))

theorem sine_pair_error (f : PR 2) (R x p q : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sineValue f R x p) (sineValue f R x q)
      (two*sineBudget f R x+two) (unit (clock p)) := by
  let g := sineF (imaginaryF f)
  let y := sineData (imaginaryF f) R x
  let P := clock p
  let Q := clock q
  have hPQ := clock_mono p q hpq
  have hU := unit_positive (Γ := Γ) P
  have left := distance_symmetric _ _ _ _ hU (sine_sample_error f R x p h)
  have middle := common_late_distance g y P P Q (sine_regular _ _ _ (imaginary_input f R x h)) (le_refl P) hPQ
  have right := dyadic_weaken _ _ _ P Q hPQ (sine_sample_error f R x q h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU (distance_triangle_same _ _ _ _ _ _ hU left middle) right)

end LeanProofs.IPRA.Analysis.GaussianNamedSincSamples
