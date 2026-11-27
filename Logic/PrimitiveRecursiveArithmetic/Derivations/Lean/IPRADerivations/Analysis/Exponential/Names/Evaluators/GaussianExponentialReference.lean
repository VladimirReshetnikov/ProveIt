import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianRadiusExponentialName
import IPRADerivations.Analysis.Exponential.FiniteSeries.GaussianScalarExponentialProductTail
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic
import IPRADerivations.Analysis.Names.GaussianNameEquivalence

/-!
# Common finite references for actual Gaussian exponential names

At each original output observation, a later input query and a larger
finite cutoff give the same one-unit dyadic accuracy. The input change
is estimated at the earlier cutoff. The remaining terms then use the
original uniform scalar tail. This permits independent clocks to be
synchronized for the product law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialReference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (qadd qmul canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRadiusExponentialName (input index inputPrecision sample sample_at value query_bound
  boundedSamples bounded_samples_at precision_budget commonDenominator)
open GaussianRationalExponentialTail (cutoff lastIndex last_successor precisionDenominator precision_positive)
open GaussianRationalRadiusExponentialLipschitz (factor)
open GaussianScalarExponentialProductTail (rectangleCutoff reserve growthExponent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem unit_monotone {s t : PTm n} (h : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx] le (unit s) (unit t) :=
  GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) h

theorem dyadic_weaken (a b A s t : PTm n) (hst : Γ ⊢[PRAAx] le s t)
    (h : Γ ⊢[PRAAx] distanceBounded a b A (unit t)) : Γ ⊢[PRAAx] distanceBounded a b A (unit s) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive t) (unit_positive s)
    (mul_le_mul_left A (unit_monotone hst)) h

theorem later_query (f : PR 2) (R x p j : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hj : Γ ⊢[PRAAx] le (inputPrecision R p) j) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum (ap2 f j x) (index R p)) (value f R p x) one (commonDenominator p) := by
  let i := inputPrecision R p
  let I := unit i
  let C := commonDenominator p
  let d := factor R (index R p)
  have dist : Γ ⊢[PRAAx] distanceBounded (ap2 f j x) (ap2 f i x) two I :=
    GaussianNameEquivalence.point_at_later f x i j h.andE₁ hj
  have raw := GaussianRationalRadiusExponentialLipschitz.scalar_sum_lipschitz
    (ap2 f j x) (ap2 f i x) R two I (index R p) (unit_positive i)
    (bounded_samples_at f R x j h.andE₂) (query_bound f R x p h) dist
  have budget : Γ ⊢[PRAAx] le ((d*two)*C) (one*I) := by
    have eq := natEq (pw_succ (Γ := Γ) two p)
    apply le_congr ?_ (one_mul I).eqSymm (precision_budget R p)
    apply deriveNat
    unfold C commonDenominator unit d
    ipra_simps
    rw [eq]
    ring
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive i) (unit_positive (succ p)) budget raw

theorem later_cutoff (q R p K : PTm n) (h : Γ ⊢[PRAAx] bounded q R one)
    (hK : Γ ⊢[PRAAx] le (index R p) K) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum q K) (scalarSum q (index R p)) one (commonDenominator p) := by
  have raw := GaussianRationalExponentialTail.scalar_cutoff_distance q R (p+num 4) (monus K (index R p)) h
  have eq := GaussianRationalFiniteSum.sum_index_congr (Γ := Γ) scalarBody (congrSucc (eq_add_of_le hK)).eqSymm (.eqRefl q)
  have grow : Γ ⊢[PRAAx] le (commonDenominator p) (precisionDenominator (p+num 4)) :=
    unit_monotone (le_of_eq_add (d := num 6) (by ipra_ring))
  exact distance_radius_mono _ _ _ _ _ _ (precision_positive _) (unit_positive (succ p))
    (le_congr (by ipra_ring) (by ipra_ring) grow)
    (distance_congr eq (.eqRefl _) (.eqRefl _) (.eqRefl _) raw)

theorem finite_reference (f : PR 2) (R x p j K : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hj : Γ ⊢[PRAAx] le (inputPrecision R p) j) (hK : Γ ⊢[PRAAx] le (index R p) K) :
    Γ ⊢[PRAAx] distanceBounded (scalarSum (ap2 f j x) K) (sample f R p x) one (unit p) := by
  have combined := distance_triangle_same _ _ _ _ _ _ (unit_positive (succ p))
    (later_cutoff (ap2 f j x) R p K (bounded_samples_at f R x j h.andE₂) hK)
    (later_query f R x p j h hj)
  have budget : Γ ⊢[PRAAx] le ((one+one)*unit p) (one*commonDenominator p) := by
    refine le_of_eq_add (d := zero) ?_
    have e := natEq (pw_succ (Γ := Γ) two p)
    apply deriveNat
    unfold commonDenominator unit
    ipra_simps
    rw [e]
    ring
  exact distance_congr (.eqRefl _) (sample_at f R p x).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive (succ p)) (unit_positive p) budget combined)

theorem recode_fixed (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) :
    Γ ⊢[PRAAx] GaussianFastValueCut.recode q ≐ q :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical _) hq
    (raw_den_positive _) (GaussianFastValueCut.recode_represents _) (raw_represents _)

theorem add_sample (f g : PR 2) (x y p : PTm n) :
    Γ ⊢[PRAAx] ap2 (GaussianNameArithmetic.addF f g) p (GaussianNameArithmetic.addData x y) ≐
      qadd (ap2 f (GaussianFastValueCut.exponent two p) x) (ap2 g (GaussianFastValueCut.exponent two p) y) :=
  (GaussianNameArithmetic.add_at f g x y p).eqTrans (recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))

theorem add_input (f g : PR 2) (R x y : PTm n) (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y) :
    Γ ⊢[PRAAx] input (GaussianNameArithmetic.addF f g) (R+R) (GaussianNameArithmetic.addData x y) := by
  refine .andI (GaussianNameArithmetic.add_fast f g x y hf.andE₁ hg.andE₁) (.allI ?_)
  let r := Syn.shift R
  let a := Syn.shift x
  let b := Syn.shift y
  let j := GaussianFastValueCut.exponent two (var 0 : PTm (n+1))
  have ha : Γ.map Fm.shift ⊢[PRAAx] boundedSamples f r a := by simpa [r,a,Fm.shift,Syn.shift] using hf.andE₂.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] boundedSamples g r b := by simpa [r,b,Fm.shift,Syn.shift] using hg.andE₂.shift
  have d := GaussianRationalReciprocal.bounded_sum (ap2 f j a) (ap2 g j b) r one r one (le_refl _) (le_refl _)
    (bounded_samples_at f r a j ha) (bounded_samples_at g r b j hb)
  have q : Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 (GaussianNameArithmetic.addF f g) (var 0)
      (GaussianNameArithmetic.addData a b)) (r+r) one :=
    bound_congr (add_sample f g a b (var 0)).eqSymm (by ipra_ring) (one_mul _) d
  simpa only [boundedSamples,GaussianNameArithmetic.subst_addData,PTm.subst_add,Syn.shift,r,a,b] using q

theorem index_below_rectangle (R D p t : PTm n) (hD : Γ ⊢[PRAAx] le D (R+R))
    (hp : Γ ⊢[PRAAx] le p t) : Γ ⊢[PRAAx] le (index D p) (rectangleCutoff R t) := by
  have first : Γ ⊢[PRAAx] le (index D p) (cutoff D (p+num 4)) :=
    le_congr (.eqRefl _) (last_successor D (p+num 4)) (le_succ_self _)
  apply le_trans first
  unfold cutoff ExponentialTail.Nt rectangleCutoff reserve growthExponent
  ipra_le 2*sl hD+2*sl hD*𝔟 (D+(R+R))+sl hp+
    24*𝔟 R*𝔟 R+28*𝔟 R+15*𝔟 t+632

theorem original_finite_exponential_reference_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input f (var 0) (var 1) ⟶ le (inputPrecision (var 0) (var 2)) (var 3) ⟶
      le (index (var 0) (var 2)) (var 4) ⟶ distanceBounded (scalarSum (ap2 f (var 3) (var 1)) (var 4))
        (sample f (var 0) (var 2) (var 1)) one (unit (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (finite_reference f _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_rectangle_index_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (var 0+var 0) ⟶ le (var 2) (var 3) ⟶ le (index (var 1) (var 2)) (rectangleCutoff (var 0) (var 3))) :=
  closeUniv 4 (.impI (.impI (index_below_rectangle _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianExponentialReference
