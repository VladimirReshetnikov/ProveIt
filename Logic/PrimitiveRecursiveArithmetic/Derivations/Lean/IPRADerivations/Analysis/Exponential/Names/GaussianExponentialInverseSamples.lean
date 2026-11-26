import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponentialSample
import IPRADerivations.Analysis.FiniteOperations.GaussianBoundedInverseApartness
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance

/-!
# Exact inverse rational samples for a bounded named exponential

A late observation of the original positive exponential has a certified
rational reciprocal. Powering this pair gives joint approximations to
the original positive and negative exponentials at every bounded natural
multiple of the input.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace LeanProofs.IPRA.Analysis.GaussianExponentialInverseSamples

open_ipra
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianBoundedIntegerExponentialSample (prefix_error sampleBudget stage_input one_cross)
open GaussianBoundedIntegerExponentialStages (scaledF stageData radius point majorant power_bound)
open GaussianBoundedInverseApartness (anchor_apart productError raw_product_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialInverse (negative_input exponential_inverse)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianNameRingLaws (negativeF negativeData oneF)
open GaussianRadiusExponentialName (input nameF data name_regular)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qmul canonical qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (power_product qmul_commutative)
open GaussianRationalReciprocal (power qone bound_congr power_canonical reciprocal_canonical)
open GaussianRationalRoundedPower (qone_power)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def disk (R : PTm n) : PTm n := pw (num 3) R
def height (f : PR 2) (R x : PTm n) : PTm n :=
  GaussianBoundedInverseApartness.height (nameF f) (nameF (negativeF f)) (data R x) (data R (negativeData x)) (disk R)
def positive (f : PR 2) (p R x : PTm n) : PTm n := GaussianNameReciprocal.tail (nameF f) (height f R x) (data R x) p
def negative (f : PR 2) (p R x : PTm n) : PTm n := GaussianNameReciprocal.raw (nameF f) (height f R x) (data R x) p
def inverseDisk (f : PR 2) (R x : PTm n) : PTm n := GaussianNameReciprocal.R (height f R x)

ipra_subst disk
ipra_subst height
ipra_subst positive [GaussianNameReciprocal.tail]
ipra_subst negative [GaussianNameReciprocal.raw, GaussianNameReciprocal.tail]
ipra_subst inverseDisk

theorem disk_positive (R : PTm n) : Γ ⊢[PRAAx] le one (disk R) :=
  AnalyticNumberTheory.BlockChain.one_le_pw' (le_of_eq_add (d := two) (by ipra_ring)) R

theorem sample_disk (f : PR 2) (R p x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (data R x)) (disk R) one :=
  bound_congr (GaussianRadiusExponentialName.sample_at f R p x).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _ (GaussianRadiusExponentialName.query_bound f R x p h))

private theorem sample_disks (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] smallSamples (nameF f) (data R x) (disk R) one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [smallSamples,Syn.shift,GaussianRadiusExponentialName.subst_data,subst_disk,one,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
    sample_disk f (Syn.shift R) (var 0) (Syn.shift x) hs

private theorem inverse_cross (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameArithmetic.multiplyF (nameF f) (nameF (negativeF f))) oneF
      (GaussianNameArithmetic.multiplyData (nameF f) (nameF (negativeF f)) (data R x) (data R (negativeData x))) (data R x) := by
  change Γ ⊢[PRAAx] crossEquivalent (GaussianExponentialInverse.productF f) oneF
    (GaussianExponentialInverse.productData f R x) (data R x)
  exact cross_trans _ _ _ _ _ _ (exponential_inverse f R x h) (GaussianBoundedInverseApartness.ones_equivalent x (data R x))

private theorem apart (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart (nameF f) (height f R x) (data R x) := by
  have hn := negative_input f R x h
  exact anchor_apart (nameF f) (nameF (negativeF f)) (data R x) (data R (negativeData x)) (disk R)
    (disk_positive R) (name_regular f R x h) (name_regular (negativeF f) R (negativeData x) hn)
    (sample_disks (negativeF f) R (negativeData x) hn) (inverse_cross f R x h)

theorem exact_pair (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] qmul (positive f p R x) (negative f p R x) ≐ qone :=
  GaussianNameReciprocal.tail_inverse_identity _ _ _ _ (name_regular f R x h) (apart f R x h)

theorem positive_canonical (f : PR 2) (p R x : PTm n) : Γ ⊢[PRAAx] canonical (positive f p R x) :=
  GaussianRadiusExponentialName.sample_canonical f R (p+GaussianNameReciprocal.anchor (height f R x)) x

theorem negative_canonical (f : PR 2) (p R x : PTm n) : Γ ⊢[PRAAx] canonical (negative f p R x) :=
  reciprocal_canonical _

theorem positive_bound (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (positive f p R x) (disk R) one :=
  sample_disk f R _ x h

theorem negative_bound (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (negative f p R x) (inverseDisk f R x) one :=
  GaussianNameReciprocal.raw_bound _ _ _ _ (name_regular f R x h) (apart f R x h)

theorem positive_sample (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data R x)) (positive f p R x) two (unit p) :=
  GaussianNameReciprocal.tail_sample_distance (nameF f) (height f R x) (data R x) p (name_regular f R x h)

theorem inverse_power (A B i : PTm n) (h : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qmul (power A i) (power B i) ≐ qone :=
  (power_product A B i).eqSymm.eqTrans
    ((congrAp2 GaussianRationalReciprocal.powerF (.eqRefl i) h).eqTrans (qone_power i))

/-- Recover the error of an inverse sample by multiplying by its exact
inverse partner. The scaled exponential never needs a second reciprocal. -/
theorem inverse_error (P N a b C D E K U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hN : Γ ⊢[PRAAx] canonical N) (hb : Γ ⊢[PRAAx] canonical b)
    (hC : Γ ⊢[PRAAx] bounded N C one) (hD : Γ ⊢[PRAAx] bounded b D one)
    (hP : Γ ⊢[PRAAx] distanceBounded P a E U)
    (hProduct : Γ ⊢[PRAAx] distanceBounded (qmul P N) qone K U)
    (hInverse : Γ ⊢[PRAAx] qmul a b ≐ qone) :
    Γ ⊢[PRAAx] distanceBounded N b (D*(C*E+K)) U := by
  have aN : Γ ⊢[PRAAx] distanceBounded (qmul a N) (qmul P N) (C*E) U :=
    distance_congr (qmul_commutative a N).eqSymm (qmul_commutative P N).eqSymm (.eqRefl _) (.eqRefl _)
      (multiply_distance N a P C E U hU hC (distance_symmetric _ _ _ _ hU hP))
  have eq : Γ ⊢[PRAAx] qmul b (qmul a N) ≐ N :=
    (qmul_associative b a N).eqSymm.eqTrans
      ((qmul_congr ((qmul_commutative b a).eqTrans hInverse) (.eqRefl _)).eqTrans
        ((qmul_commutative qone N).eqTrans (qmul_one_right N hN)))
  exact distance_congr eq (qmul_one_right b hb) (.eqRefl _) (.eqRefl _)
    (multiply_distance b _ _ D (C*E+K) U hU hD (distance_triangle_same _ _ _ _ _ _ hU aN hProduct))

def baseNegativeRadius (f : PR 2) (R x : PTm n) : PTm n := inverseDisk f R x*
  (disk R*two+productError (nameF f) (nameF (negativeF f)) (data R x) (data R (negativeData x)))

ipra_subst baseNegativeRadius [two, one]

theorem negative_sample (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF (negativeF f)) p (data R (negativeData x)))
      (negative f p R x) (baseNegativeRadius f R x) (unit p) := by
  have hn := negative_input f R x h
  have prod := raw_product_at (nameF f) (nameF (negativeF f)) (data R x) (data R (negativeData x)) p
    (name_regular f R x h) (name_regular (negativeF f) R (negativeData x) hn) (inverse_cross f R x h)
  exact inverse_error _ _ _ _ (disk R) (inverseDisk f R x) two _ (unit p) (unit_positive p)
    (GaussianRadiusExponentialName.sample_canonical (negativeF f) R p (negativeData x)) (negative_canonical f p R x)
    (sample_disk (negativeF f) R p (negativeData x) hn) (negative_bound f p R x h) (positive_sample f p R x h)
    prod (exact_pair f p R x h)

def positiveRadius (E i R : PTm n) : PTm n := sampleBudget E i R (disk R) (num 4)
def negativeRadius (f : PR 2) (E i R x : PTm n) : PTm n :=
  GaussianBoundedIntegerExponentialStages.powerBudget E (inverseDisk f R x)*
    (disk (radius E R)*positiveRadius E i R+
      productError (nameF (scaledF f)) (nameF (negativeF (scaledF f))) (data (radius E R) (stageData E i x))
        (data (radius E R) (negativeData (stageData E i x))))

ipra_subst positiveRadius

ipra_subst negativeRadius

theorem positive_power (f : PR 2) (p E i R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hi : Γ ⊢[PRAAx] le i E)
    (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (point f p E i R x) (power (positive f p R x) i) (positiveRadius E i R) (unit p) := by
  let A := positive f p R x
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have base0 := cross_at _ _ _ _ p p (one_cross f E R x h hE)
  have base1 := distance_radius_mono _ _ _ _ two u (GaussianRationalHorner.positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by ipra_ring)) base0
  have base2 := positive_sample f p R x h
  have base : Γ ⊢[PRAAx] distanceBounded (point f p E one R x) A (num 4) u :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hu base1 base2)
  exact prefix_error f p E i R x A (disk R) (num 4) h (positive_bound f p R x h) base hi

theorem negative_power (f : PR 2) (p E i R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hi : Γ ⊢[PRAAx] le i E)
    (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (nameF (negativeF (scaledF f))) p (data (radius E R) (negativeData (stageData E i x))))
      (power (negative f p R x) i) (negativeRadius f E i R x) (unit p) := by
  let G := scaledF f
  let S := radius E R
  let X := stageData E i x
  let B := negative f p R x
  have hh := stage_input f E i R x h hi
  have hn := negative_input G S X hh
  have prod := raw_product_at (nameF G) (nameF (negativeF G)) (data S X) (data S (negativeData X)) p
    (name_regular G S X hh) (name_regular (negativeF G) S (negativeData X) hn) (inverse_cross G S X hh)
  exact inverse_error (point f p E i R x) (ap2 (nameF (negativeF G)) p (data S (negativeData X)))
    (power (positive f p R x) i) (power B i) (disk S) (GaussianBoundedIntegerExponentialStages.powerBudget E (inverseDisk f R x))
    (positiveRadius E i R) _ (unit p) (unit_positive p) (GaussianRadiusExponentialName.sample_canonical (negativeF G) S p (negativeData X))
    (power_canonical B i) (sample_disk (negativeF G) S p (negativeData X) hn) (power_bound B _ E i (negative_bound f p R x h) hi)
    (positive_power f p E i R x h hi hE) prod (inverse_power _ _ _ (exact_pair f p R x h))

end LeanProofs.IPRA.Analysis.GaussianExponentialInverseSamples
