import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Names.GaussianNameConjugation
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff

/-!
# Actual exponentials of differences with equal exponential names

Original exponential addition, replacement in original multiplication
and the actual negative-exponential inverse identify exp(f-g) with one.
The genuine negative of that same difference program also exponentiates
to one. Every original input radius and operation clock is retained,
including radius zero. No real-valuedness or injectivity is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedExponentialDifferenceIdentity

open_ipra
open GaussianRadiusExponentialName (input nameF data name_regular)
open GaussianNameRingLaws (negativeF negativeData oneF one_fast one_at)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qone qsub_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def differenceF (f g : PR 2) : PR 2 := GaussianNamedDifference.nameF f g
def differenceData (x y : PTm n) : PTm n := GaussianNamedDifference.data x y
def exponentialData (R x y : PTm n) : PTm n := data (R+R) (differenceData x y)
def negativeExponentialData (R x y : PTm n) : PTm n := data (R+R) (negativeData (differenceData x y))

ipra_subst differenceData
ipra_subst exponentialData
ipra_subst negativeExponentialData

theorem difference_input (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y) : Γ ⊢[PRAAx]
    input (differenceF f g) (R+R) (differenceData x y) :=
  GaussianExponentialReference.add_input f (negativeF g) R x (negativeData y) hf
    (GaussianExponentialInverse.negative_input g R y hg)

theorem difference_exponential_regular (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y) : Γ ⊢[PRAAx]
    pointCN (nameF (differenceF f g)) (exponentialData R x y) :=
  name_regular _ _ _ (difference_input f g R x y hf hg)

theorem difference_exponential_one (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (differenceF f g)) oneF (exponentialData R x y) y := by
  have hn := GaussianExponentialInverse.negative_input g R y hg
  have hd := difference_input f g R x y hf hg
  have addition := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent f (negativeF g) (differenceF f g)
    R R (R+R) x (negativeData y) (differenceData x y) hf hn hd (cross_refl _ _ hd.andE₁)
  have nf := name_regular f R x hf
  have ng := name_regular g R y hg
  have nn := name_regular (negativeF g) R (negativeData y) hn
  have replace := GaussianGammaAdjacentCutoff.multiply_cross (nameF f) (nameF g)
    (nameF (negativeF g)) (nameF (negativeF g)) (data R x) (data R y) (data R (negativeData y)) (data R (negativeData y))
    nf ng nn nn he (cross_refl _ _ nn)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ addition)
    (cross_trans _ _ _ _ _ _ replace (GaussianExponentialInverse.exponential_inverse g R y hg))

theorem ones_equivalent (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF oneF x y := by
  apply GaussianNameConjugation.equal_samples_cross oneF oneF x y (one_fast x) (one_fast y)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
    (one_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)).eqTrans (one_at (var 0) (Syn.shift y)).eqSymm

theorem negative_exponential_of_one (f : PR 2) (R x anchor : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data R x) anchor) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (negativeF f)) oneF (data R (negativeData x)) anchor := by
  let F := nameF f
  let G := nameF (negativeF f)
  let u := data R x
  let v := data R (negativeData x)
  have hn := GaussianExponentialInverse.negative_input f R x hf
  have ng := name_regular (negativeF f) R (negativeData x) hn
  have replacement := GaussianGammaAdjacentCutoff.multiply_cross F oneF G G u v v v
    (name_regular f R x hf) (one_fast v) ng ng
    (cross_trans _ _ _ _ _ _ he (ones_equivalent anchor v)) (cross_refl _ _ ng)
  have reduce := cross_trans _ _ _ _ _ _ replacement (GaussianNameRingLaws.multiply_one_left G v ng)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ reduce)
    (cross_trans _ _ _ _ _ _ (GaussianExponentialInverse.exponential_inverse f R x hf) (ones_equivalent x anchor))

theorem negative_difference_exponential_one (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (negativeF (differenceF f g))) oneF (negativeExponentialData R x y) y :=
  negative_exponential_of_one (differenceF f g) (R+R) (differenceData x y) y
    (difference_input f g R x y hf hg) (difference_exponential_one f g R x y hf hg he)

theorem both_difference_exponentials_one (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (differenceF f g)) oneF (exponentialData R x y) y ⋏
      crossEquivalent (nameF (negativeF (differenceF f g))) oneF (negativeExponentialData R x y) y :=
  .andI (difference_exponential_one f g R x y hf hg he) (negative_difference_exponential_one f g R x y hf hg he)

/-- Only the auxiliary observation of the literal one program is
removed; the original requested exponential observation is unchanged. -/
theorem observation_of_one_cross (f : PR 2) (x anchor p : PTm n)
    (he : Γ ⊢[PRAAx] crossEquivalent f oneF x anchor) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) qone one (unit p) := by
  let z := qsub (ap2 f p x) qone
  let q := GaussianRationalSlackRemoval.precision z one (unit p) one
  apply GaussianRationalSlackRemoval.slack_removal_at z one (unit p) one (unit_positive p)
  change Γ ⊢[PRAAx] bounded z (one*unit q+one*unit p) (unit p*unit q)
  have near := cross_at f oneF x anchor p q he
  exact GaussianRationalReciprocal.bound_congr
    (qsub_congr (.eqRefl _) (one_at q anchor)) (by ipra_ring) (.eqRefl _) near

theorem difference_exponential_observation (f g : PR 2) (R x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF (differenceF f g)) p (exponentialData R x y)) qone one (unit p) :=
  observation_of_one_cross _ _ y p (difference_exponential_one f g R x y hf hg he)

theorem negative_difference_exponential_observation (f g : PR 2) (R x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF (negativeF (differenceF f g))) p (negativeExponentialData R x y)) qone one (unit p) :=
  observation_of_one_cross _ _ y p (negative_difference_exponential_one f g R x y hf hg he)

theorem actual_original_equal_exponentials_difference_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((input f (var 0) (var 1) ⋏ (input g (var 0) (var 2) ⋏
      crossEquivalent (nameF f) (nameF g) (data (var 0) (var 1)) (data (var 0) (var 2)))) ⟶
        crossEquivalent (nameF (differenceF f g)) oneF (exponentialData (var 0) (var 1) (var 2)) (var 2) ⋏
          crossEquivalent (nameF (negativeF (differenceF f g))) oneF
            (negativeExponentialData (var 0) (var 1) (var 2)) (var 2)) :=
  closeUniv 3 (.impI (both_difference_exponentials_one f g _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_original_equal_exponentials_difference_observations_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((input f (var 0) (var 1) ⋏ (input g (var 0) (var 2) ⋏
      crossEquivalent (nameF f) (nameF g) (data (var 0) (var 1)) (data (var 0) (var 2)))) ⟶
        distanceBounded (ap2 (nameF (differenceF f g)) (var 3) (exponentialData (var 0) (var 1) (var 2))) qone one (unit (var 3)) ⋏
          distanceBounded (ap2 (nameF (negativeF (differenceF f g))) (var 3) (negativeExponentialData (var 0) (var 1) (var 2))) qone one (unit (var 3))) :=
  closeUniv 4 (.impI (.andI
    (difference_exponential_observation f g _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (negative_difference_exponential_observation f g _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedExponentialDifferenceIdentity
