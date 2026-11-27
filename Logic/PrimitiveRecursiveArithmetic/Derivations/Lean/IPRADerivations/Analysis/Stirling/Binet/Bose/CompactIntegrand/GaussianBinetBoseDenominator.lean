import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.GaussianBinetBoseExponential
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialAffineLower
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedFiniteProductApartness

/-!
# Apartness of the original Bose denominator

At a positive rational time the original subtraction `exp(2πt)−1`
reads back as the literal Taylor gap at a later clock. The first-order
term gives a uniform margin and an explicit reciprocal certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseDenominator

open_ipra
open GaussianBinetBoseExponential (scaleF scaleData expData expF expRadius exp_regular scale_positive scale_lower_order)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent)
open GaussianNameRingLaws (negativeF negativeData negative_at oneF one_at)
open GaussianNamedDifference (name_regular)
open GaussianRationalLowerBounds (lower lower_congr name_lower)
open GaussianRationalMetric (qsub qnegative qsub_canonical qnegative_canonical)
open GaussianRationalSyntheticDivision (qone qadd_congr qsub_congr qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nameF : PR 2 := GaussianNamedDifference.nameF expF oneF
def data (A B : PTm n) : PTm n := GaussianNamedDifference.data (expData false A B) zero
def sampleClock (p : PTm n) : PTm n := exponent two p

def reciprocalF : PR 2 := GaussianNameReciprocal.nameF nameF
def reciprocalData (A B : PTm n) : PTm n := GaussianNameReciprocal.nameData B (data A B)

ipra_subst data

ipra_subst reciprocalData

theorem regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  name_regular expF oneF (expData false A B) zero (exp_regular false A B hB)
    (GaussianNameRingLaws.one_fast zero)

private theorem negative_one_at (p : PTm n) :
    Γ ⊢[PRAAx] ap2 (negativeF oneF) p (negativeData zero) ≐ qnegative qone := by
  have raw := (negative_at (Γ := Γ) oneF zero p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qsub_canonical _ _))
  exact raw.eqTrans ((qsub_congr (.eqRefl _) (one_at _ _)).eqTrans
    (qzero_add _ (qnegative_canonical _)))

theorem sample_at (p A B : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data A B) ≐ qsub (ap2 expF (sampleClock p) (expData false A B)) qone :=
  (GaussianExponentialReference.add_sample expF (negativeF oneF) (expData false A B) (negativeData zero) p).eqTrans
    (qadd_congr (.eqRefl _) (negative_one_at (sampleClock p)))

theorem observation_lower (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data A B)) (num 4*A) B := by
  let r := sampleClock p
  let R := expRadius A
  let t := GaussianRadiusExponentialName.inputPrecision R r
  let q := ap2 scaleF t (scaleData false A B)
  let K := GaussianRadiusExponentialName.index R r
  have s := scale_positive t A B hB
  have k : Γ ⊢[PRAAx] le one K := GaussianPositiveExponentialSeparation.original_cutoff_positive R r
  have l := GaussianExponentialAffineLower.finite_gap_lower q K (num 4*A) B s.andE₁ s.andE₂ k hB
    (scale_lower_order t A B hB)
  have read := (sample_at (Γ := Γ) p A B).eqTrans
    (qsub_congr (GaussianRadiusExponentialName.sample_at scaleF R r (scaleData false A B)) (.eqRefl _))
  exact lower_congr read.eqSymm (.eqRefl _) (.eqRefl _) l

theorem apart (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart nameF B (data A B) := by
  let p := GaussianNameReciprocal.anchor B
  let s := ap2 nameF p (data A B)
  have h := name_lower s (num 4*A) B
    (GaussianRationalHorner.positive_product _ _ (by ipra_le 3) hA) hB (observation_lower p A B hB)
  have grow : Γ ⊢[PRAAx] le B (unit B) := le_trans (le_succ_self B) (RationalClosure.succ_le_two_pow B)
  exact GaussianNamedFiniteProductApartness.weaken_margin s B (unit B) hB grow h

theorem reciprocal_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN reciprocalF (reciprocalData A B) :=
  GaussianNameReciprocal.name_fast _ _ _ (regular A B hB) (apart A B hA hB)

theorem actual_Binet_Bose_denominator_and_reciprocal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 0) ⋏ le one (var 1)) ⟶
      GaussianNameReciprocal.apart nameF (var 1) (data (var 0) (var 1)) ⋏
        pointCN reciprocalF (reciprocalData (var 0) (var 1))) :=
  closeUniv 2 (.impI (.andI (apart _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (reciprocal_regular _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseDenominator
