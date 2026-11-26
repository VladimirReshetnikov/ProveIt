import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate

/-!
# Independent rates for original named rational quotients

Endpoint rates are carried through the original difference and product
programs. The common nonzero increment has reciprocal bounded by its
encoding denominator, so the endpoint rate is amplified by that bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotientRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianNameBounds (U sample_bound subst_U)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedDifferenceQuotient (nameF data inverse separated inverse_bound)
open GaussianNamedDifferenceRate (source leadingNumerator leadingDenominator rate_parameters_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem quotient_rate (F G H K : PR 2) (x y u v h D A B C E : PTm n)
    (hs : Γ ⊢[PRAAx] separated h D) (hr : Γ ⊢[PRAAx] source F G H K x y u v A B C E) :
    Γ ⊢[PRAAx] independentRate (nameF F G) (nameF H K) (data F G x y h D) (data H K u v h D)
      (D*leadingNumerator A B C E) (leadingDenominator B E) := by
  let J := GaussianNamedDifference.nameF F G
  let L := GaussianNamedDifference.nameF H K
  let X := GaussianNamedDifference.data x y
  let Y := GaussianNamedDifference.data u v
  let c := inverse h D
  let N := leadingNumerator A B C E
  let W := leadingDenominator B E
  let R := U J X
  have hJ : Γ ⊢[PRAAx] pointCN J X :=
    GaussianNamedDifference.name_regular F G x y hr.andE₂.andE₁.andE₁ hr.andE₂.andE₁.andE₂
  have hL : Γ ⊢[PRAAx] pointCN L Y :=
    GaussianNamedDifference.name_regular H K u v hr.andE₂.andE₂.andE₁.andE₁ hr.andE₂.andE₂.andE₁.andE₂
  have hc := constant_regular (Γ := Γ) c
  have hW := GaussianNamedDifferenceRate.denominator_positive B E hr.andE₁.andE₁ hr.andE₁.andE₂
  have jc : Γ ⊢[PRAAx] sampleBound J X R := by
    refine .allI ?_
    have hJs : Γ.map Fm.shift ⊢[PRAAx] pointCN J (Syn.shift X) :=
      by simpa only [Fm.shift,Syn.shift,GaussianEuclideanDistanceName.subst_pointCN] using hJ.shift
    change Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 J (var 0) (Syn.shift X)) (Syn.shift R) one
    rw [show Syn.shift R = U J (Syn.shift X) from subst_U _ J X]
    exact sample_bound J (Syn.shift X) (var 0) hJs
  have cc : Γ ⊢[PRAAx] sampleBound constantF c D := by
    refine .allI ?_
    have hcBound : Γ ⊢[PRAAx] bounded c D one := inverse_bound h D hs
    have base := hcBound.shift
    have bs : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalMetric.bounded (Syn.shift c) (Syn.shift D) one := by
      simpa only [Fm.shift,Syn.shift,GaussianRationalMetric.subst_bounded,one,PTm.subst_succ,PTm.subst_zero] using base
    exact bound_congr (constant_at (var 0) (Syn.shift c)).eqSymm (.eqRefl _) (.eqRefl _) bs
  have diff : Γ ⊢[PRAAx] independentRate J L X Y N W :=
    GaussianNamedDifferenceRate.original_rate F G H K x y u v A B C E hr
  have product := GaussianNamedMultiplyRate.independent_rate constantF J constantF L c X c Y
    zero one N W R D (le_refl _) hW hc hJ hc hL jc cc (GaussianNamedDifferenceRate.self_rate constantF c hc) diff
  change Γ ⊢[PRAAx] independentRate (multiplyF constantF J) (multiplyF constantF L)
    (multiplyData constantF J c X) (multiplyData constantF L c Y) (D*N) W
  exact rate_parameters_congr (multiplyF constantF J) (multiplyF constantF L)
    (multiplyData constantF J c X) (multiplyData constantF L c Y)
    (GaussianNamedMultiplyRate.leadingNumerator zero one N W R D)
    (GaussianNamedMultiplyRate.leadingDenominator one W) (D*N) W
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) product

end LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotientRate
