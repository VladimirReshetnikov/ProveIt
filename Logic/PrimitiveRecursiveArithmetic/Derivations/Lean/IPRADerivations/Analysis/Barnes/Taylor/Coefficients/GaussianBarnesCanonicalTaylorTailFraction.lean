import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeTail
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherTail
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFiniteProperness

/-!
# Exact fraction independence of the Barnes Taylor tail rows

Equal Gaussian rational points give equal base reciprocals at each
positive row. The original second and higher coefficient programs
therefore agree exactly, including their finite sums at fixed cutoffs.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorTailFraction

open_ipra
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalFiniteProperness (scaled_fraction_equal)
open GaussianBarnesCanonicalHigherRows (coefficient degree)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (qnegative)
open GaussianRationalReciprocal (power reciprocal)
open GaussianRationalSyntheticDivision (qone qadd_congr qsub_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem reciprocal_equal (z w B D k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hk : Γ ⊢[PRAAx] le one k) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] reciprocal (base z B k) ≐ reciprocal (base w D k) := by
  have same : Γ ⊢[PRAAx] base z B k ≐ base w D k :=
    qadd_congr (.eqRefl qone) (scaled_fraction_equal z w B D k hB hD hk he)
  ipra_congr (reciprocal (var 0) : PTm 1) with [same]

theorem second_row_equal (z w B D k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hk : Γ ⊢[PRAAx] le one k) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalSecondDerivativeRow.value z B k ≐
      GaussianBarnesCanonicalSecondDerivativeRow.value w D k := by
  have same := reciprocal_equal z w B D k hB hD hk he
  exact qmul_congr (.eqRefl _) (qsub_congr (.eqRefl _) (qmul_congr same same))

theorem higher_row_equal (z w B D k j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hk : Γ ⊢[PRAAx] le one k) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] coefficient z B k j ≐ coefficient w D k j := by
  have same := reciprocal_equal z w B D k hB hD hk he
  ipra_congr (GaussianRationalHorner.qmul (qnegative (power (qnegative (var 0)) (var 1))) (var 2) : PTm 3)
    with [same, .eqRefl (degree j), .eqRefl (GaussianDominantPairAlgebra.radiusPoint one (GaussianBarnesCanonicalHigherRows.coefficientDenominator k j))]
    using [coefficient,GaussianBarnesCanonicalHigherRows.signedPower]

theorem second_tail_equal (z w B D N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalSecondDerivativeTail.value z B N r ≐
      GaussianBarnesCanonicalSecondDerivativeTail.value w D N r := by
  let body := GaussianBarnesCanonicalSecondDerivativeTail.body
  apply GaussianRationalFiniteSum.sum_congr_bounded body body r
    (GaussianBarnesCanonicalSecondDerivativeTail.data z B N) (GaussianBarnesCanonicalSecondDerivativeTail.data w D N)
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hB.shift.wk
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hD.shift.wk
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.wk
  have same := second_row_equal (sh z) (sh w) (sh B) (sh D) (succ (sh N+i)) hb hd (zero_lt_succ _) eq
  simpa only [termsEqual,body,GaussianBarnesCanonicalSecondDerivativeTail.subst_data,Syn.shift,sh,Δ,i] using
    (GaussianBarnesCanonicalSecondDerivativeTail.body_at (sh z) (sh B) (sh N) i).eqTrans
      (same.eqTrans (GaussianBarnesCanonicalSecondDerivativeTail.body_at (sh w) (sh D) (sh N) i).eqSymm)

theorem higher_tail_equal (z w B D N j r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalHigherTail.value z B N j r ≐
      GaussianBarnesCanonicalHigherTail.value w D N j r := by
  let body := GaussianBarnesCanonicalHigherTail.body
  apply GaussianRationalFiniteSum.sum_congr_bounded body body r
    (GaussianBarnesCanonicalHigherTail.data z B N j) (GaussianBarnesCanonicalHigherTail.data w D N j)
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hB.shift.wk
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hD.shift.wk
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.wk
  have same := higher_row_equal (sh z) (sh w) (sh B) (sh D) (succ (sh N+i)) (sh j) hb hd (zero_lt_succ _) eq
  simpa only [termsEqual,body,GaussianBarnesCanonicalHigherTail.subst_data,Syn.shift,sh,Δ,i] using
    (GaussianBarnesCanonicalHigherTail.body_at (sh z) (sh B) (sh N) (sh j) i).eqTrans
      (same.eqTrans (GaussianBarnesCanonicalHigherTail.body_at (sh w) (sh D) (sh N) (sh j) i).eqSymm)

theorem actual_Barnes_finite_Taylor_tail_fraction_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let w := var 1
     let B := var 2
     let D := var 3
     let N := var 4
     let j := var 5
     let r := var 6
     (le one B ⋏ (le one D ⋏ (ofGaussian z B ≐ ofGaussian w D))) ⟶
       ((GaussianBarnesCanonicalSecondDerivativeTail.value z B N r ≐ GaussianBarnesCanonicalSecondDerivativeTail.value w D N r) ⋏
        (GaussianBarnesCanonicalHigherTail.value z B N j r ≐ GaussianBarnesCanonicalHigherTail.value w D N j r))) :=
  closeUniv 7 (.impI (.andI
    (second_tail_equal _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (higher_tail_equal _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorTailFraction
