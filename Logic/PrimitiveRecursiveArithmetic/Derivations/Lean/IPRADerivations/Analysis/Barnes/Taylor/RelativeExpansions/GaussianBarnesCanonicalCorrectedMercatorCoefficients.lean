import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalCorrectedMercator
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherMercatorSum
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalQuadraticBinding

/-!
# Exact coefficient order of the original corrected Barnes row polynomial

The constant term vanishes. The first two nonconstant terms use
the original derivative rows. The remaining finite sum uses the
original general-degree coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (zeroCode)
open GaussianBarnesCanonicalCorrectedMercator (polynomial correctionDelta)
open GaussianBarnesCanonicalDerivativeAlgebra (linearTerm)
open GaussianBarnesCanonicalHigherRows (coefficient previous degree)
open GaussianBarnesCanonicalRelativeStep (source relative)
open GaussianBarnesCanonicalQuadraticBinding (secondTerm low_terms)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalHorner (qzero qadd qmul ofGaussian ofGaussian_canonical ofGaussian_represents zero_represents canonical_unique)
open GaussianRationalReciprocal (power powerF power_succ)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_left qmul_zero_right qzero_canonical qzero_add)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "higher" => GaussianBarnesCanonicalHigherMercatorSum.value
local notation "logValue" => GaussianFiniteLogarithmPolynomial.value

theorem coefficient_split (z h R B k H N : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) : Γ ⊢[PRAAx]
    polynomial (previous N) z h B k ≐ qadd (qadd (linearTerm z h B k) (secondTerm z h B k)) (higher z h B k N) := by
  let a := qmul (radiusPoint k one) (logValue two (relative z h B k))
  let b := higher z h B k N
  let c := correctionDelta z h B k
  have swap : Γ ⊢[PRAAx] qadd (qadd a b) c ≐ qadd (qadd a c) b :=
    (qadd_associative a b c).eqTrans
      ((qadd_congr (.eqRefl a) (qadd_commutative b c)).eqTrans (qadd_associative a c b).eqSymm)
  exact (qadd_congr (GaussianBarnesCanonicalHigherMercatorSum.weighted_split z h R B k H N hs) (.eqRefl c)).eqTrans
    (swap.eqTrans (qadd_congr (low_terms z h R B k H hs) (.eqRefl b)))

private theorem zero_fraction (B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian zeroCode B ≐ qzero :=
  canonical_unique _ _ zeroCode B (ofGaussian_canonical _ _ hb) qzero_canonical hb
    (ofGaussian_represents _ _ hb) (zero_represents B)

private theorem zero_power (B j : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] power (ofGaussian zeroCode B) (ConciseIPRA.PTm.succ j) ≐ qzero :=
  (congrAp2 powerF (.eqRefl _) (zero_fraction B hb)).eqTrans
    ((power_succ qzero j).eqTrans (qmul_zero_right _))

private theorem zero_higher (z B k N : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] higher z zeroCode B k N ≐ qzero := by
  let t := GaussianBarnesCanonicalHigherMercatorSum.body
  let X := GaussianBarnesCanonicalHigherMercatorSum.data z zeroCode B k
  refine GaussianRationalMatrixFiniteSums.sum_zero_of_terms t N X (.allI (.impI ?_))
  let s (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
  have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Syn.shift,Fm.shift,one] using hb.shift.wk
  have atZero := (GaussianBarnesCanonicalHigherMercatorSum.body_at (Γ := Δ) (s z) zeroCode (s B) (s k) (var 0)).eqTrans
    ((qmul_congr (.eqRefl _) (zero_power (s B) (previous (var 0)) bs)).eqTrans (qmul_zero_right _))
  simpa only [t,X,Δ,s,Syn.shift,GaussianBarnesCanonicalHigherMercatorSum.subst_data,
    ComplexLogarithmRemainder.subst_zeroCode] using atZero

theorem zero_increment (z R B k H N : PTm n) (hs : Γ ⊢[PRAAx] source z zeroCode R B k H) :
    Γ ⊢[PRAAx] polynomial (previous N) z zeroCode B k ≐ qzero := by
  have hb := hs.andE₁.andE₁
  have lin : Γ ⊢[PRAAx] linearTerm z zeroCode B k ≐ qzero :=
    (qmul_congr (zero_fraction B hb) (.eqRefl _)).eqTrans (qmul_zero_left _)
  have quad : Γ ⊢[PRAAx] secondTerm z zeroCode B k ≐ qzero :=
    (qmul_congr (.eqRefl _) (zero_power B one hb)).eqTrans (qmul_zero_right _)
  exact (coefficient_split z zeroCode R B k H N hs).eqTrans
    ((qadd_congr ((qadd_congr lin quad).eqTrans (qzero_add qzero qzero_canonical))
      (zero_higher z B k N hb)).eqTrans (qadd_zero_right qzero qzero_canonical))

theorem actual_Barnes_corrected_Mercator_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     let N := var 6
     source z h R B k H ⟶
       (polynomial (previous N) z h B k ≐ qadd (qadd (linearTerm z h B k) (secondTerm z h B k)) (higher z h B k N))) :=
  closeUniv 7 (.impI (coefficient_split _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorCoefficients
