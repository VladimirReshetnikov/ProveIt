import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.HigherOrders.GaussianBarnesCanonicalHigherRelative
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeMercatorRemainder
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# Split the original weighted Mercator polynomial into Barnes degrees

The first two terms are the original degree-two Mercator polynomial.
Every remaining term is the corresponding original Barnes coefficient
times the full increment power.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherMercatorSum

open_ipra
open GaussianBarnesCanonicalHigherRows (coefficient previous degree)
open GaussianBarnesCanonicalHigherRelative (term_binding)
open GaussianBarnesCanonicalRelativeStep (source relative)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianFiniteLogarithmPolynomial (sourceTerm source_term_at coefficient_congr)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalFiniteSum (sum sum_index_congr sum_multiply multiply_body_at multiplyBody)
open GaussianRationalHorner (qadd qmul ofGaussian)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBarnesCanonicalRelativeMercatorRemainder.polynomial
local notation "S" => GaussianFiniteLogarithmPolynomial.value
local notation "C" => GaussianFiniteLogarithmPolynomial.coefficient

def data (z h B k : PTm n) : PTm n := pairT (pairT z h) (pairT B k)

def body : PTm 2 :=
  qmul (coefficient (fstT (fstT (var 1))) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0))
    (power (ofGaussian (sndT (fstT (var 1))) (fstT (sndT (var 1)))) (degree (var 0)))

def value (z h B k N : PTm n) : PTm n := sum body N (data z h B k)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (data z h B k) = data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) := by simp [data]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z h B k N : PTm n) :
    Syn.subst σ (value z h B k N) =
      value (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ N) := by simp [value]

theorem body_at (z h B k j : PTm n) : Γ ⊢[PRAAx]
    inst2 body j (data z h B k) ≐ qmul (coefficient z B k j) (power (ofGaussian h B) (degree j)) := by
  let x := data z h B k
  change Γ ⊢[PRAAx] inst2 body j x ≐ _
  have u : Γ ⊢[PRAAx] fstT x ≐ pairT z h := fst_pair _ _
  have v : Γ ⊢[PRAAx] sndT x ≐ pairT B k := snd_pair _ _
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (qmul (coefficient (var 0) (var 2) (var 3) (var 4)) (power (ofGaussian (var 1) (var 2)) (degree (var 4))) : PTm 5)
    (σ := ![fstT (fstT x),sndT (fstT x),fstT (sndT x),sndT (sndT x),j]) (σ' := ![z,h,B,k,j]) (fun p => by
      fin_cases p
      · exact (congrFst u).eqTrans (fst_pair _ _)
      · exact (congrSnd u).eqTrans (snd_pair _ _)
      · exact (congrFst v).eqTrans (fst_pair _ _)
      · exact (congrSnd v).eqTrans (snd_pair _ _)
      · exact .eqRefl j)
  simpa [body,inst2] using e

private theorem weighted_offset_at (z h R B k H j : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx]
      inst2 (multiplyBody (offB sourceTerm)) j (pairT (radiusPoint k one) (pairT two (relative z h B k))) ≐
        inst2 body j (data z h B k) := by
  let w := relative z h B k
  let a := radiusPoint k one
  have idx : Γ ⊢[PRAAx] two+j ≐ previous j := by unfold previous; ipra_ring
  have offset := GaussianRationalFiniteProduct.offset_at (Γ := Γ) sourceTerm two j w
  have terms : Γ ⊢[PRAAx] inst2 sourceTerm (two+j) w ≐ qmul (C (previous j)) (power w (degree j)) := by
    simp only [source_term_at]
    exact qmul_congr (coefficient_congr idx) (congrAp2 powerF (congrSucc idx) (.eqRefl _))
  exact (multiply_body_at (offB sourceTerm) a j (pairT two w)).eqTrans
    ((qmul_congr (.eqRefl _) (offset.eqTrans terms)).eqTrans
      ((term_binding z h R B k H j hs).eqSymm.eqTrans (body_at z h B k j).eqSymm))

theorem weighted_split (z h R B k H N : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qmul (radiusPoint k one) (L (previous N) z h B k) ≐
      qadd (qmul (radiusPoint k one) (S two (relative z h B k))) (value z h B k N) := by
  let v := relative z h B k
  let a := radiusPoint k one
  let t := offB sourceTerm
  let x := pairT two v
  have e : Γ ⊢[PRAAx] previous N ≐ two+N := by unfold previous; ipra_ring
  have split := (sum_index_congr sourceTerm e (.eqRefl v)).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split sourceTerm two N v)
  have tail : Γ ⊢[PRAAx] sum (multiplyBody t) N (pairT a x) ≐ value z h B k N := by
    refine GaussianRationalFiniteSum.sum_congr_bounded
      (multiplyBody t) body N (pairT a x) (data z h B k) (.allI (.impI ?_))
    let sh (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    have sr : Δ ⊢[PRAAx] source (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) := by
      simpa [Δ,Fm.shift,sh,Syn.shift] using hs.shift.wk
    simpa only [Δ,sh,t,a,x,v,Syn.shift,subst_data,GaussianDominantPairAlgebra.subst_radiusPoint,
      GaussianBarnesCanonicalRelativeStep.subst_relative,subst_pairT,one,two,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
        weighted_offset_at (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) (var 0) sr
  exact (qmul_congr (.eqRefl a) split).eqTrans
    ((qmul_add a (S two v) (sum t N x)).eqTrans
      (qadd_congr (.eqRefl _) ((sum_multiply t a N x).eqSymm.eqTrans tail)))

theorem actual_Barnes_weighted_Mercator_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     let N := var 6
     source z h R B k H ⟶
       (qmul (radiusPoint k one) (L (previous N) z h B k) ≐
         qadd (qmul (radiusPoint k one) (S two (relative z h B k))) (value z h B k N))) :=
  closeUniv 7 (.impI (weighted_split _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherMercatorSum
