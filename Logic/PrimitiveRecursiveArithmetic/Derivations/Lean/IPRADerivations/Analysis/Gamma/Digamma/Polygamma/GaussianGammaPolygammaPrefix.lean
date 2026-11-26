import IPRADerivations.Analysis.Gamma.Digamma.Polygamma.GaussianGammaPolygammaTail
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# The exact signed polygamma partial sums

The zero-index term is included explicitly. Splitting the original finite
buffer at any cutoff gives precisely the original C30 tail at that cutoff,
with the same sign and factorial scalars on both buffers.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPolygammaPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianGammaPolygammaTail (body data tail signedTail signed_C30_tail_bound term_at)
open GaussianGammaPolygammaTailRows (term)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalFiniteSum (sum termsEqual)
open GaussianRationalHorner (qmul qadd qadd_canonical qmul_canonical)
open GaussianRationalMetric (qnegative qsub distanceBounded)
open GaussianRationalReciprocal (power qone)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)
open Products (fact)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scale (m x : PTm n) : PTm n := qmul (power (qnegative qone) (succ m)) (qmul (radiusPoint (fact m) one) x)
def partialSum (z B m N : PTm n) : PTm n :=
  qadd (scale m (term z B zero (succ m))) (signedTail z B m zero N)

@[simp] theorem subst_signedTail {l : ℕ} (σ : Fin n → PTm l) (z B m N r : PTm n) :
    Syn.subst σ (signedTail z B m N r) =
      signedTail (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [signedTail]

@[simp] theorem subst_scale {l : ℕ} (σ : Fin n → PTm l) (m x : PTm n) :
    Syn.subst σ (scale m x) = scale (Syn.subst σ m) (Syn.subst σ x) := by
  simp [scale,Products.fact,one]

@[simp] theorem subst_partialSum {l : ℕ} (σ : Fin n → PTm l) (z B m N : PTm n) :
    Syn.subst σ (partialSum z B m N) = partialSum (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ N) := by
  simp [partialSum]

theorem partial_sum_canonical (z B m N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (partialSum z B m N) :=
  qadd_canonical _ _

private theorem scale_congr (m : PTm n) {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] scale m x ≐ scale m y :=
  qmul_congr (.eqRefl _) (qmul_congr (.eqRefl _) h)

private theorem scale_add (m x y : PTm n) : Γ ⊢[PRAAx] scale m (qadd x y) ≐ qadd (scale m x) (scale m y) :=
  (qmul_congr (.eqRefl _) (GaussianRationalCoefficientScaling.qmul_add _ _ _)).eqTrans
    (GaussianRationalCoefficientScaling.qmul_add _ _ _)

private theorem term_index_congr (z B e j k : PTm n) (he : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] term z B j e ≐ term z B k e := by
  simpa only [GaussianGammaPolygammaTailRows.subst_term,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (term (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![z,B,j,e]) (σ' := ![z,B,k,e])
      (fun i => by
        fin_cases i
        · exact .eqRefl _
        · exact .eqRefl _
        · exact he
        · exact .eqRefl _)

theorem raw_tail_split (z B e N r : PTm n) : Γ ⊢[PRAAx]
    tail z B e zero (N+r) ≐ qadd (tail z B e zero N) (tail z B e N r) := by
  let x := data z B e zero
  have rows : Γ ⊢[PRAAx] termsEqual (offB body) body r (pairT N x) (data z B e N) := by
    refine .allI (.impI ?_)
    let Z := Syn.shift z
    let C := Syn.shift B
    let E := Syn.shift e
    let M := Syn.shift N
    let i : PTm (n+1) := var 0
    have offset := offset_at (Γ := lt i (Syn.shift r) :: Γ.map Fm.shift) body M i (data Z C E zero)
    have row := (term_at (Γ := lt i (Syn.shift r) :: Γ.map Fm.shift) (M+i) Z C E zero).eqTrans
      ((term_index_congr Z C E (succ (zero+(M+i))) (succ (M+i)) (congrSucc (zero_add _))).eqTrans
        (term_at i Z C E M).eqSymm)
    simpa only [Syn.shift,GaussianGammaPolygammaTail.subst_data,subst_pairT,ConciseIPRA.PTm.subst_zero,Z,C,E,M,i,x] using
      offset.eqTrans row
  have rest := GaussianRationalFiniteSum.sum_congr_bounded (offB body) body (m := r) (x := pairT N x) (y := data z B e N) rows
  exact (GaussianRationalMatrixFiniteSums.sum_split (Γ := Γ) body N r x).eqTrans
    (qadd_congr (.eqRefl _) rest)

theorem split_partial_sum (z B m N r : PTm n) : Γ ⊢[PRAAx]
    partialSum z B m (N+r) ≐ qadd (partialSum z B m N) (signedTail z B m N r) := by
  let a := scale m (term z B zero (succ m))
  let b := signedTail z B m zero N
  let c := signedTail z B m N r
  have e := (scale_congr m (raw_tail_split (Γ := Γ) z B (succ m) N r)).eqTrans (scale_add m _ _)
  exact (qadd_congr (.eqRefl a) e).eqTrans (GaussianRationalSumAlgebra.qadd_associative a b c).eqSymm

theorem partial_sum_gap (z R B m N r : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] distanceBounded (partialSum z B m (N+r)) (partialSum z B m N)
      (fact (pred m)*pw two (succ m)) (pw N m) := by
  have e := (qsub_congr (split_partial_sum (Γ := Γ) z B m N r) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (qmul_canonical _ _))
  exact GaussianRationalReciprocal.bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (signed_C30_tail_bound z R B m N r hB hz hm hN hR)

end LeanProofs.IPRA.Analysis.GaussianGammaPolygammaPrefix
