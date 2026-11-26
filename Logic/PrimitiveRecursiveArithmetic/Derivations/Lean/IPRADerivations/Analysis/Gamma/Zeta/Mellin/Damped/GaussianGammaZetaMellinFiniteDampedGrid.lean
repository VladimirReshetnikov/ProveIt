import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteDampedEvaluator
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinDampedStrip

/-!
# Exact agreement of the finite damped evaluator and the transposed strip

Transpose the actual time-by-decay-index matrix. Every entry is read
from the original positive-scale Euler evaluator at the same clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at field0 field1 field2 field3 field4 field5
  field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianFastValueCut (exponent)
open GaussianGammaZetaMellinDampedStrip (dampedBody dampedValue damped_index_at)
open GaussianGammaZetaMellinFiniteDampedEvaluator (raw evaluatorF rawBody rawData evaluator_at raw_term_at)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (columnBody columnSumBody rowBody rowSumBody column_entry column_sum_at row_entry row_sum_at)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Damped" => GaussianEulerPositiveScalingIntegrand.evaluatorF
local notation "stripData" => GaussianGammaZetaMellinStrip.data

private def cell (j i p z B M a C E : PTm n) : PTm n :=
  inst2 rawBody j (rawData p (grid i M a C E) z B)

private def matrix : PTm 3 :=
  let d : PTm 3 := var 2
  cell (var 0) (var 1) (field0 d) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))
    (field1 d) (field2 d) (field3 d) (field4 d)

private theorem cell_at (j i p z B M N a C E : PTm n) :
    Γ ⊢[PRAAx] inst3 matrix j i (stripData p z B M N a C E) ≐ cell j i p z B M a C E := by
  let d := stripData p z B M N a C E
  let f : PTm 9 := cell (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
  let x : Fin 9 → PTm n := ![j,i,field0 d,fstT (sndT (field5 d)),sndT (sndT (field5 d)),field1 d,field2 d,field3 d,field4 d]
  let y : Fin 9 → PTm n := ![j,i,p,z,B,M,a,C,E]
  have parcel : Γ ⊢[PRAAx] field5 d ≐ pairT N (pairT z B) := field5_at _ _ _ _ _ _
  have e := (congrSnd parcel).eqTrans (snd_pair N (pairT z B))
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) f (σ := x) (σ' := y) (fun k => by
    fin_cases k
    · exact .eqRefl j
    · exact .eqRefl i
    · exact field0_at _ _ _ _ _ _
    · exact (congrFst e).eqTrans (fst_pair z B)
    · exact (congrSnd e).eqTrans (snd_pair z B)
    · exact field1_at _ _ _ _ _ _
    · exact field2_at _ _ _ _ _ _
    · exact field3_at _ _ _ _ _ _
    · exact field4_at _ _ _ _ _ _)
  simpa only [inst3,matrix,cell,subst_inst2,GaussianGammaZetaMellinFiniteDampedEvaluator.subst_rawData,
    GaussianCompactRiemannName.subst_grid,GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,
    GaussianCompactRiemannName.subst_field2,GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,
    GaussianCompactRiemannName.subst_field5,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val,f,x,y,d] using read

private theorem column_at (i p z B M N a C E : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalFubini.column matrix i N (stripData p z B M N a C E) ≐ raw p (grid i M a C E) z B N := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have e := (column_entry (Γ := Δ) matrix (var 0) (sh i) (stripData (sh p) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E))).eqTrans
    (cell_at (var 0) (sh i) (sh p) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E))
  simpa only [cell,sh,Δ,Syn.shift,subst_pairT,GaussianGammaZetaMellinStrip.subst_data,
    GaussianGammaZetaMellinFiniteDampedEvaluator.subst_rawData,GaussianCompactRiemannName.subst_grid] using e

private theorem row_at (j p z B M N a C E : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalFubini.row matrix j M (stripData p z B M N a C E) ≐
      sum (sampleBody Damped) M (sampleData p M a C E (GaussianEulerPositiveScalingIntegrand.fixedData z B (succ j) one)) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (sh M) :: Γ.map Fm.shift
  let x := GaussianEulerPositiveScalingIntegrand.fixedData (sh z) (sh B) (succ (sh j)) one
  have left := (row_entry (Γ := Δ) matrix (sh j) (var 0) (stripData (sh p) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E))).eqTrans
    ((cell_at (sh j) (var 0) (sh p) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E)).eqTrans
      (raw_term_at (sh j) (sh p) (grid (var 0) (sh M) (sh a) (sh C) (sh E)) (sh z) (sh B)))
  have right := sample_body_at (Γ := Δ) Damped (var 0) (sh p) (sh M) (sh a) (sh C) (sh E) x
  simpa only [cell,sh,Δ,x,Syn.shift,subst_pairT,GaussianGammaZetaMellinStrip.subst_data,GaussianCompactRiemannName.subst_sampleData,
    GaussianEulerPositiveScalingIntegrand.subst_fixedData,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using left.eqTrans right.eqSymm

theorem strip_grid_agreement (p z B M N a C E Q : PTm n) :
    Γ ⊢[PRAAx] quadrature evaluatorF p M a C E (GaussianGammaZetaMellinFiniteDampedEvaluator.data z B N Q) ≐
      dampedValue (exponent Q p) z B M N a C E := by
  let q := exponent Q p
  let d := stripData q z B M N a C E
  let x := GaussianGammaZetaMellinFiniteDampedEvaluator.data z B N Q
  let w := weight C E M
  have outer : Γ ⊢[PRAAx] GaussianRationalFubini.columnFirst matrix N M d ≐ sum (sampleBody evaluatorF) M (sampleData p M a C E x) := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    let sh (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (sh M) :: Γ.map Fm.shift
    let q' := exponent (sh Q) (sh p)
    let d' := stripData q' (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E)
    let x' := GaussianGammaZetaMellinFiniteDampedEvaluator.data (sh z) (sh B) (sh N) (sh Q)
    let t := grid (var 0) (sh M) (sh a) (sh C) (sh E)
    have left := (column_sum_at (Γ := Δ) matrix (var 0) (sh N) d').eqTrans
      (column_at (var 0) q' (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E))
    have read := evaluator_at (Γ := Δ) (sh p) t (sh z) (sh B) (sh N) (sh Q)
    have right := (sample_body_at (Γ := Δ) evaluatorF (var 0) (sh p) (sh M) (sh a) (sh C) (sh E) x').eqTrans read
    simpa only [sh,Δ,d,d',x,x',q,q',t,Syn.shift,subst_pairT,GaussianGammaZetaMellinStrip.subst_data,
      GaussianGammaZetaMellinFiniteDampedEvaluator.subst_data,GaussianFastValueCut.subst_exponent,
      GaussianCompactRiemannName.subst_sampleData] using left.eqTrans right.eqSymm
  have transposed : Γ ⊢[PRAAx] sum (multiplyBody (rowSumBody matrix)) N (pairT w (pairT M d)) ≐ dampedValue q z B M N a C E := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    let sh (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    let d' := stripData (sh q) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E)
    let w' := weight (sh C) (sh E) (sh M)
    let i : PTm (n+1) := var 0
    have left := (multiply_body_at (Γ := Δ) (rowSumBody matrix) w' i (pairT (sh M) d')).eqTrans
      (qmul_congr (.eqRefl w') ((row_sum_at matrix i (sh M) d').eqTrans
        (row_at i (sh q) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E))))
    have right := damped_index_at (Γ := Δ) i (sh q) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E)
    simpa only [d,d',w,w',i,sh,Δ,quadrature,Syn.shift,subst_pairT,GaussianGammaZetaMellinStrip.subst_data,
      GaussianRationalRiemannRefinement.subst_weight] using left.eqTrans right.eqSymm
  have order := (GaussianRationalFubini.fubini (Γ := Γ) matrix N M d).eqTrans outer
  exact (qmul_congr (.eqRefl w) order.eqSymm).eqTrans
    ((sum_multiply (rowSumBody matrix) w N (pairT M d)).eqSymm.eqTrans transposed)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedGrid
