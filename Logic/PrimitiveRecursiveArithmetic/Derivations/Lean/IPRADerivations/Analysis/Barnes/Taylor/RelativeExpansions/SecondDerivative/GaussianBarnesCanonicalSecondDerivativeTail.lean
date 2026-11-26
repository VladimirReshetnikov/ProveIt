import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.SecondDerivative.GaussianBarnesCanonicalSecondDerivativeRow
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Cofinal.GaussianBarnesCanonicalDerivativeTail
import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogTail
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareInterval

/-!
# Finite tails of the original rational second-derivative rows

The actual rational sum contains the second derivative expressions for
`N < k ≤ N+r`. The inverse-square telescope supplies the bound
`12R*r/(N*(N+r))`, and consecutive blocks split exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeTail

open_ipra
open GaussianRationalMatrixFiniteSums (split_indexed_rows gap_of_split)
open GaussianBarnesCanonicalLogTail (source row_source)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianReciprocalSquareInterval (denominator rowsBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "row" => GaussianBarnesCanonicalSecondDerivativeRow.value
local notation "C" => GaussianBarnesCanonicalSecondDerivativeRow.boundNumerator

def data (z B N : PTm n) : PTm n := pairT z (pairT B N)

def body : PTm 2 := row (fstT (var 1)) (fstT (sndT (var 1))) (succ (sndT (sndT (var 1))+var 0))

def value (z B N r : PTm n) : PTm n := sum body r (data z B N)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (data z B N) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [data]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B N r : PTm n) :
    Syn.subst σ (value z B N r) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by simp [value]

theorem body_at (z B N i : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data z B N) ≐ row z B (succ (N+i)) := by
  let x := data z B N
  have d : Γ ⊢[PRAAx] sndT x ≐ pairT B N := snd_pair _ _
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (row (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT x,fstT (sndT x),succ (sndT (sndT x)+i)]) (σ' := ![z,B,succ (N+i)]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst d).eqTrans (fst_pair _ _)
      · exact congrSucc (congrAdd ((congrSnd d).eqTrans (snd_pair _ _)) (.eqRefl _)))
  simpa only [body,inst2,GaussianBarnesCanonicalSecondDerivativeRow.subst_value,subst_fstT,subst_sndT,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.tail_cons,Matrix.head_cons,x] using h

theorem rows_bounded (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] rowsBounded body N (C R) (data z B N) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift
  have b := GaussianBarnesCanonicalSecondDerivativeRow.row_bound (sh z) (sh R) (sh B) (succ (sh N+i))
    (row_source (sh z) (sh R) (sh B) (sh N) i hs)
  simpa only [rowsBounded,sh,i,Syn.shift,subst_data,GaussianBarnesCanonicalSecondDerivativeRow.subst_boundNumerator,
    GaussianBarnesCanonicalDerivativeRow.boundDenominator] using
    bound_congr (body_at (sh z) (sh B) (sh N) i).eqSymm (.eqRefl _) (.eqRefl _) b

theorem interval_bound (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N r) (C R*r) (denominator N r) :=
  GaussianReciprocalSquareInterval.interval_bound body N r (C R) (data z B N) h.andE₂.andE₁ (rows_bounded z R B N h)

theorem tail_bound (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N r) (C R) N :=
  GaussianReciprocalSquareInterval.tail_bound body N r (C R) (data z B N) h.andE₂.andE₁ (rows_bounded z R B N h)

theorem split (z B N r s : PTm n) :
    Γ ⊢[PRAAx] value z B N (r+s) ≐ qadd (value z B N r) (value z B (N+r) s) := by
  let sh {m : ℕ} (v : PTm m) := Syn.shift v
  refine split_indexed_rows body (row (sh (sh z)) (sh (sh B)) (var 0))
    (data z B N) (data z B (N+r)) N r s ?_ ?_
  all_goals simp only [sh,GaussianBarnesCanonicalSecondDerivativeRow.subst_value,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
  · simpa only [Syn.shift,sh,subst_data] using
      (body_at (Γ := Γ.map Fm.shift) (sh z) (sh B) (sh N) (sh r+var 0))
  · simpa only [Syn.shift,sh,subst_data,PTm.subst_add] using
      (body_at (Γ := Γ.map Fm.shift) (sh z) (sh B) (sh N+sh r) (var 0))

theorem finite_gap (z R B N r s : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (value z B N (r+s)) (value z B N r) (C R) (N+r) :=
  gap_of_split body _ _ r s _ _ (split z B N r s)
    (tail_bound z R B (N+r) s (GaussianBarnesCanonicalDerivativeTail.late_source z R B N r h))

theorem actual_Barnes_second_derivative_finite_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (value (var 0) (var 2) (var 3) (var 4)) (C (var 1)) (var 3)) :=
  closeUniv 5 (.impI (tail_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeTail
