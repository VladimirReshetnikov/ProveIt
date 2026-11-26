import IPRADerivations.Analysis.GaussianBarnesCanonicalDerivativeRow
import IPRADerivations.Analysis.GaussianBarnesCanonicalLogTail
import IPRADerivations.Analysis.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.GaussianReciprocalSquareInterval

/-!
# Finite tails of the rational first-derivative expressions

The actual rational sum contains the derivative expressions for
`N < k ≤ N+r`. Its exact norm bound is `2R²*r/(N*(N+r))`,
and arbitrary consecutive blocks split with no rounding error.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogTail (source row_source)
open GaussianRationalFiniteSum (sum termsEqual)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalSquareInterval (denominator rowsBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "row" => GaussianBarnesCanonicalDerivativeRow.value
local notation "C" => GaussianBarnesCanonicalDerivativeRow.boundNumerator

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
  simpa only [body,inst2,GaussianBarnesCanonicalDerivativeRow.subst_value,subst_fstT,subst_sndT,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.tail_cons,Matrix.head_cons,x] using h

theorem rows_bounded (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] rowsBounded body N (C R) (data z B N) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift
  have b := GaussianBarnesCanonicalDerivativeRow.row_bound (sh z) (sh R) (sh B) (succ (sh N+i))
    (row_source (sh z) (sh R) (sh B) (sh N) i hs)
  simpa only [rowsBounded,sh,i,Syn.shift,subst_data,GaussianBarnesCanonicalDerivativeRow.subst_boundNumerator,
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
  let x := data z B N
  let y := data z B (N+r)
  have tail : Γ ⊢[PRAAx] sum (offB body) s (pairT r x) ≐ sum body s y := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    let sh (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (sh s) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have off := GaussianRationalFiniteProduct.offset_at (Γ := Δ) body (sh r) i (data (sh z) (sh B) (sh N))
    have e : Δ ⊢[PRAAx] succ (sh N+(sh r+i)) ≐ succ ((sh N+sh r)+i) :=
      congrSucc (add_assoc _ _ _).eqSymm
    have a := body_at (Γ := Δ) (sh z) (sh B) (sh N) (sh r+i)
    have b := body_at (Γ := Δ) (sh z) (sh B) (sh N+sh r) i
    have c : Δ ⊢[PRAAx] row (sh z) (sh B) (succ (sh N+(sh r+i))) ≐ row (sh z) (sh B) (succ ((sh N+sh r)+i)) := by
      ipra_congr (row (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl _, .eqRefl _, e]
    simpa only [termsEqual,Syn.shift,sh,i,Δ,subst_pairT,x,y,subst_data,PTm.subst_add] using
      off.eqTrans (a.eqTrans (c.eqTrans b.eqSymm))
  exact (GaussianRationalMatrixFiniteSums.sum_split body r s x).eqTrans (qadd_congr (.eqRefl _) tail)

theorem late_source (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] source z R B (N+r) :=
  .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ (le_add_right _ _))
    (.andI h.andE₂.andE₂.andE₁ (le_trans h.andE₂.andE₂.andE₂ (le_add_right _ _))))

theorem finite_gap (z R B N r s : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (value z B N (r+s)) (value z B N r) (C R) (N+r) := by
  let v := value z B (N+r) s
  have cancel : Γ ⊢[PRAAx] qsub (value z B N (r+s)) (value z B N r) ≐ v :=
    (qsub_congr (split z B N r s) (.eqRefl (value z B N r))).eqTrans
    (qadd_sub_cancel (value z B N r) v (GaussianRationalFiniteSum.sum_canonical body s (data z B (N+r))))
  exact bound_congr cancel.eqSymm (.eqRefl _) (.eqRefl _) (tail_bound z R B (N+r) s (late_source z R B N r h))

theorem actual_Barnes_first_derivative_finite_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (value (var 0) (var 2) (var 3) (var 4)) (C (var 1)) (var 3)) :=
  closeUniv 5 (.impI (tail_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeTail
