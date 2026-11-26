import IPRADerivations.Analysis.GaussianBarnesCanonicalHigherRows
import IPRADerivations.Analysis.GaussianBarnesCanonicalDerivativeTail

/-!
# Uniform finite tails of the higher Barnes logarithmic coefficients

The primitive-recursive sum keeps the original retained indices and
the encoded order. The inverse-square telescope applies uniformly at
every internal order and every internal cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHigherRows (coefficient coefficientGain coefficient_square_bound)
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

def data (z B N j : PTm n) : PTm n := pairT (pairT z B) (pairT N j)

def body : PTm 2 :=
  coefficient (fstT (fstT (var 1))) (sndT (fstT (var 1)))
    (succ (fstT (sndT (var 1))+var 0)) (sndT (sndT (var 1)))

def value (z B N j r : PTm n) : PTm n := sum body r (data z B N j)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B N j : PTm n) :
    Syn.subst σ (data z B N j) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ j) :=
  by simp [data]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B N j r : PTm n) :
    Syn.subst σ (value z B N j r) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ j) (Syn.subst σ r) :=
  by simp [value]

theorem body_at (z B N j i : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data z B N j) ≐ coefficient z B (succ (N+i)) j := by
  let x := data z B N j
  have u : Γ ⊢[PRAAx] fstT x ≐ pairT z B := fst_pair _ _
  have v : Γ ⊢[PRAAx] sndT x ≐ pairT N j := snd_pair _ _
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (coefficient (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (fstT x),sndT (fstT x),succ (fstT (sndT x)+i),sndT (sndT x)])
    (σ' := ![z,B,succ (N+i),j]) (fun p => by
      fin_cases p
      · exact (congrFst u).eqTrans (fst_pair _ _)
      · exact (congrSnd u).eqTrans (snd_pair _ _)
      · exact congrSucc (congrAdd ((congrFst v).eqTrans (fst_pair _ _)) (.eqRefl _))
      · exact (congrSnd v).eqTrans (snd_pair _ _))
  simpa [body,inst2,x] using e

theorem rows_bounded (z R B N j : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] rowsBounded body N (coefficientGain j) (data z B N j) := by
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift
  have b := coefficient_square_bound (sh z) (sh R) (sh B) (succ (sh N+i)) (sh j)
    (row_source (sh z) (sh R) (sh B) (sh N) i hs)
  simpa only [rowsBounded,sh,i,Syn.shift,subst_data,GaussianBarnesCanonicalHigherRows.subst_coefficientGain] using
    bound_congr (body_at (sh z) (sh B) (sh N) (sh j) i).eqSymm (.eqRefl _) (.eqRefl _) b

theorem interval_bound (z R B N j r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N j r) (coefficientGain j*r) (denominator N r) :=
  GaussianReciprocalSquareInterval.interval_bound body N r (coefficientGain j) (data z B N j)
    h.andE₂.andE₁ (rows_bounded z R B N j h)

theorem tail_bound (z R B N j r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N j r) (coefficientGain j) N :=
  GaussianReciprocalSquareInterval.tail_bound body N r (coefficientGain j) (data z B N j)
    h.andE₂.andE₁ (rows_bounded z R B N j h)

theorem split (z B N j r s : PTm n) :
    Γ ⊢[PRAAx] value z B N j (r+s) ≐ qadd (value z B N j r) (value z B (N+r) j s) := by
  let x := data z B N j
  let y := data z B (N+r) j
  have tail : Γ ⊢[PRAAx] sum (offB body) s (pairT r x) ≐ sum body s y := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    let sh (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (sh s) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have off := GaussianRationalFiniteProduct.offset_at (Γ := Δ) body (sh r) i (data (sh z) (sh B) (sh N) (sh j))
    have e : Δ ⊢[PRAAx] succ (sh N+(sh r+i)) ≐ succ ((sh N+sh r)+i) :=
      congrSucc (add_assoc _ _ _).eqSymm
    have a := body_at (Γ := Δ) (sh z) (sh B) (sh N) (sh j) (sh r+i)
    have b := body_at (Γ := Δ) (sh z) (sh B) (sh N+sh r) (sh j) i
    have c : Δ ⊢[PRAAx] coefficient (sh z) (sh B) (succ (sh N+(sh r+i))) (sh j) ≐
        coefficient (sh z) (sh B) (succ ((sh N+sh r)+i)) (sh j) := by
      ipra_congr (coefficient (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl _, .eqRefl _, e, .eqRefl _]
    simpa only [termsEqual,Syn.shift,sh,i,Δ,subst_pairT,x,y,subst_data,PTm.subst_add] using
      off.eqTrans (a.eqTrans (c.eqTrans b.eqSymm))
  exact (GaussianRationalMatrixFiniteSums.sum_split body r s x).eqTrans (qadd_congr (.eqRefl _) tail)

theorem finite_gap (z R B N j r s : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (value z B N j (r+s)) (value z B N j r) (coefficientGain j) (N+r) := by
  let v := value z B (N+r) j s
  have cancel := (qsub_congr (split (Γ := Γ) z B N j r s) (.eqRefl (value z B N j r))).eqTrans
    (qadd_sub_cancel (value z B N j r) v (GaussianRationalFiniteSum.sum_canonical body s (data z B (N+r) j)))
  exact bound_congr cancel.eqSymm (.eqRefl _) (.eqRefl _)
    (tail_bound z R B (N+r) j s (GaussianBarnesCanonicalDerivativeTail.late_source z R B N r h))

theorem actual_Barnes_all_higher_coefficient_finite_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let R := var 1
     let B := var 2
     let N := var 3
     let j := var 4
     let r := var 5
     let s := var 6
     source z R B N ⟶ distanceBounded (value z B N j (r+s)) (value z B N j r) (coefficientGain j) (N+r)) :=
  closeUniv 7 (.impI (finite_gap _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherTail
