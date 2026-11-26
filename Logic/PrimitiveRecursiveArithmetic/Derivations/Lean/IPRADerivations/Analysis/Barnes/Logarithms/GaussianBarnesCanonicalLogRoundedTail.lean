import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogObservation
import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogTail
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement

/-!
# Finite sums of actual rounded Barnes logarithms

Compare the literal rounded row sum to the exact finite sum and compare
the same rounded interval at two ordered precisions. The offset
identity uses the original rows on both interval pieces.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogRoundedTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogRow (roundedValue subst_roundedValue)
open GaussianBarnesCanonicalLogTail (source row_source)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open DyadicComplexLogarithm (unit precision)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (p z R B N : PTm n) : PTm n := pairT p (pairT z (pairT R (pairT B N)))

def body : PTm 2 := roundedValue (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
  (fstT (sndT (sndT (sndT (var 1))))) (succ (sndT (sndT (sndT (sndT (var 1))))+var 0))

def value (p z R B N r : PTm n) : PTm n := sum body r (data p z R B N)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (data p z R B N) =
      data (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [data]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p z R B N r : PTm n) :
    Syn.subst σ (value p z R B N r) =
      value (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [value]

theorem body_at (p z R B N i : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data p z R B N) ≐ roundedValue p z R B (succ (N+i)) := by
  let X := data p z R B N
  let d := sndT X
  let e := sndT d
  let f := sndT e
  let g := sndT f
  have hd : Γ ⊢[PRAAx] d ≐ pairT z (pairT R (pairT B N)) := snd_pair _ _
  have he : Γ ⊢[PRAAx] e ≐ pairT R (pairT B N) := (congrSnd hd).eqTrans (snd_pair _ _)
  have hf : Γ ⊢[PRAAx] f ≐ pairT B N := (congrSnd he).eqTrans (snd_pair _ _)
  have hg : Γ ⊢[PRAAx] g ≐ N := (congrSnd hf).eqTrans (snd_pair _ _)
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (roundedValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT X,fstT d,fstT e,fstT f,succ (g+i)]) (σ' := ![p,z,R,B,succ (N+i)]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst hd).eqTrans (fst_pair _ _)
      · exact (congrFst he).eqTrans (fst_pair _ _)
      · exact (congrFst hf).eqTrans (fst_pair _ _)
      · exact congrSucc (congrAdd hg (.eqRefl _)))
  simpa only [body,inst2,subst_roundedValue,subst_fstT,subst_sndT,PTm.subst_add,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four, Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,X,d,e,f,g] using fields

theorem split (p z R B N r s : PTm n) :
    Γ ⊢[PRAAx] value p z R B N (r+s) ≐ qadd (value p z R B N r) (value p z R B (N+r) s) := by
  let x := data p z R B N
  let y := data p z R B (N+r)
  have tail : Γ ⊢[PRAAx] sum (offB body) s (pairT r x) ≐ sum body s y := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh s) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have off := GaussianRationalFiniteProduct.offset_at (Γ := Δ) body (sh r) i (data (sh p) (sh z) (sh R) (sh B) (sh N))
    have e : Δ ⊢[PRAAx] succ (sh N+(sh r+i)) ≐ succ ((sh N+sh r)+i) :=
      congrSucc (add_assoc _ _ _).eqSymm
    have a := body_at (Γ := Δ) (sh p) (sh z) (sh R) (sh B) (sh N) (sh r+i)
    have b := body_at (Γ := Δ) (sh p) (sh z) (sh R) (sh B) (sh N+sh r) i
    have c : Δ ⊢[PRAAx] roundedValue (sh p) (sh z) (sh R) (sh B) (succ (sh N+(sh r+i))) ≐
        roundedValue (sh p) (sh z) (sh R) (sh B) (succ ((sh N+sh r)+i)) := by
      ipra_congr (roundedValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
        [.eqRefl _, .eqRefl _, .eqRefl _, .eqRefl _, e]
    simpa only [GaussianRationalFiniteSum.termsEqual, Syn.shift, sh, i, Δ, subst_pairT, x, y, subst_data, PTm.subst_add] using
      off.eqTrans (a.eqTrans (c.eqTrans b.eqSymm))
  exact (GaussianRationalMatrixFiniteSums.sum_split body r s x).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) tail)

private theorem row_at_most (N i r : PTm n) (h : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] le (succ (N+i)) (N+r) :=
  le_congr (add_succ _ _) (.eqRefl _) (add_le_add₂ (le_refl N) h)

theorem rounding_error (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (value p z R B N r) (GaussianBarnesCanonicalLogTail.value z B N r (precision p))
      (r*(two*(N+r))) (unit p) := by
  let x := data p z R B N
  let y := GaussianBarnesCanonicalLogTail.data z B N (precision p)
  have hU := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  refine sum_distance body GaussianBarnesCanonicalLogTail.body r x y (two*(N+r)) (unit p) hU (.allI (.impI ?_))
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.wk
  have le := row_at_most (sh N) i (sh r) (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have err := GaussianBarnesCanonicalLogRow.rounded_error (sh p) (sh z) (sh R) (sh B) (succ (sh N+i))
    (row_source (sh z) (sh R) (sh B) (sh N) i hs)
  have u := GaussianLocalLogarithmName.unit_positive (Γ := Δ) (sh p)
  have e := distance_radius_mono _ _ _ _ _ _ u u (mul_le_mul_right (unit (sh p))
    (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two le))) err
  simpa only [termsDistance,x,y,sh,Syn.shift,Δ,i,subst_data,GaussianBarnesCanonicalLogTail.subst_data,
    DyadicComplexLogarithm.subst_unit,DyadicComplexLogarithm.subst_precision,PTm.subst_mul,PTm.subst_add,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    distance_congr (body_at (sh p) (sh z) (sh R) (sh B) (sh N) i).eqSymm
      (GaussianBarnesCanonicalLogTail.body_at (sh z) (sh B) (sh N) (precision (sh p)) i).eqSymm (.eqRefl _) (.eqRefl _) e

theorem ordered_distance (p q z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (value q z R B N r) (value p z R B N r) (r*(num 5*(N+r))) (unit p) := by
  let x := data q z R B N
  let y := data p z R B N
  have hU := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  refine sum_distance body body r x y (num 5*(N+r)) (unit p) hU (.allI (.impI ?_))
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.wk
  have hp : Δ ⊢[PRAAx] le (sh p) (sh q) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hpq.shift.wk
  have le := row_at_most (sh N) i (sh r) (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have err := GaussianBarnesCanonicalLogObservation.ordered_distance (sh p) (sh q) (sh z) (sh R) (sh B) (succ (sh N+i))
    (row_source (sh z) (sh R) (sh B) (sh N) i hs) hp
  have u := GaussianLocalLogarithmName.unit_positive (Γ := Δ) (sh p)
  have e := distance_radius_mono _ _ _ _ _ _ u u (mul_le_mul_right (unit (sh p))
    (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 5) le))) err
  simpa only [termsDistance,x,y,sh,Syn.shift,Δ,i,subst_data,DyadicComplexLogarithm.subst_unit,
    PTm.subst_mul,PTm.subst_add,PTm.subst_num] using
    distance_congr (body_at (sh q) (sh z) (sh R) (sh B) (sh N) i).eqSymm (body_at (sh p) (sh z) (sh R) (sh B) (sh N) i).eqSymm
      (.eqRefl _) (.eqRefl _) e

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogRoundedTail
