import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalThirdLogarithmSeries
import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareInterval

/-!
# Cauchy estimate for original cubic Barnes logarithm prefixes on x>0

After the first row, the original kth zero-based row has size at most
4/k² on the whole positive axis. The reciprocal-square telescope therefore
controls gaps between any two of the original nonempty partial sums.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmCauchy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Common (mul_le_mul pw_two)
open GaussianBarnesCanonicalHigherDerivative (body body_at)
open GaussianBarnesCanonicalThirdLogarithmRows
  (center denominator denominator_positive derivative_at numerator row shiftedNumerator)
open GaussianBarnesCanonicalThirdLogarithmSeries (value)
open GaussianDominantPairAlgebra (radius_bounded)
open GaussianRationalFiniteSum (sum termsEqual sum_index_congr)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalSquareInterval (rowsBounded)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain : PTm n := two*two

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (gain : PTm n) = (gain : PTm m) := by simp [gain,two,one]

theorem row_bound (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] bounded (row A B i) gain (i*i) := by
  let c := shiftedNumerator A B i
  let u := i*B
  have hc : Γ ⊢[PRAAx] le u c := le_add_left _ _
  have hs : Γ ⊢[PRAAx] le (succ i) (two*i) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right i hi)
  have compare : Γ ⊢[PRAAx] le (numerator B i*(i*i)) (gain*denominator A B i) := by
    have size : Γ ⊢[PRAAx] le ((two*succ i*pw B (succ two))*(i*i))
        ((two*(two*i)*pw B (succ two))*(i*i)) :=
      mul_le_mul (mul_le_mul (mul_le_mul (le_refl two) hs) (le_refl _)) (le_refl _)
    have left : Γ ⊢[PRAAx] ((two*(two*i)*pw B (succ two))*(i*i)) ≐ gain*(u*u*u) := by
      have cube := natEq ((pw_succ (Γ := Γ) B two).eqTrans (congrMul (pw_two B) (.eqRefl B)))
      apply deriveNat
      dsimp only [gain,u]
      ipra_simps
      rw [cube]
      ring
    have right : Γ ⊢[PRAAx] gain*(c*c*c) ≐ gain*denominator A B i :=
      congrMul (.eqRefl _) ((pw_succ c two).eqTrans (congrMul (pw_two c) (.eqRefl c))).eqSymm
    exact le_trans size (le_congr left.eqSymm right (mul_le_mul (le_refl gain) (mul_le_mul (mul_le_mul hc hc) hc)))
  have hD := denominator_positive A B i hA
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hD (positive_product _ _ hi hi)
    compare (radius_bounded _ _ hD)

private theorem rows_bounded (A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rowsBounded body N gain (GaussianBarnesCanonicalHigherTail.data (center A B) B (succ N) zero) := by
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let m := Syn.shift N
  let i : PTm (n+1) := var 0
  let Δ := Γ.map Fm.shift
  have aPos : Δ ⊢[PRAAx] le one a := by simpa [Δ,Fm.shift,Syn.shift,a,one] using hA.shift
  have bPos : Δ ⊢[PRAAx] le one b := by simpa [Δ,Fm.shift,Syn.shift,b,one] using hB.shift
  have eq : Δ ⊢[PRAAx] succ m+i ≐ succ (m+i) := by ipra_ring
  have idx : Δ ⊢[PRAAx] le one (succ m+i) := le_trans (zero_lt_succ m) (le_add_right _ _)
  have e := (body_at (Γ := Δ) (center a b) b (succ m) zero i).eqTrans
    (derivative_at a b (succ m+i) aPos bPos)
  simpa only [rowsBounded,Syn.shift,a,b,m,i,Δ,subst_gain,GaussianBarnesCanonicalThirdLogarithmRows.subst_center,
    GaussianBarnesCanonicalHigherTail.subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      bound_congr e.eqSymm (.eqRefl _) (congrMul eq eq) (row_bound a b (succ m+i) aPos idx)

theorem tail_bound (A B N r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (GaussianBarnesCanonicalThirdLogarithmTail.value A B N r) gain N :=
  GaussianReciprocalSquareInterval.tail_bound body N r gain _ hN (rows_bounded A B N hA hB)

theorem split (A B N r : PTm n) :
    Γ ⊢[PRAAx] value A B (succ N+r) ≐
      qadd (value A B (succ N)) (GaussianBarnesCanonicalThirdLogarithmTail.value A B N r) := by
  let x := GaussianBarnesCanonicalHigherTail.data (center A B) B zero zero
  let y := GaussianBarnesCanonicalHigherTail.data (center A B) B (succ N) zero
  have block : Γ ⊢[PRAAx] sum (offB body) r (pairT (succ N) x) ≐ sum body r y := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    let a := Syn.shift A
    let b := Syn.shift B
    let k := succ (Syn.shift N)
    let i : PTm (n+1) := var 0
    let Δ := lt i (Syn.shift r) :: Γ.map Fm.shift
    let X := GaussianBarnesCanonicalHigherTail.data (center a b) b zero zero
    have raw := GaussianRationalFiniteProduct.offset_at (Γ := Δ) body k i X
    have pre := body_at (Γ := Δ) (center a b) b zero zero (k+i)
    have post := body_at (Γ := Δ) (center a b) b k zero i
    have z : Δ ⊢[PRAAx] GaussianBarnesCanonicalHigherRows.derivative (center a b) b (succ (zero+(k+i))) zero ≐
        GaussianBarnesCanonicalHigherRows.derivative (center a b) b (succ (k+i)) zero := by
      ipra_congr (GaussianBarnesCanonicalHigherRows.derivative (var 0) (var 1) (var 2) (var 3) : PTm 4)
        with [.eqRefl _, .eqRefl _, congrSucc (zero_add _), .eqRefl _]
    simpa only [termsEqual,Syn.shift,x,y,a,b,k,i,Δ,X,subst_pairT,GaussianBarnesCanonicalThirdLogarithmRows.subst_center,
      GaussianBarnesCanonicalHigherTail.subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
        raw.eqTrans (pre.eqTrans (z.eqTrans post.eqSymm))
  exact (GaussianRationalMatrixFiniteSums.sum_split body (succ N) r x).eqTrans (qadd_congr (.eqRefl _) block)

theorem added_prefix_error (A B N r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (value A B (succ N+r)) (value A B (succ N)) gain N := by
  let v := GaussianBarnesCanonicalThirdLogarithmTail.value A B N r
  have cancel : Γ ⊢[PRAAx] qsub (value A B (succ N+r)) (value A B (succ N)) ≐ v :=
    (qsub_congr (split A B N r) (.eqRefl _)).eqTrans
      (qadd_sub_cancel _ v (GaussianRationalFiniteSum.sum_canonical body r _))
  exact bound_congr cancel.eqSymm (.eqRefl _) (.eqRefl _) (tail_bound A B N r hA hB hN)

theorem ordered_prefix_error (A B N M : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hNM : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] distanceBounded (value A B (succ M)) (value A B (succ N)) gain N := by
  let r := LeanProofs.IPRA.PTm.monus M N
  have pos : Γ ⊢[PRAAx] succ N+r ≐ succ M :=
    (by ipra_ring : Γ ⊢[PRAAx] succ N+r ≐ succ (N+r)).eqTrans (congrSucc (eq_add_of_le hNM).eqSymm)
  have e : Γ ⊢[PRAAx] value A B (succ N+r) ≐ value A B (succ M) := sum_index_congr body pos (.eqRefl _)
  exact GaussianRationalDistanceOrder.distance_congr e (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (added_prefix_error A B N r hA hB hN)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmCauchy
