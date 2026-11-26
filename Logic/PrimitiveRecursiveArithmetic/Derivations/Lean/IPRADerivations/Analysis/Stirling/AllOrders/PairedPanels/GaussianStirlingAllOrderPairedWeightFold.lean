import IPRADerivations.Analysis.Stirling.AllOrders.Covariance.GaussianStirlingAllOrderCrossedRectangles
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumMirror

/-!
# Exact reflected averaging of the unweighted reciprocal factor

Pairing the reciprocal-power weight samples on a mesh of length 8S
gives the original reflected weight sum over its first 4S indices.
The left and reflected averages differ by the difference of their
right endpoint and midpoint corrections.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedWeightFold

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num subst_num)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianStirlingAllOrderBoxProductGap (weightAt)
open GaussianStirlingAllOrderCrossedCells (segmentData reflectedBody reflected_at subst_segmentData)
open GaussianStirlingAllOrderCrossedRectangles (reflectedSum)
open GaussianStirlingAllOrderPairedRefinement (start mesh)
open GaussianStirlingAllOrderPairedWeight (weight pairWeight subst_weight)
open RationalAlgebra (add_congr multiply_congr multiply_add multiply_associative)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalEq_congr)
open RationalFiniteSum (sum term sum_ext termwiseEq canonical_equal)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalNormalForm (normalize_well_formed)
open RationalSumMirror (mirrorBody mirrorData mirror_at mirror_sum subst_mirrorData)
open RationalSumSegments (sum_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def singleWeight (q A B S i : PTm n) : PTm n := weight q (mesh B S) (start A S+B*i)

def weightData (q A B S : PTm n) : PTm n := pairT q (pairT (mesh B S) (pairT (start A S) B))

def weightBody : PTm 2 :=
  let d := var 1
  let e := sndT (sndT d)
  weight (fstT d) (fstT (sndT d)) (fstT e+sndT e*var 0)

ipra_subst weightData [mesh, start]

theorem weight_row_at (i q A B S : PTm n) :
    Γ ⊢[PRAAx] term weightBody i (weightData q A B S) ≐ singleWeight q A B S i := by
  let d := weightData q A B S
  have middle : Γ ⊢[PRAAx] sndT d ≐ pairT (mesh B S) (pairT (start A S) B) := snd_pair _ _
  have tail : Γ ⊢[PRAAx] sndT (sndT d) ≐ pairT (start A S) B :=
    (congrSnd middle).eqTrans (snd_pair _ _)
  have q' : Γ ⊢[PRAAx] fstT d ≐ q := fst_pair _ _
  have M : Γ ⊢[PRAAx] fstT (sndT d) ≐ mesh B S := (congrFst middle).eqTrans (fst_pair _ _)
  have a : Γ ⊢[PRAAx] fstT (sndT (sndT d)) ≐ start A S := (congrFst tail).eqTrans (fst_pair _ _)
  have b : Γ ⊢[PRAAx] sndT (sndT (sndT d)) ≐ B := (congrSnd tail).eqTrans (snd_pair _ _)
  simp only [term,inst2,weightBody,subst_weight,subst_fstT,subst_sndT,PTm.subst_mul,PTm.subst_add,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [singleWeight,subst_weight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (weight (var 0) (var 1) (var 2))
      (σ := ![fstT d,fstT (sndT d),fstT (sndT (sndT d))+sndT (sndT (sndT d))*i])
      (σ' := ![q,mesh B S,start A S+B*i]) (fun j => by
        fin_cases j
        · exact q'
        · exact M
        · exact congrAdd a (congrMul b (.eqRefl i)))

private theorem reflection (B S i : PTm n) (hi : Γ ⊢[PRAAx] le i (S*num 4)) :
    Γ ⊢[PRAAx] B*monus (S*num 4+S*num 4) i ≐ monus (mesh B S) (B*i) := by
  let N := S*num 4
  let M := N+N
  have h := le_trans hi (le_add_right N N)
  have total : Γ ⊢[PRAAx] M ≐ monus M i+i :=
    (eq_add_of_le h).eqTrans (add_comm _ _)
  have expanded : Γ ⊢[PRAAx] mesh B S ≐ B*monus M i+B*i :=
    (by dsimp [mesh,M,N]; ipra_ring : Γ ⊢[PRAAx] mesh B S ≐ B*M).eqTrans
      ((congrMul (.eqRefl B) total).eqTrans (by ipra_ring))
  exact ((congrMonus expanded (.eqRefl (B*i))).eqTrans (add_monus _ _)).eqSymm

private theorem exact_mirror_at (i q A B S : PTm n) (hi : Γ ⊢[PRAAx] le i (S*num 4)) :
    Γ ⊢[PRAAx] term (mirrorBody weightBody) i (mirrorData (S*num 4) (weightData q A B S)) ≐
      term reflectedBody i (segmentData q A B S zero) := by
  let N := S*num 4
  let x := weightData q A B S
  have right : Γ ⊢[PRAAx] singleWeight q A B S (monus (N+N) i) ≐
      weight q (mesh B S) (start A S+monus (mesh B S) (B*i)) :=
    fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) (congrAdd (.eqRefl _) (reflection B S i hi)))
  have clean : Γ ⊢[PRAAx] term reflectedBody i (segmentData q A B S zero) ≐ weightAt q A B S i :=
    (reflected_at i q A B S zero).eqTrans (by
      simpa only [GaussianStirlingAllOrderCrossedCells.subst_weightAt,Syn.subst_var,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
        Prf.eqCongr (Γ := Γ) (weightAt (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
          (σ := ![q,A,B,S,zero+i]) (σ' := ![q,A,B,S,i])
          (fun j => by fin_cases j <;> first | exact .eqRefl _ | exact zero_add i))
  exact (mirror_at weightBody i N x hi).eqTrans
    ((add_congr (weight_row_at i q A B S) ((weight_row_at (monus (N+N) i) q A B S).eqTrans right)).eqTrans clean.eqSymm)

private theorem reflected_fold (q A B S : PTm n) :
    Γ ⊢[PRAAx] sum (mirrorBody weightBody) (S*num 4) (mirrorData (S*num 4) (weightData q A B S)) ≐
      reflectedSum q A B S zero (S*num 4) := by
  apply sum_ext
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh S*num 4) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i (sh S*num 4) := Prf.hyp0
  have eq := exact_mirror_at i (sh q) (sh A) (sh B) (sh S) (le_of_lt hi)
  simpa only [Δ,termwiseEq,sh,i,Syn.shift,subst_weightData,subst_mirrorData,subst_segmentData,
    PTm.subst_mul,subst_num,ConciseIPRA.PTm.subst_zero] using
      rationalEq_congr eq.eqSymm (.eqRefl _) (.eqRefl _)

theorem weight_fold (q A B S : PTm n) :
    Γ ⊢[PRAAx] add (sum weightBody (S*num 8) (weightData q A B S)) (singleWeight q A B S (S*num 8)) ≐
      add (reflectedSum q A B S zero (S*num 4)) (singleWeight q A B S (S*num 4)) := by
  let M := S*num 8
  let N := S*num 4
  let x := weightData q A B S
  have e : Γ ⊢[PRAAx] M ≐ N+N := by dsimp [M,N]; ipra_ring
  have last : Γ ⊢[PRAAx] singleWeight q A B S M ≐ term weightBody (N+N) x :=
    (weight_row_at M q A B S).eqSymm.eqTrans (congrInst2 _ e (.eqRefl x))
  exact (add_congr (sum_congr weightBody e (.eqRefl x)) last).eqTrans
    ((mirror_sum weightBody N x).eqTrans (add_congr (reflected_fold q A B S) (weight_row_at N q A B S)))

def weightAverage (q A B S : PTm n) : PTm n :=
  multiply (fraction one (S*num 8)) (sum weightBody (S*num 8) (weightData q A B S))

theorem double_scale (S v : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] multiply (fraction two one) (multiply (fraction one (S*num 8)) v) ≐
      multiply (fraction one (S*num 4)) v := by
  let M := S*num 8
  let N := S*num 4
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ hS (by ipra_le 3)
  have hD := positive_product _ _ (le_refl one) hM
  have eq : Γ ⊢[PRAAx] fraction (two*one) (one*M) ≐ fraction one N := by
    apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hD) (normalize_well_formed _ _ hN)
      (fraction_represents _ _ hD) (fraction_represents _ _ hN) hD hN
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    dsimp only [M,N]
    ipra_simps
    ring
  exact (multiply_associative _ _ _).eqSymm.eqTrans
    (multiply_congr ((fraction_multiply two one one M (le_refl one) hM).eqTrans eq) (.eqRefl v))

theorem weight_average (q A B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] add (multiply (fraction two one) (weightAverage q A B S))
        (multiply (fraction one (S*num 4)) (singleWeight q A B S (S*num 8))) ≐
      add (multiply (fraction one (S*num 4)) (reflectedSum q A B S zero (S*num 4)))
        (multiply (fraction one (S*num 4)) (singleWeight q A B S (S*num 4))) := by
  let c := fraction one (S*num 4)
  exact (add_congr (double_scale S _ hS) (.eqRefl _)).eqTrans
    ((multiply_add c _ _).eqSymm.eqTrans
      ((multiply_congr (.eqRefl c) (weight_fold q A B S)).eqTrans (multiply_add c _ _)))

theorem actual_reflected_reciprocal_weight_average_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (le one (var 3) ⟶
      add (multiply (fraction two one) (weightAverage (var 0) (var 1) (var 2) (var 3)))
        (multiply (fraction one (var 3*num 4)) (singleWeight (var 0) (var 1) (var 2) (var 3) (var 3*num 8))) ≐
      add (multiply (fraction one (var 3*num 4)) (reflectedSum (var 0) (var 1) (var 2) (var 3) zero (var 3*num 4)))
        (multiply (fraction one (var 3*num 4)) (singleWeight (var 0) (var 1) (var 2) (var 3) (var 3*num 4)))) :=
  closeUniv 4 (.impI (weight_average _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedWeightFold
