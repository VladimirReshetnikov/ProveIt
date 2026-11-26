import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedWeightFold

/-!
# Exact first-half average of the centered Bernoulli profile

The two reflected samples agree, the right endpoint is zero, and the
single midpoint term supplies the entire correction from the
left-endpoint average on the full mesh.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedBernoulliFold

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num subst_num)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingAllOrderBoxProductGap (sampleAt)
open GaussianStirlingAllOrderCenteredBernoulli (reflected_sample endpoint_samples_zero)
open GaussianStirlingAllOrderCrossedCells (segmentData bernoulliBody bernoulli_at subst_segmentData)
open GaussianStirlingAllOrderCrossedRectangles (bernoulliSum)
open GaussianStirlingAllOrderPairedWeightFold (double_scale)
open RationalAlgebra (add_congr multiply_add multiply_congr multiply_commutative multiply_associative)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalEq_congr)
open RationalFiniteSum (sum term sum_ext termwiseEq sum_well_formed)
open RationalNonnegativePowers (fraction_congr)
open RationalReciprocalPowerTail (add_zero_right)
open RationalSumAdditivity (addedBody added_term sum_additive)
open RationalSumConstants (multiply_one_right count_add)
open RationalSumMirror (mirrorBody mirrorData mirror_at mirror_sum subst_mirrorData)
open RationalSumSegments (sum_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem sample_at (m : ℕ) (i q A B S : PTm n) :
    Γ ⊢[PRAAx] term (bernoulliBody m) i (segmentData q A B S zero) ≐ sampleAt m S i := by
  have e : Γ ⊢[PRAAx] sampleAt m S (zero+i) ≐ sampleAt m S i := by
    simpa only [GaussianStirlingAllOrderCrossedCells.subst_sampleAt,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one] using Prf.eqCongr (Γ := Γ) (sampleAt m (var 0) (var 1) : PTm 2)
      (σ := ![S,zero+i]) (σ' := ![S,i]) (fun j => by
        fin_cases j
        · exact .eqRefl S
        · exact zero_add i)
  exact (bernoulli_at m i q A B S zero).eqTrans e

private theorem row_symmetric (m : ℕ) (i q A B S : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hi : Γ ⊢[PRAAx] le i (S*num 4)) :
    Γ ⊢[PRAAx] term (bernoulliBody m) (monus (S*num 4+S*num 4) i) (segmentData q A B S zero) ≐
      term (bernoulliBody m) i (segmentData q A B S zero) := by
  let N := S*num 4
  let M := S*num 8
  let f := bernoulliBody m
  let d := segmentData q A B S zero
  have e : Γ ⊢[PRAAx] N+N ≐ M := by dsimp [M,N]; ipra_ring
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have hiM : Γ ⊢[PRAAx] le i M :=
    le_congr (.eqRefl _) e (le_trans hi (le_add_right N N))
  exact (congrInst2 f (congrMonus e (.eqRefl i)) (.eqRefl d)).eqTrans
    ((sample_at m (monus M i) q A B S).eqTrans
      ((reflected_sample (m+1) i M hM hiM).eqTrans (sample_at m i q A B S).eqSymm))

private theorem sum_symmetric (m : ℕ) (q A B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    let f := bernoulliBody m
    let d := segmentData q A B S zero
    Γ ⊢[PRAAx] sum (mirrorBody f) (S*num 4) (mirrorData (S*num 4) d) ≐
      add (sum f (S*num 4) d) (sum f (S*num 4) d) := by
  let f := bernoulliBody m
  let d := segmentData q A B S zero
  let N := S*num 4
  have bridge : Γ ⊢[PRAAx] sum (mirrorBody f) N (mirrorData N d) ≐ sum (addedBody f f) N (pairT d d) := by
    apply sum_ext
    refine .allI (.impI ?_)
    let sh (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh S*num 4) :: Γ.map Fm.shift
    let data := segmentData (sh q) (sh A) (sh B) (sh S) zero
    have hi : Δ ⊢[PRAAx] lt i (sh S*num 4) := Prf.hyp0
    have hs : Δ ⊢[PRAAx] le one (sh S) := by
      simpa [Δ,Fm.shift,sh,Syn.shift,one] using hS.shift.wk
    have e := (mirror_at f i (sh S*num 4) data (le_of_lt hi)).eqTrans
      ((add_congr (.eqRefl _) (row_symmetric m i (sh q) (sh A) (sh B) (sh S) hs (le_of_lt hi))).eqTrans
        (added_term f f i data data).eqSymm)
    simpa only [f,d,N,Δ,data,sh,i,termwiseEq,Syn.shift,subst_mirrorData,subst_segmentData,subst_pairT,
      PTm.subst_mul,subst_num,ConciseIPRA.PTm.subst_zero] using
        rationalEq_congr e.eqSymm (.eqRefl _) (.eqRefl _)
  exact bridge.eqTrans (sum_additive f f N d d)

theorem bernoulli_fold (m : ℕ) (q A B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] bernoulliSum m q A B S zero (S*num 8) ≐
      add (add (bernoulliSum m q A B S zero (S*num 4)) (bernoulliSum m q A B S zero (S*num 4)))
        (sampleAt m S (S*num 4)) := by
  let f := bernoulliBody m
  let d := segmentData q A B S zero
  let N := S*num 4
  let M := S*num 8
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have e : Γ ⊢[PRAAx] M ≐ N+N := by dsimp [M,N]; ipra_ring
  have last : Γ ⊢[PRAAx] term f M d ≐ fraction zero one :=
    (sample_at m M q A B S).eqTrans (endpoint_samples_zero (m+1) M hM).2
  have cancel : Γ ⊢[PRAAx] add (sum f M d) (term f M d) ≐ sum f M d :=
    (add_congr (.eqRefl _) last).eqTrans (add_zero_right _ (sum_well_formed f M d))
  exact cancel.eqSymm.eqTrans
    ((add_congr (sum_congr f e (.eqRefl d)) (congrInst2 f e (.eqRefl d))).eqTrans
      ((mirror_sum f N d).eqTrans (add_congr (sum_symmetric m q A B S hS) (sample_at m N q A B S))))

theorem bernoulli_average (m : ℕ) (q A B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] multiply (fraction one (S*num 8)) (bernoulliSum m q A B S zero (S*num 8)) ≐
      add (multiply (fraction one (S*num 4)) (bernoulliSum m q A B S zero (S*num 4)))
        (multiply (fraction one (S*num 8)) (sampleAt m S (S*num 4))) := by
  let N := S*num 4
  let c := fraction one (S*num 8)
  let v := bernoulliSum m q A B S zero N
  have hv : Γ ⊢[PRAAx] RationalNormalForm.wellFormed v := sum_well_formed _ _ _
  have unit := (multiply_one_right v hv).eqSymm
  have factor : Γ ⊢[PRAAx] add v v ≐ multiply (fraction two one) v :=
    (add_congr unit unit).eqTrans ((multiply_add v _ _).eqSymm.eqTrans
      ((multiply_congr (.eqRefl v) ((count_add one one).eqTrans (fraction_congr (by ipra_ring) (.eqRefl one)))).eqTrans
        (multiply_commutative _ _)))
  have scale : Γ ⊢[PRAAx] multiply c (add v v) ≐ multiply (fraction one N) v :=
    (multiply_congr (.eqRefl c) factor).eqTrans
      ((multiply_associative _ _ _).eqSymm.eqTrans
        ((multiply_congr (multiply_commutative c (fraction two one)) (.eqRefl v)).eqTrans
          ((multiply_associative _ _ _).eqTrans (double_scale S v hS))))
  exact (multiply_congr (.eqRefl c) (bernoulli_fold m q A B S hS)).eqTrans
    ((multiply_add c _ _).eqTrans (add_congr scale (.eqRefl _)))

theorem actual_centered_Bernoulli_half_grid_average_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (le one (var 3) ⟶
      multiply (fraction one (var 3*num 8)) (bernoulliSum m (var 0) (var 1) (var 2) (var 3) zero (var 3*num 8)) ≐
        add (multiply (fraction one (var 3*num 4)) (bernoulliSum m (var 0) (var 1) (var 2) (var 3) zero (var 3*num 4)))
          (multiply (fraction one (var 3*num 8)) (sampleAt m (var 3) (var 3*num 4)))) :=
  closeUniv 4 (.impI (bernoulli_average m _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedBernoulliFold
