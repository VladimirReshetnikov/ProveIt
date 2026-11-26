import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumAlgebra

/-!
# Grouping the original finite sum at numerical cut points

The piece from one cut to the next uses the original offset summand
and the exact difference of the two cut indices. Summing those
pieces gives the same original prefix sum. Repeated cuts contribute
the original empty sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSum

open_ipra
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open GaussianRationalFiniteSum (sum sum_canonical sum_index_congr)
open GaussianRationalSumAlgebra (qadd_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def increasing (cut : PR 2) (d : PTm n) : Fm PTm n :=
  .all (le (ap2 cut (var 0) (Syn.shift d)) (ap2 cut (succ (var 0)) (Syn.shift d)))

def block (cut : PR 2) (f : PTm 2) (i d x : PTm n) : PTm n :=
  sum (offB f) (monus (ap2 cut (succ i) d) (ap2 cut i d)) (pairT (ap2 cut i d) x)

def blockBody (cut : PR 2) (f : PTm 2) : PTm 2 :=
  block cut f (var 0) (fstT (var 1)) (sndT (var 1))

def prefixLaw (cut : PR 2) (f : PTm 2) (k d x : PTm n) : Fm PTm n :=
  qadd (sum f (ap2 cut zero d) x) (sum (blockBody cut f) k (pairT d x)) ≐ sum f (ap2 cut k d) x

ipra_subst increasing [Syn.subst_shift, Syn.shift_subst]

ipra_subst block

ipra_subst prefixLaw

theorem cut_step (cut : PR 2) (d i : PTm n) (h : Γ ⊢[PRAAx] increasing cut d) :
    Γ ⊢[PRAAx] le (ap2 cut i d) (ap2 cut (succ i) d) := by
  simpa only [increasing,subst_le,subst_ap2,ConciseIPRA.PTm.subst_succ,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

theorem block_at (cut : PR 2) (f : PTm 2) (i d x : PTm n) :
    Γ ⊢[PRAAx] inst2 (blockBody cut f) i (pairT d x) ≐ block cut f i d x := by
  simp only [blockBody,inst2,subst_block,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have left := congrAp2 (Γ := Γ) cut (.eqRefl i) (fst_pair d x)
  have right := congrAp2 (Γ := Γ) cut (.eqRefl (succ i)) (fst_pair d x)
  exact sum_index_congr _ (congrMonus right left) (congrPairT left (snd_pair d x))

theorem original_prefix_step (cut : PR 2) (f : PTm 2) (i d x : PTm n)
    (h : Γ ⊢[PRAAx] increasing cut d) :
    Γ ⊢[PRAAx] sum f (ap2 cut (succ i) d) x ≐ qadd (sum f (ap2 cut i d) x) (block cut f i d x) :=
  (sum_index_congr f (eq_add_of_le (cut_step cut d i h)) (.eqRefl x)).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split f (ap2 cut i d) (monus (ap2 cut (succ i) d) (ap2 cut i d)) x)

theorem grouped_prefix_base (cut : PR 2) (f : PTm 2) (d x : PTm n) :
    Γ ⊢[PRAAx] prefixLaw cut f zero d x :=
  (qadd_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_zero _ _)).eqTrans
    (GaussianReciprocalHorner.qadd_zero_right _ (sum_canonical _ _ _))

theorem grouped_prefix_step (cut : PR 2) (f : PTm 2) (i d x : PTm n) (h : Γ ⊢[PRAAx] increasing cut d)
    (ih : Γ ⊢[PRAAx] prefixLaw cut f i d x) : Γ ⊢[PRAAx] prefixLaw cut f (succ i) d x := by
  let a := sum f (ap2 cut zero d) x
  let b := sum (blockBody cut f) i (pairT d x)
  let c := block cut f i d x
  have e : Γ ⊢[PRAAx] sum (blockBody cut f) (succ i) (pairT d x) ≐ qadd b c :=
    (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl b) (block_at cut f i d x))
  exact (qadd_congr (.eqRefl a) e).eqTrans ((qadd_associative a b c).eqSymm.eqTrans
    ((qadd_congr ih (.eqRefl c)).eqTrans (original_prefix_step cut f i d x h).eqSymm))

theorem grouped_prefix (cut : PR 2) (f : PTm 2) (k d x : PTm n) (h : Γ ⊢[PRAAx] increasing cut d) :
    Γ ⊢[PRAAx] prefixLaw cut f k d x := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw cut f (var 0) (Syn.shift d) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using grouped_prefix_base cut f d x
    · have h' : Γ.map Fm.shift ⊢[PRAAx] increasing cut (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using h.shift
      simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        grouped_prefix_step cut f (var 0) (Syn.shift d) (Syn.shift x) h'.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem grouped_from_zero (cut : PR 2) (f : PTm 2) (k d x : PTm n)
    (h : Γ ⊢[PRAAx] increasing cut d) (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero) :
    Γ ⊢[PRAAx] sum (blockBody cut f) k (pairT d x) ≐ sum f (ap2 cut k d) x := by
  have e := (sum_index_congr f h0 (.eqRefl x)).eqTrans (GaussianRationalFiniteSum.sum_zero f x)
  exact ((qadd_congr e (.eqRefl _)).eqTrans (qzero_add _ (sum_canonical _ _ _))).eqSymm.eqTrans
    (grouped_prefix cut f k d x h)

theorem actual_grouped_finite_sum_closed (cut : PR 2) (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (increasing cut (var 1) ⟶ (ap2 cut zero (var 1) ≐ zero) ⟶
      sum (blockBody cut f) (var 0) (pairT (var 1) (var 2)) ≐ sum f (ap2 cut (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (grouped_from_zero cut f _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSum
