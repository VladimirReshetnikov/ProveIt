import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumSegments
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFiniteSumReversal

/-!
# Reversal of the scalar rational finite sum

Reversing the internal indices of a fixed rational row leaves its
canonical sum code unchanged. The original accumulator reads raw
rational codes, so the proof applies without a canonicality premise
on any input row.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSumReversal

open_ipra
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalFiniteSumReversal (data reverseBody reverse_body_at first_at)
open RationalAlgebra (add_congr add_associative add_commutative)
open RationalArithmetic (add add_guard)
open RationalArgmin (rationalEq_congr)
open RationalFiniteSum (term sum termwiseEq sum_ext subst_sum)
open RationalReciprocalPowerTail (add_zero_right zero_fraction)
open RationalSumSegments (sum_congr split)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A scalar sum can be viewed from its first index. The first row
is still fed directly to rational addition, even when raw. -/
theorem sum_first (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] sum f (succ N) x ≐ add (term f zero x) (sum (offB f) N (pairT (succ zero) x)) := by
  let tail := sum (offB f) N (pairT (succ zero) x)
  have singleton : Γ ⊢[PRAAx] sum f one x ≐
      add (GaussianEuclideanDistanceName.fraction zero one) (term f zero x) :=
    (RationalFiniteSum.sum_succ f zero x).eqTrans (add_congr ((RationalFiniteSum.sum_zero f x).eqTrans zero_fraction.eqSymm) (.eqRefl _))
  have head : Γ ⊢[PRAAx]
      add (add (GaussianEuclideanDistanceName.fraction zero one) (term f zero x)) tail ≐
        add (term f zero x) tail :=
    (add_associative _ _ _).eqTrans ((add_commutative _ _).eqTrans (add_zero_right _ (add_guard _ _)))
  have count : Γ ⊢[PRAAx] succ N ≐ one+N := by ipra_ring
  exact (sum_congr f count (.eqRefl x)).eqTrans
    ((split f one N x).eqTrans ((add_congr singleton (.eqRefl tail)).eqTrans head))

private theorem reverse_tail_at (f : PTm 2) (i N x : PTm n) :
    Γ ⊢[PRAAx] term (offB (reverseBody f)) i (pairT (succ zero) (data (succ N) x)) ≐
      term (reverseBody f) i (data N x) := by
  have index : Γ ⊢[PRAAx] one+i ≐ succ i := by ipra_ring
  exact (offset_at (reverseBody f) (succ zero) i (data (succ N) x)).eqTrans
    ((congrInst2 (reverseBody f) index (.eqRefl _)).eqTrans
      ((reverse_body_at f (succ i) (succ N) x).eqTrans
        ((congrInst2 f (succ_monus_succ N (succ i)) (.eqRefl _)).eqTrans
          (reverse_body_at f i N x).eqSymm)))

private theorem reverse_tail (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] sum (offB (reverseBody f)) N (pairT (succ zero) (data (succ N) x)) ≐
      sum (reverseBody f) N (data N x) := by
  apply sum_ext
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have h := reverse_tail_at (Γ := Δ) f (var 0) (Syn.shift N) (Syn.shift x)
  simpa only [Δ,termwiseEq,Syn.shift,subst_pairT,
    GaussianRationalFiniteSumReversal.subst_data,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using
    rationalEq_congr h.eqSymm (.eqRefl _) (.eqRefl _)

def reversal (f : PTm 2) (N x : PTm n) : Fm PTm n :=
  sum (reverseBody f) N (data N x) ≐ sum f N x

ipra_subst reversal

/-- Each successor trades the last term of the original sum against
the first term of its reversal. -/
theorem reverse (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] reversal f N x := by
  have all : Γ ⊢[PRAAx] .all (reversal f (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_reversal,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (RationalFiniteSum.sum_zero _ _).eqTrans (RationalFiniteSum.sum_zero f x).eqSymm
    · simp only [subst_reversal,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let K : PTm (n+1) := var 0
      let y := Syn.shift x
      let Δ := reversal f K y :: Γ.map Fm.shift
      have step := sum_first (Γ := Δ) (reverseBody f) K (data (succ K) y)
      exact step.eqTrans ((add_congr (first_at f K y) ((reverse_tail f K y).eqTrans Prf.hyp0)).eqTrans
        ((add_commutative _ _).eqTrans (RationalFiniteSum.sum_succ f K y).eqSymm))
  simpa only [subst_reversal,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem actual_scalar_rational_sum_reversal_closed (f : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (reversal f (var 0) (var 1)) :=
  closeUniv 2 (reverse f _ _)

end LeanProofs.IPRA.Analysis.RationalSumReversal
