import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumConstants
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct

/-!
# Exact scalar rational sum splitting at an internal index

A finite prefix and the shifted suffix add to the original finite
sum. The comparison is literal equality of canonical codes and uses
the original scalar sum constructor on both segments.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSumSegments

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalFiniteProduct (offset_at)
open RationalAlgebra (add_congr add_associative)
open RationalArithmetic (add)
open RationalFiniteSum (sum term sum_at sumCodeF sum_well_formed subst_sum)
open RationalReciprocalPowerTail (add_zero_right zero_fraction)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sum_congr (body : PTm 2) {N N' x x' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx] sum body N x ≐ sum body N' x' :=
  (sum_at body N x).eqSymm.eqTrans ((congrAp2 (sumCodeF body) hN hx).eqTrans (sum_at body N' x'))

def splitLaw (body : PTm 2) (N M x : PTm n) : Fm PTm n :=
  sum body (N+M) x ≐ add (sum body N x) (sum (offB body) M (pairT N x))

@[simp] theorem subst_splitLaw {l : ℕ} (σ : Fin n → PTm l) (body : PTm 2) (N M x : PTm n) :
    (splitLaw body N M x).subst σ = splitLaw body (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) := by
  simp [splitLaw]

private theorem split_zero (body : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] splitLaw body N zero x :=
  (sum_congr body (add_zero N) (.eqRefl x)).eqTrans
    ((add_congr (.eqRefl _) ((RationalFiniteSum.sum_zero (offB body) (pairT N x)).eqTrans zero_fraction.eqSymm)).eqTrans
      (add_zero_right (sum body N x) (sum_well_formed _ _ _))).eqSymm

private theorem split_succ (body : PTm 2) (N M x : PTm n)
    (h : Γ ⊢[PRAAx] splitLaw body N M x) : Γ ⊢[PRAAx] splitLaw body N (succ M) x := by
  have step := (sum_congr (Γ := Γ) body (add_succ N M) (.eqRefl x)).eqTrans (RationalFiniteSum.sum_succ body (N+M) x)
  have atTerm : Γ ⊢[PRAAx] term (offB body) M (pairT N x) ≐ term body (N+M) x := offset_at body N M x
  exact step.eqTrans ((add_congr h atTerm.eqSymm).eqTrans
    ((add_associative _ _ _).eqTrans (add_congr (.eqRefl _) (RationalFiniteSum.sum_succ _ _ _).eqSymm)))

theorem split (body : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx] splitLaw body N M x := by
  have h : Γ ⊢[PRAAx] .all (splitLaw body (Syn.shift N) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using split_zero (Γ := Γ) body N x
    · simp only [subst_splitLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact split_succ body (Syn.shift N) (var 0) (Syn.shift x) Prf.hyp0
  simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE M

theorem actual_rational_segment_split_closed (body : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (splitLaw body (var 0) (var 1) (var 2)) :=
  closeUniv 3 (split body _ _ _)

end LeanProofs.IPRA.Analysis.RationalSumSegments
