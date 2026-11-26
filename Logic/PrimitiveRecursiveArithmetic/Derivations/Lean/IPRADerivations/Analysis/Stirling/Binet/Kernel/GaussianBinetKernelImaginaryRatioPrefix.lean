import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelImaginaryRatioRows
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamily
import IPRADerivations.Analysis.Polynomials.GaussianRationalCoefficientScaling

/-!
# Exact finite original Binet prefix at a frozen imaginary ratio

For a rational time (t=A/B) and the fixed original observation (π_p),
the actual rational prefix programs satisfy `t² K_{N,p}(t) = r S_N(r)`
at (r=t/(2π_p)). Quantifier-free induction keeps the prefix length
internal.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelImaginaryRatioPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelImaginaryRatioRows (ratioNumerator ratioDenominator rational_time_row)
open GaussianBinetKernelRows (rowF rowBody rowData inputData row_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right)
open GaussianSineProductImaginaryLogDerivative (rationalReal logarithmRow logarithmSum logarithm_sum_succ)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawPrefix (p N A B : PTm n) : PTm n := GaussianNamedFiniteSumFamily.finite rowF rowBody p N (inputData A B)
def timeSquare (A B : PTm n) : PTm n := fraction (A*A) (B*B)
def ratio (p A B : PTm n) : PTm n := rationalReal (ratioNumerator p A) (ratioDenominator p B)

@[simp] theorem subst_rawPrefix {m : ℕ} (σ : Fin n → PTm m) (p N A B : PTm n) :
    Syn.subst σ (rawPrefix p N A B) = rawPrefix (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [rawPrefix,GaussianNamedFiniteSumFamily.finite,inputData]
@[simp] theorem subst_timeSquare {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (timeSquare A B) = timeSquare (Syn.subst σ A) (Syn.subst σ B) := by simp [timeSquare]
@[simp] theorem subst_ratio {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (ratio p A B) = ratio (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [ratio]

private def prefixLaw (p N A B : PTm n) : Fm PTm n :=
  qmul (timeSquare A B) (rawPrefix p N A B) ≐
    qmul (ratio p A B) (logarithmSum (ratioNumerator p A) (ratioDenominator p B) N)

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (p N A B : PTm n) :
    (prefixLaw p N A B).subst σ = prefixLaw (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [prefixLaw]

private theorem prefix_zero (p A B : PTm n) : Γ ⊢[PRAAx] prefixLaw p zero A B := by
  let a := ratioNumerator p A
  let b := ratioDenominator p B
  have x : Γ ⊢[PRAAx] rawPrefix p zero A B ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
  have y : Γ ⊢[PRAAx] logarithmSum a b zero ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
  exact ((qmul_congr (.eqRefl _) x).eqTrans (qmul_zero_right _)).eqTrans
    ((qmul_congr (.eqRefl _) y).eqTrans (qmul_zero_right _)).eqSymm

private theorem prefix_step (p N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] prefixLaw p N A B) : Γ ⊢[PRAAx] prefixLaw p (succ N) A B := by
  let a := ratioNumerator p A
  let b := ratioDenominator p B
  let t := timeSquare A B
  let r := ratio p A B
  let u := ap2 rowF p (rowData N A B)
  let v := logarithmRow N a b
  let body := GaussianNamedFiniteSumFamily.body rowF rowBody
  have term := (GaussianNamedFiniteSumFamily.term_at (Γ := Γ) rowF rowBody N p (inputData A B)).eqTrans
    (congrAp2 rowF (.eqRefl p) (row_at N A B))
  have left : Γ ⊢[PRAAx] rawPrefix p (succ N) A B ≐ GaussianRationalHorner.qadd (rawPrefix p N A B) u :=
    (GaussianRationalFiniteSum.sum_succ body N (pairT p (inputData A B))).eqTrans (qadd_congr (.eqRefl _) term)
  have right := logarithm_sum_succ (Γ := Γ) a b N
  have row := rational_time_row p N A B hB
  exact (qmul_congr (.eqRefl t) left).eqTrans ((qmul_add t (rawPrefix p N A B) u).eqTrans
    ((qadd_congr ih row).eqTrans ((qmul_add r (logarithmSum a b N) v).eqSymm.eqTrans
      (qmul_congr (.eqRefl r) right.eqSymm))))

theorem rational_time_prefix (p N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (timeSquare A B) (rawPrefix p N A B) ≐
      qmul (ratio p A B) (logarithmSum (ratioNumerator p A) (ratioDenominator p B) N) := by
  let sh (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,one] using hB.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (sh p) (var 0) (sh A) (sh B)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,sh,Syn.subst_inst_shift] using prefix_zero p A B
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,sh,subst_repl_shift]
      exact prefix_step (sh p) (var 0) (sh A) (sh B) hs.wk Prf.hyp0
  change Γ ⊢[PRAAx] prefixLaw p N A B
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,sh,Syn.subst_inst_shift] using all.allE N

theorem actual_frozen_ratio_Binet_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ prefixLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (rational_time_prefix _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelImaginaryRatioPrefix
