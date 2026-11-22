import IPRADerivations.Analysis.RationalAnnihilatorOnSpan
import IPRADerivations.Analysis.RationalAnnihilatorPolynomialWeight

/-!
# The actual rational polynomial and norm certificate of a proper span

The same rational free-column vector supplies both the nonzero coefficient
and the exact original span zeros. The compiled polynomial has bounded
weight, and the original rational norm has that computed degree.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSuperellipticSpanCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianWeightedMonomialBasis (count)
open RationalSuperellipticNormDegree (d norm input pointInput)
open RationalSuperellipticSubspace (curveInput curvePoints properSpan pointMembership)
open RationalGaussianEmbedding (scalarZero scalarOne)
open RationalAnnihilatorPolynomial (polynomial)
open RationalAnnihilatorPolynomialWeight (nonzeroLambda)
open RationalPolynomialWeightedDegreeGaussianEmbedding (weightedDegree)
open RationalCurvePointsGaussianEmbedding (functionZeros)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def vector (f m c L A R : PTm n) : PTm n := RationalOriginalAnnihilator.vector A R (count m (d f c) L)

def compiled (f m c L A R : PTm n) : PTm n := polynomial (vector f m c L A R) m (d f c) L

def weight (f m c L A R : PTm n) : PTm n := weightedDegree (compiled f m c L A R) m L (d f c)

def certificate (f m c L P A R : PTm n) : Fm PTm n :=
  RationalSuperellipticNormDegree.certificate f (compiled f m c L A R) m L c ⋏
    (functionZeros (compiled f m c L A R) m P ⋏ (le (length P) (weight f m c L A R) ⋏ le (weight f m c L A R) L))

theorem unit_nonzero (v s : PTm n) (h : Γ ⊢[PRAAx] entry v s ≐ scalarOne) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalEq (entry v s) scalarZero) := by
  have eq := (RationalPolynomialGaussianEmbedding.embed_congr h).eqTrans RationalGaussianEmbedding.embed_one
  exact .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero
    (eq.wk.eqSymm.eqTrans ((RationalGaussianEmbedding.zero_iff (entry v s)).wk.iffMpr Prf.hyp0)))

theorem original_nonzero_witness (a m e L s : PTm n) (hs : Γ ⊢[PRAAx] lt s (count m e L))
    (hu : Γ ⊢[PRAAx] entry a s ≐ scalarOne) : Γ ⊢[PRAAx] nonzeroLambda a m e L := by
  refine .exI s ?_
  simpa only [nonzeroLambda,Fm.subst_and,subst_lt,subst_neg,RationalArgmin.subst_rationalEq,
    Foundations.MasterCertificate.subst_entry,GaussianWeightedMonomialBasis.subst_count,
    RationalGaussianEmbedding.subst_scalarZero,Syn.inst_zero,Syn.subst_var,Syn.subst_inst_shift] using
    Prf.andI hs (unit_nonzero a s hu)

theorem actual_norm_input (f G m c L : PTm n) (hf : Γ ⊢[PRAAx] curveInput f m c)
    (hShape : Γ ⊢[PRAAx] GaussianPolynomialMonicCompanion.rowShape G m L)
    (hNZ : Γ ⊢[PRAAx] RationalPolynomialWeightedDegreeGaussianEmbedding.nonzeroRows G m L) : Γ ⊢[PRAAx] input f G m L c := by
  have bounds := Prf.andE₂ (Prf.andE₂ hf)
  exact .andI (.andE₁ hf) (.andI (.andE₁ (.andE₂ hf)) (.andI (.andE₁ bounds)
    (.andI (.andE₁ (.andE₂ bounds)) (.andI (.andE₂ (.andE₂ bounds)) (.andI hShape hNZ)))))

theorem constructed_certificate (f m c L P A R : PTm n) (hf : Γ ⊢[PRAAx] curveInput f m c)
    (hProper : Γ ⊢[PRAAx] properSpan A R (count m (d f c) L))
    (hPts : Γ ⊢[PRAAx] curvePoints f m P) (hSpan : Γ ⊢[PRAAx] pointMembership m (d f c) L P A R) : Γ ⊢[PRAAx]
    certificate f m c L P A R := by
  let e := d f c
  let a := vector f m c L A R
  let G := compiled f m c L A R
  have hm : Γ ⊢[PRAAx] le one m := le_trans (le_succ_self one) (.andE₁ hf)
  have rank := RationalSuperellipticSubspace.rank_deficit A R (count m e L) hProper
  have hv := RationalOriginalAnnihilator.certificate_of_deficit A R (count m e L) rank
  have hNZ := original_nonzero_witness a m e L (RationalOriginalAnnihilator.free A R (count m e L))
    (.andE₁ (.andE₂ hv)) (.andE₁ (.andE₂ (.andE₂ hv)))
  have hWeight := RationalAnnihilatorPolynomialWeight.weighted_bound a m e L (.andI hm (.andI (.andE₁ hv) hNZ))
  have hn := actual_norm_input f G m c L hf (RationalAnnihilatorPolynomial.polynomial_shape a m e L)
    (RationalAnnihilatorPolynomialWeight.nonzero_rows a m e L hNZ)
  have zeros := RationalAnnihilatorOnSpan.computed_polynomial_zeros A R m e L P hm rank hSpan
  have P' : Γ ⊢[PRAAx] pointInput f G m P := .andI (.andE₁ hPts) (.andI (.andE₂ hPts) zeros)
  exact .andI (RationalSuperellipticNormDegree.exact_norm_degree f G m L c hn)
    (.andI zeros (.andI (RationalSuperellipticNormDegree.weighted_zero_bound f G m L c P hn P') hWeight))

def output (f m c L A R : PTm n) : PTm n := pairT (vector f m c L A R)
  (pairT (compiled f m c L A R) (norm f (compiled f m c L A R) m L c))

def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))

theorem output_at (f m c L A R : PTm n) : Γ ⊢[PRAAx] app outputF ![f,m,c,L,A,R] ≐ output f m c L A R := by
  simpa [outputF,output,compiled,vector,d,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![f,m,c,L,A,R]

theorem actual_rational_superelliptic_span_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) ⟶ properSpan (var 5) (var 6) (count (var 1) (d (var 0) (var 2)) (var 3)) ⟶
      curvePoints (var 0) (var 1) (var 4) ⟶ pointMembership (var 1) (d (var 0) (var 2)) (var 3) (var 4) (var 5) (var 6) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (constructed_certificate _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_rational_superelliptic_span_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (app outputF ![var 0,var 1,var 2,var 3,var 4,var 5] ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (output_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalSuperellipticSpanCertificate
