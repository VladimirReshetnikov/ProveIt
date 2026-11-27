import IPRADerivations.Analysis.Polynomials.Products.Convolution.GaussianRationalLowCoefficientConvolution

/-!
# The actual weighted Cauchy coefficient identity

The numerical coefficient weight e splits as i+(e-i) in the SAME actual
low-exponent convolution. Original normalized scalar multiplication and
the already proved finite-sum transports derive the coefficient Leibniz
identity, with explicit weighted ORIGINAL factors. No derivative, weighted
convolution, or Bell law is supplied as an input. No sum/product recursion
is added. This is a finite algebra prerequisite, not analytic C4.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalWeightedCoefficientConvolution

open_ipra
open GaussianRationalHorner (qmul qadd)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalNaturalScale (natScale natScale_congr natScale_as_product natScale_add natScale_product naturalPoint)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient data getP getQ getN getM getE)
open GaussianRationalFiniteSum (sum)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leftTerm (P Q N M e i : PTm n) : PTm n :=
  qmul (natScale i (entry P (monus N i))) (entry Q (monus M (monus e i)))
def rightTerm (P Q N M e i : PTm n) : PTm n :=
  qmul (entry P (monus N i)) (natScale (monus e i) (entry Q (monus M (monus e i))))
def leftBody : PTm 2 := leftTerm (getP (var 1)) (getQ (var 1)) (getN (var 1)) (getM (var 1)) (getE (var 1)) (var 0)
def rightBody : PTm 2 := rightTerm (getP (var 1)) (getQ (var 1)) (getN (var 1)) (getM (var 1)) (getE (var 1)) (var 0)
def leftSum (P Q N M e : PTm n) : PTm n := sum leftBody (succ e) (data P Q N M e)
def rightSum (P Q N M e : PTm n) : PTm n := sum rightBody (succ e) (data P Q N M e)
ipra_subst leftTerm
ipra_subst rightTerm
ipra_subst leftSum
ipra_subst rightSum

theorem left_at (P Q N M e i : PTm n) : Γ ⊢[PRAAx]
    inst2 leftBody i (data P Q N M e) ≐ leftTerm P Q N M e i := by
  simp only [leftBody,inst2,subst_leftTerm,getP,getQ,getN,getM,getE,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (natScale_congr (.eqRefl _)
      (entry_congr (GaussianRationalLowCoefficientConvolution.get_p _ _ _ _ _)
        (congrMonus (GaussianRationalLowCoefficientConvolution.get_n _ _ _ _ _) (.eqRefl _))))
    (entry_congr (GaussianRationalLowCoefficientConvolution.get_q _ _ _ _ _)
      (congrMonus (GaussianRationalLowCoefficientConvolution.get_m _ _ _ _ _)
        (congrMonus (GaussianRationalLowCoefficientConvolution.get_e _ _ _ _ _) (.eqRefl _))))
theorem right_at (P Q N M e i : PTm n) : Γ ⊢[PRAAx]
    inst2 rightBody i (data P Q N M e) ≐ rightTerm P Q N M e i := by
  simp only [rightBody,inst2,subst_rightTerm,getP,getQ,getN,getM,getE,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (entry_congr (GaussianRationalLowCoefficientConvolution.get_p _ _ _ _ _)
      (congrMonus (GaussianRationalLowCoefficientConvolution.get_n _ _ _ _ _) (.eqRefl _)))
    (natScale_congr (congrMonus (GaussianRationalLowCoefficientConvolution.get_e _ _ _ _ _) (.eqRefl _))
      (entry_congr (GaussianRationalLowCoefficientConvolution.get_q _ _ _ _ _)
        (congrMonus (GaussianRationalLowCoefficientConvolution.get_m _ _ _ _ _)
          (congrMonus (GaussianRationalLowCoefficientConvolution.get_e _ _ _ _ _) (.eqRefl _)))))

theorem left_scale_product (t a b : PTm n) : Γ ⊢[PRAAx] natScale t (qmul a b) ≐ qmul (natScale t a) b :=
  (natScale_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative a b)).eqTrans
    ((natScale_product t b a).eqSymm.eqTrans (GaussianRationalPowerAlgebra.qmul_commutative b (natScale t a)))

theorem term_weight_split (P Q N M e i : PTm n) (hi : Γ ⊢[PRAAx] le i e) : Γ ⊢[PRAAx]
    natScale e (GaussianRationalLowCoefficientConvolution.term P Q N M e i) ≐
      qadd (leftTerm P Q N M e i) (rightTerm P Q N M e i) :=
  (natScale_congr (eq_add_of_le hi) (.eqRefl _)).eqTrans
    ((natScale_add i (monus e i) (GaussianRationalLowCoefficientConvolution.term P Q N M e i)).eqTrans
      (qadd_congr (left_scale_product _ _ _) (natScale_product _ _ _).eqSymm))

theorem multiplied_entry_split (P Q N M e i : PTm n) (hi : Γ ⊢[PRAAx] le i e) : Γ ⊢[PRAAx]
    inst2 (GaussianRationalFiniteSum.multiplyBody GaussianRationalLowCoefficientConvolution.termBody) i
        (pairT (naturalPoint e) (data P Q N M e)) ≐
      inst2 (GaussianRationalFiniteSum.addBody leftBody rightBody) i (data P Q N M e) := by
  have hm := (GaussianRationalFiniteSum.multiply_body_at (Γ := Γ)
      GaussianRationalLowCoefficientConvolution.termBody (naturalPoint e) i (data P Q N M e)).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalLowCoefficientConvolution.term_at P Q N M e i)).eqTrans
      ((natScale_as_product e _).eqSymm.eqTrans (term_weight_split P Q N M e i hi)))
  have ha : Γ ⊢[PRAAx] inst2 (GaussianRationalFiniteSum.addBody leftBody rightBody) i (data P Q N M e) ≐
      qadd (leftTerm P Q N M e i) (rightTerm P Q N M e i) := by
    simp only [GaussianRationalFiniteSum.inst2_addBody]
    exact qadd_congr (left_at P Q N M e i) (right_at P Q N M e i)
  exact hm.eqTrans ha.eqSymm

theorem weighted_cauchy (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient (GaussianRationalPolynomialProduct.product P Q N M) (N+M) e) ≐
      qadd (leftSum P Q N M e) (rightSum P Q N M e) := by
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual
      (GaussianRationalFiniteSum.multiplyBody GaussianRationalLowCoefficientConvolution.termBody)
      (GaussianRationalFiniteSum.addBody leftBody rightBody) (succ e)
      (pairT (naturalPoint e) (data P Q N M e)) (data P Q N M e) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ,subst_pairT,GaussianRationalNaturalScale.subst_naturalPoint,
      GaussianRationalLowCoefficientConvolution.subst_data] using
      multiplied_entry_split (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0) hi
  exact (natScale_congr (.eqRefl _) (GaussianRationalLowCoefficientConvolution.product_exponent P Q N M e hN hM)).eqTrans
    ((natScale_as_product e (GaussianRationalLowCoefficientConvolution.cauchySum P Q N M e)).eqTrans
      ((GaussianRationalFiniteSum.sum_multiply GaussianRationalLowCoefficientConvolution.termBody (naturalPoint e) (succ e) (data P Q N M e)).eqSymm.eqTrans
        ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ entries).eqTrans
          (GaussianRationalFiniteSum.sum_add leftBody rightBody (succ e) (data P Q N M e)))))

def output (P Q N M e : PTm n) : PTm n := pairT
  (natScale e (exponentCoefficient (GaussianRationalPolynomialProduct.product P Q N M) (N+M) e))
  (pairT (leftSum P Q N M e) (rightSum P Q N M e))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (P Q N M e : PTm n) : PTm n := PTm.app outputF ![P,Q,N,M,e]
ipra_subst output
ipra_subst run

theorem program_at (P Q N M e : PTm n) : Γ ⊢[PRAAx] run P Q N M e ≐ output P Q N M e := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![P,Q,N,M,e]
theorem returned_weighted_coefficient (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    fstT (run P Q N M e) ≐ natScale e (exponentCoefficient (GaussianRationalPolynomialProduct.product P Q N M) (N+M) e) :=
  (program_at P Q N M e).fstE
theorem returned_left (P Q N M e : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run P Q N M e)) ≐ leftSum P Q N M e :=
  (program_at P Q N M e).sndE.fstE
theorem returned_right (P Q N M e : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run P Q N M e)) ≐ rightSum P Q N M e :=
  (program_at P Q N M e).sndE.sndE
theorem returned_agreement (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    fstT (run P Q N M e) ≐ qadd (fstT (sndT (run P Q N M e))) (sndT (sndT (run P Q N M e))) :=
  (returned_weighted_coefficient P Q N M e).eqTrans ((weighted_cauchy P Q N M e hN hM).eqTrans
    (qadd_congr (returned_left P Q N M e).eqSymm (returned_right P Q N M e).eqSymm))

theorem actual_raw_left_product_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (natScale (var 0) (qmul (var 1) (var 2)) ≐ qmul (natScale (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (left_scale_product _ _ _)
theorem actual_bounded_term_weight_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 4) ⟶ natScale (var 4) (GaussianRationalLowCoefficientConvolution.term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐
      qadd (leftTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (rightTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (term_weight_split _ _ _ _ _ _ Prf.hyp0))
theorem actual_weighted_coefficient_cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      natScale (var 4) (exponentCoefficient (GaussianRationalPolynomialProduct.product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) (var 4)) ≐
        qadd (leftSum (var 0) (var 1) (var 2) (var 3) (var 4)) (rightSum (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (weighted_cauchy _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_weighted_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_weighted_coefficient_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶ fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      qadd (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (.impI (returned_agreement _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalWeightedCoefficientConvolution
