import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantTerms
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProductDegree
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct
import IPRADerivations.Analysis.RationalArithmetic.Fibers.GaussianRationalCurveFibers
import IPRADerivations.Analysis.RationalArithmetic.GaussianScalarColumnSelection
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Core.CongruenceTactic

/-!
# Computed degree and leading values of the actual determinant stages

The SAME existing determinant stage reads each actual selected cell and
uses its original polynomial-product recursion. Its success bit reflects
all original factor flags; a zero factor forces the actual stage zero.
Genuine bounded/QF induction derives first, degree and leading-product
identities. Raw factors remain normalized by the real field operations.
All dimensions, word codes, prefixes and persistent data are numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTermDegree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms
  (factor factorBody widthBody data factor_body_at width_at stage stage_zero stage_succ stage_length
    term signPoint sign_even sign_odd sign_canonical term_coefficient)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
  (first flag degree nonzeroCoefficients allZero flag_cases flag_one_of_nonzero nonzero_of_flag_one
    flag_one_of_found flag_zero_of_all_zero all_zero_of_flag_zero success_index first_zero_prefix)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree
  (leading leading_canonical leading_nonzero first_exact product_success product_first product_degree
    product_leading product_failure_left product_failure_right)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qone_canonical qzero_canonical qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant
  (recode recode_eq recode_congr zeroPrefix zero_prefix_at)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (singleton singleton_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factorFlags (M m L w j : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift j) ⟶
  flag (factor (Syn.shift M) (Syn.shift m) (Syn.shift w) (var 0)) (Syn.shift L) ≐ one)
def firstBody : PTm 2 := first factorBody (Syn.subst ![var 1] widthBody)
def degreeBody : PTm 2 := degree factorBody (Syn.subst ![var 1] widthBody)
def leadingBody : PTm 2 := leading factorBody (Syn.subst ![var 1] widthBody)
def firstSum (M m L w j : PTm n) : PTm n := ap2 (sumF firstBody) j (data M m L w)
def degreeSum (M m L w j : PTm n) : PTm n := ap2 (sumF degreeBody) j (data M m L w)
def leadingProduct (M m L w j : PTm n) : PTm n := GaussianRationalFiniteProduct.qprod leadingBody j (data M m L w)

@[simp] theorem subst_factorFlags {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    (factorFlags M m L w j).subst σ = factorFlags (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ j) := by simp [factorFlags,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_firstSum {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (firstSum M m L w j) = firstSum (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ j) := by simp [firstSum]
@[simp] theorem subst_degreeSum {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (degreeSum M m L w j) = degreeSum (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ j) := by simp [degreeSum]
@[simp] theorem subst_leadingProduct {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (leadingProduct M m L w j) = leadingProduct (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ j) := by simp [leadingProduct]

theorem first_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    first C N ≐ first D M := by
  ipra_congr (first (var 0) (var 1) : PTm 2) with [hC, hN]
theorem flag_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    flag C N ≐ flag D M := by
  ipra_congr (flag (var 0) (var 1) : PTm 2) with [hC, hN]
theorem degree_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    degree C N ≐ degree D M := congrMonus hN (first_congr hC hN)
theorem leading_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    leading C N ≐ leading D M := recode_congr (entry_congr hC (first_congr hC hN))

theorem first_body_at (M m L w j : PTm n) : Γ ⊢[PRAAx]
    inst2 firstBody j (data M m L w) ≐ first (factor M m w j) L := by
  simpa [inst2,firstBody,Syn.subst_subst,widthBody] using first_congr (Γ := Γ)
    (factor_body_at M m L w j) (width_at M m L w)
theorem degree_body_at (M m L w j : PTm n) : Γ ⊢[PRAAx]
    inst2 degreeBody j (data M m L w) ≐ degree (factor M m w j) L := by
  simpa [inst2,degreeBody,Syn.subst_subst,widthBody] using degree_congr (Γ := Γ)
    (factor_body_at M m L w j) (width_at M m L w)
theorem leading_body_at (M m L w j : PTm n) : Γ ⊢[PRAAx]
    inst2 leadingBody j (data M m L w) ≐ leading (factor M m w j) L := by
  simpa [inst2,leadingBody,Syn.subst_subst,widthBody] using leading_congr (Γ := Γ)
    (factor_body_at M m L w j) (width_at M m L w)
theorem first_sum_zero (M m L w : PTm n) : Γ ⊢[PRAAx] firstSum M m L w zero ≐ zero := sum_zero _ _
theorem degree_sum_zero (M m L w : PTm n) : Γ ⊢[PRAAx] degreeSum M m L w zero ≐ zero := sum_zero _ _
theorem leading_product_zero (M m L w : PTm n) : Γ ⊢[PRAAx] leadingProduct M m L w zero ≐ qone :=
  GaussianRationalFiniteProduct.product_zero _ _
theorem first_sum_succ (M m L w j : PTm n) : Γ ⊢[PRAAx]
    firstSum M m L w (succ j) ≐ firstSum M m L w j+first (factor M m w j) L :=
  (sum_succ _ _ _).eqTrans (congrAdd (.eqRefl _) (first_body_at _ _ _ _ _))
theorem degree_sum_succ (M m L w j : PTm n) : Γ ⊢[PRAAx]
    degreeSum M m L w (succ j) ≐ degreeSum M m L w j+degree (factor M m w j) L :=
  (sum_succ _ _ _).eqTrans (congrAdd (.eqRefl _) (degree_body_at _ _ _ _ _))
theorem leading_product_succ (M m L w j : PTm n) : Γ ⊢[PRAAx]
    leadingProduct M m L w (succ j) ≐ qmul (leadingProduct M m L w j) (leading (factor M m w j) L) :=
  (GaussianRationalFiniteProduct.product_succ _ _ _).eqTrans
    (qmul_congr (.eqRefl _) (leading_body_at _ _ _ _ _))

theorem empty_zero_prefix (C : PTm n) : Γ ⊢[PRAAx] zeroPrefix C zero := by
  simp only [zeroPrefix,Syn.shift,ConciseIPRA.PTm.subst_zero]
  exact .allI (.impI (not_succ_le_self (var 0) _ (le_trans Prf.hyp0 (zero_le _))))
theorem singleton_first : Γ ⊢[PRAAx] first (singleton (qone : PTm n)) zero ≐ zero :=
  first_exact _ _ _ (le_refl _) (empty_zero_prefix _)
    (.impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero
      (((recode_congr (singleton_lookup _)).eqTrans (recode_eq _ qone_canonical)).wk.eqSymm.eqTrans Prf.hyp0)))
theorem singleton_success : Γ ⊢[PRAAx] flag (singleton (qone : PTm n)) zero ≐ one :=
  flag_one_of_found _ _ (lt_congr singleton_first.eqSymm (.eqRefl _) (zero_lt_succ zero))
theorem singleton_degree : Γ ⊢[PRAAx] degree (singleton (qone : PTm n)) zero ≐ zero :=
  (congrMonus (.eqRefl _) singleton_first).eqTrans (monus_self zero)
theorem singleton_leading : Γ ⊢[PRAAx] leading (singleton (qone : PTm n)) zero ≐ qone :=
  (recode_congr (entry_congr (.eqRefl _) singleton_first)).eqTrans
    ((recode_congr (singleton_lookup _)).eqTrans (recode_eq _ qone_canonical))

theorem stage_zero_success (M m L w : PTm n) : Γ ⊢[PRAAx] flag (stage M m L w zero) (zero*L) ≐ one :=
  (flag_congr (stage_zero _ _ _ _) (zero_mul _)).eqTrans singleton_success

theorem factors_at (M m L w j i : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j)
    (hi : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx] flag (factor M m w i) L ≐ one := by
  have rule : Γ ⊢[PRAAx] lt i j ⟶ flag (factor M m w i) L ≐ one := by
    simpa [factorFlags] using h.allE i
  exact .impE rule hi

theorem factors_empty (M m L w : PTm n) : Γ ⊢[PRAAx] factorFlags M m L w zero := by
  simp only [factorFlags,Syn.shift,ConciseIPRA.PTm.subst_zero]
  refine .allI (.impI ?_)
  exact not_succ_le_self (var 0) _ (le_trans Prf.hyp0 (zero_le _))

theorem factors_prefix (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w (succ j)) :
    Γ ⊢[PRAAx] factorFlags M m L w j := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] factorFlags (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (succ (Syn.shift j)) := by
    simpa only [Fm.shift,subst_factorFlags,ConciseIPRA.PTm.subst_succ,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  exact factors_at _ _ _ _ _ _ hs.wk (le_trans Prf.hyp0 (le_succ_self _))
theorem factors_last (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w (succ j)) :
    Γ ⊢[PRAAx] flag (factor M m w j) L ≐ one := factors_at _ _ _ _ _ _ h (le_refl _)
theorem factors_append (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j)
    (hj : Γ ⊢[PRAAx] flag (factor M m w j) L ≐ one) : Γ ⊢[PRAAx] factorFlags M m L w (succ j) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] factorFlags (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift j) := by
    simpa only [Fm.shift,subst_factorFlags,Syn.shift] using h.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] flag (factor (Syn.shift M) (Syn.shift m) (Syn.shift w) (Syn.shift j)) (Syn.shift L) ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianRationalPolynomialDegree.subst_flag,
      GaussianPolynomialDeterminantTerms.subst_factor,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  have bound : lt (var 0) (succ (Syn.shift j)) :: Γ.map Fm.shift ⊢[PRAAx] le (var 0) (Syn.shift j) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  refine .orE (lt_or_eq_of_le bound) ?_ ?_
  · exact factors_at _ _ _ _ _ _ hs.wk.wk Prf.hyp0
  · exact (flag_congr (GaussianPolynomialDeterminantTerms.factor_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans js.wk.wk


theorem successor_width (j L : PTm n) : Γ ⊢[PRAAx] succ j*L ≐ j*L+L := by ipra_ring

theorem product_flags_reflect (P Q N M : PTm n)
    (h : Γ ⊢[PRAAx] flag (GaussianRationalPolynomialProduct.product P Q N M) (N+M) ≐ one) :
    Γ ⊢[PRAAx] (flag P N ≐ one) ⋏ (flag Q M ≐ one) := by
  refine .andI ?_ ?_
  · refine .orE (flag_cases P N) ?_ Prf.hyp0
    exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans (product_failure_left _ _ _ _ Prf.hyp0)))
  · refine .orE (flag_cases Q M) ?_ Prf.hyp0
    exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans (product_failure_right _ _ _ _ Prf.hyp0)))

def successLaw (M m L w j : PTm n) : Fm PTm n := Fm.iff (flag (stage M m L w j) (j*L) ≐ one) (factorFlags M m L w j)
def factorsSyntax (M m L w j : PTm n) : BFm n := .all j
  (.eq (flag (factor (Syn.shift M) (Syn.shift m) (Syn.shift w) (var 0)) (Syn.shift L)) one)
def successSyntax (M m L w j : PTm n) : BFm n := .and
  (.imp (.eq (flag (stage M m L w j) (j*L)) one) (factorsSyntax M m L w j))
  (.imp (factorsSyntax M m L w j) (.eq (flag (stage M m L w j) (j*L)) one))
@[simp] theorem subst_successLaw {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    (successLaw M m L w j).subst σ = successLaw (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ j) := by simp [successLaw,Fm.iff]
theorem success_formula (M m L w j : PTm n) : formula (successSyntax M m L w j) = successLaw M m L w j := by
  simp [successSyntax,factorsSyntax,formula,successLaw,factorFlags,Syn.shift,Fm.iff]

theorem success_zero (M m L w : PTm n) : Γ ⊢[PRAAx] successLaw M m L w zero :=
  .andI (.impI (factors_empty _ _ _ _).wk) (.impI (stage_zero_success _ _ _ _).wk)
theorem success_step (M m L w j : PTm n) (h : Γ ⊢[PRAAx] successLaw M m L w j) : Γ ⊢[PRAAx]
    successLaw M m L w (succ j) := by
  refine .andI (.impI ?_) (.impI ?_)
  · let Δ := (flag (stage M m L w (succ j)) (succ j*L) ≐ one) :: Γ
    have expanded : Δ ⊢[PRAAx] flag (GaussianRationalPolynomialProduct.product (stage M m L w j) (factor M m w j) (j*L) L) (j*L+L) ≐ one :=
      (flag_congr (Γ := Γ) (stage_succ M m L w j) (successor_width j L)).wk.eqSymm.eqTrans Prf.hyp0
    have flags := product_flags_reflect _ _ _ _ expanded
    exact factors_append _ _ _ _ _ (h.wk.iffMp (.andE₁ flags)) (.andE₂ flags)
  · let Δ := factorFlags M m L w (succ j) :: Γ
    have current : Δ ⊢[PRAAx] factorFlags M m L w (succ j) := Prf.hyp0
    have before : Δ ⊢[PRAAx] flag (stage M m L w j) (j*L) ≐ one := h.wk.iffMpr (factors_prefix _ _ _ _ _ current)
    have last := factors_last _ _ _ _ _ current
    exact (flag_congr (stage_succ _ _ _ _ _) (successor_width _ _)).eqTrans
      (product_success _ _ _ _ (nonzero_of_flag_one _ _ before) (nonzero_of_flag_one _ _ last))

/-- Success of the SAME stage reflects every original declared-width factor.
The compiler performs QF induction on the actual bounded equivalence. -/
theorem stage_success_iff (M m L w j : PTm n) : Γ ⊢[PRAAx] successLaw M m L w j := by
  let A := successSyntax (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)
  have h0 : Γ ⊢[PRAAx] (formula A).subst (Syn.inst zero) := by
    simpa only [A,success_formula,subst_successLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using success_zero M m L w
  have hs : formula A :: Γ.map Fm.shift ⊢[PRAAx] (formula A).subst (repl (succ (var 0))) := by
    simp only [A,success_formula,subst_successLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
    exact success_step _ _ _ _ _ Prf.hyp0
  simpa only [A,success_formula,subst_successLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Foundations.BoundedSyntaxInduction.induction_at A j h0 hs

theorem stage_nonzero_factors (M m L w j : PTm n)
    (h : Γ ⊢[PRAAx] flag (stage M m L w j) (j*L) ≐ one) : Γ ⊢[PRAAx] factorFlags M m L w j :=
  (stage_success_iff M m L w j).iffMp h
theorem stage_success_of_factors (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) :
    Γ ⊢[PRAAx] flag (stage M m L w j) (j*L) ≐ one := (stage_success_iff M m L w j).iffMpr h
theorem stage_zero_factor (M m L w j i : PTm n) (hi : Γ ⊢[PRAAx] lt i j)
    (hz : Γ ⊢[PRAAx] flag (factor M m w i) L ≐ zero) : Γ ⊢[PRAAx] flag (stage M m L w j) (j*L) ≐ zero := by
  refine .orE (flag_cases (stage M m L w j) (j*L)) Prf.hyp0 ?_
  have nonzero := factors_at _ _ _ _ _ _ (stage_nonzero_factors M m L w j Prf.hyp0) hi.wk
  exact .botE _ (succ_ne_zero (nonzero.eqSymm.eqTrans hz.wk))
theorem stage_all_zero_factor (M m L w j i : PTm n) (hi : Γ ⊢[PRAAx] lt i j)
    (hz : Γ ⊢[PRAAx] flag (factor M m w i) L ≐ zero) : Γ ⊢[PRAAx] allZero (stage M m L w j) (j*L) :=
  all_zero_of_flag_zero _ _ (stage_zero_factor M m L w j i hi hz)


def stageCertificate (M m L w j : PTm n) : Fm PTm n := (flag (stage M m L w j) (j*L) ≐ one) ⋏
  ((first (stage M m L w j) (j*L) ≐ firstSum M m L w j) ⋏
    ((degree (stage M m L w j) (j*L) ≐ degreeSum M m L w j) ⋏
      (leading (stage M m L w j) (j*L) ≐ leadingProduct M m L w j)))
@[simp] theorem subst_stageCertificate {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    (stageCertificate M m L w j).subst σ = stageCertificate (Syn.subst σ M) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by simp [stageCertificate]

theorem stage_certificate_zero (M m L w : PTm n) : Γ ⊢[PRAAx] stageCertificate M m L w zero :=
  .andI (stage_zero_success _ _ _ _) (.andI
    ((first_congr (stage_zero _ _ _ _) (zero_mul _)).eqTrans (singleton_first.eqTrans (first_sum_zero _ _ _ _).eqSymm)) (.andI
      ((degree_congr (stage_zero _ _ _ _) (zero_mul _)).eqTrans (singleton_degree.eqTrans (degree_sum_zero _ _ _ _).eqSymm))
      ((leading_congr (stage_zero _ _ _ _) (zero_mul _)).eqTrans (singleton_leading.eqTrans (leading_product_zero _ _ _ _).eqSymm))))
theorem stage_certificate_step (M m L w j : PTm n) (h : Γ ⊢[PRAAx] stageCertificate M m L w j)
    (hFactor : Γ ⊢[PRAAx] flag (factor M m w j) L ≐ one) : Γ ⊢[PRAAx] stageCertificate M m L w (succ j) := by
  have oldNonzero := nonzero_of_flag_one (stage M m L w j) (j*L) (Prf.andE₁ h)
  have nextNonzero := nonzero_of_flag_one (factor M m w j) L hFactor
  refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
  · exact (flag_congr (stage_succ _ _ _ _ _) (successor_width _ _)).eqTrans
      (product_success _ _ _ _ oldNonzero nextNonzero)
  · exact (first_congr (stage_succ _ _ _ _ _) (successor_width _ _)).eqTrans
      ((product_first _ _ _ _ oldNonzero nextNonzero).eqTrans
        ((congrAdd (.andE₁ (.andE₂ h)) (.eqRefl _)).eqTrans (first_sum_succ _ _ _ _ _).eqSymm))
  · exact (degree_congr (stage_succ _ _ _ _ _) (successor_width _ _)).eqTrans
      ((product_degree _ _ _ _ oldNonzero nextNonzero).eqTrans
        ((congrAdd (.andE₁ (.andE₂ (.andE₂ h))) (.eqRefl _)).eqTrans (degree_sum_succ _ _ _ _ _).eqSymm))
  · exact (leading_congr (stage_succ _ _ _ _ _) (successor_width _ _)).eqTrans
      ((product_leading _ _ _ _ oldNonzero nextNonzero).eqTrans
        ((qmul_congr (.andE₂ (.andE₂ (.andE₂ h))) (.eqRefl _)).eqTrans (leading_product_succ _ _ _ _ _).eqSymm))

def prefixLaw (M m L w N j : PTm n) : Fm PTm n := le j N ⟶ stageCertificate M m L w j
@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (M m L w N j : PTm n) :
    (prefixLaw M m L w N j).subst σ = prefixLaw (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ N) (Syn.subst σ j) := by simp [prefixLaw]

/-- Local factor flags are the original bounded contract. Only an actual
guarded conjunction of scalar equalities is the QF induction formula. -/
theorem stage_certificate (M m L w N : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w N) :
    Γ ⊢[PRAAx] stageCertificate M m L w N := by
  have source : Γ.map Fm.shift ⊢[PRAAx] factorFlags (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift N) := by
    simpa only [Fm.shift,subst_factorFlags,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,by trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (stage_certificate_zero _ _ _ _).wk
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift N) ::
        prefixLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift N) (var 0) :: Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
      have previous : Δ ⊢[PRAAx] prefixLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift N) (var 0) := Prf.hyp1
      exact stage_certificate_step _ _ _ _ _ (.impE previous (le_of_lt bound))
        (factors_at _ _ _ _ _ _ source.wk.wk bound)
  have reached : Γ ⊢[PRAAx] prefixLaw M m L w N N := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE reached (le_refl N)

theorem stage_first (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) : Γ ⊢[PRAAx]
    first (stage M m L w j) (j*L) ≐ firstSum M m L w j := .andE₁ (.andE₂ (stage_certificate M m L w j h))
theorem stage_degree (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) : Γ ⊢[PRAAx]
    degree (stage M m L w j) (j*L) ≐ degreeSum M m L w j := .andE₁ (.andE₂ (.andE₂ (stage_certificate M m L w j h)))
theorem stage_leading (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) : Γ ⊢[PRAAx]
    leading (stage M m L w j) (j*L) ≐ leadingProduct M m L w j := .andE₂ (.andE₂ (.andE₂ (stage_certificate M m L w j h)))


/-! Actual coefficient scaling preserves the genuine first coefficient
when the scalar is nonzero; the all-zero branch is kept separately. -/
theorem scaled_entry_recode (C s N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    recode (entry (GaussianRationalCoefficientScaling.scaled C s) i) ≐ qmul s (recode (entry C i)) :=
  (recode_congr (GaussianRationalCoefficientScaling.scaled_lookup C s i
    (lt_congr (.eqRefl _) hC.eqSymm ((succ_monus_succ _ _).eqTrans hi)))).eqTrans
    ((recode_eq _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
      (GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqSymm)

theorem scaled_zero_prefix (C s N e : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (he : Γ ⊢[PRAAx] le e N) (hZero : Γ ⊢[PRAAx] zeroPrefix C e) : Γ ⊢[PRAAx]
    zeroPrefix (GaussianRationalCoefficientScaling.scaled C s) e := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift C) (Syn.shift e) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hZero.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift e) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_of_lt Prf.hyp0) es.wk
  simpa only [Syn.shift,GaussianRationalCoefficientScaling.subst_scaled] using
    (scaled_entry_recode (Syn.shift C) (Syn.shift s) (Syn.shift N) (var 0) cs.wk bound).eqTrans
      ((qmul_congr (.eqRefl _) (zero_prefix_at _ _ _ zs.wk Prf.hyp0)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_right _))

theorem scaled_all_zero (C s N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hZero : Γ ⊢[PRAAx] allZero C N) : Γ ⊢[PRAAx] allZero (GaussianRationalCoefficientScaling.scaled C s) N := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] allZero (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalPolynomialDegree.subst_allZero,Syn.shift] using hZero.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ,GaussianRationalCoefficientScaling.subst_scaled] using
    (scaled_entry_recode (Syn.shift C) (Syn.shift s) (Syn.shift N) (var 0) cs.wk bound).eqTrans
      ((qmul_congr (.eqRefl _) (zero_prefix_at _ _ _ zs.wk Prf.hyp0)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_right _))

theorem scaled_failure (C s N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hZero : Γ ⊢[PRAAx] flag C N ≐ zero) : Γ ⊢[PRAAx]
    flag (GaussianRationalCoefficientScaling.scaled C s) N ≐ zero :=
  flag_zero_of_all_zero _ _ (scaled_all_zero C s N hC (all_zero_of_flag_zero C N hZero))
theorem scaled_success_reflect (C s N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] flag (GaussianRationalCoefficientScaling.scaled C s) N ≐ one) : Γ ⊢[PRAAx] flag C N ≐ one := by
  refine .orE (flag_cases C N) ?_ Prf.hyp0
  exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans (scaled_failure C s N hC.wk Prf.hyp0)))

theorem scaled_first (C s N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hs : Γ ⊢[PRAAx] canonical s) (hsn : Γ ⊢[PRAAx] neg (s ≐ qzero))
    (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    first (GaussianRationalCoefficientScaling.scaled C s) N ≐ first C N := by
  have bound := success_index C N (flag_one_of_nonzero C N h)
  have value := scaled_entry_recode C s N (first C N) hC bound
  have nonzero := GaussianRationalPolynomialProductDegree.multiply_nonzero s (leading C N) hs (leading_canonical C N) hsn (leading_nonzero C N h)
  exact first_exact _ _ _ bound (scaled_zero_prefix C s N (first C N) hC bound (first_zero_prefix C N))
    (.impI (.impE nonzero.wk (value.wk.eqSymm.eqTrans Prf.hyp0)))
theorem scaled_success (C s N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hs : Γ ⊢[PRAAx] canonical s) (hsn : Γ ⊢[PRAAx] neg (s ≐ qzero))
    (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    flag (GaussianRationalCoefficientScaling.scaled C s) N ≐ one :=
  flag_one_of_found _ _ (lt_congr (scaled_first C s N hC hs hsn h).eqSymm (.eqRefl _)
    (GaussianRationalPolynomialDegree.found_of_flag_one C N (flag_one_of_nonzero C N h)))
theorem scaled_degree (C s N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hs : Γ ⊢[PRAAx] canonical s) (hsn : Γ ⊢[PRAAx] neg (s ≐ qzero))
    (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    degree (GaussianRationalCoefficientScaling.scaled C s) N ≐ degree C N := congrMonus (.eqRefl _) (scaled_first C s N hC hs hsn h)
theorem scaled_leading (C s N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hs : Γ ⊢[PRAAx] canonical s) (hsn : Γ ⊢[PRAAx] neg (s ≐ qzero))
    (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    leading (GaussianRationalCoefficientScaling.scaled C s) N ≐ qmul s (leading C N) :=
  (recode_congr (entry_congr (.eqRefl _) (scaled_first C s N hC hs hsn h))).eqTrans
    (scaled_entry_recode C s N (first C N) hC (success_index C N (flag_one_of_nonzero C N h)))

theorem sign_nonzero (m w : PTm n) : Γ ⊢[PRAAx] neg (signPoint m w ≐ qzero) := by
  refine .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero ?_)
  exact (GaussianScalarColumnSelection.sign_square (Γ := Γ) m w).wk.eqSymm.eqTrans
    ((qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))
theorem signed_term_flag_iff (M m L w : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (flag (term M m L w) (m*L) ≐ one) (factorFlags M m L w m) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact stage_nonzero_factors M m L w m (scaled_success_reflect _ _ _ (stage_length _ _ _ _ _) Prf.hyp0)
  · exact scaled_success _ _ _ (stage_length _ _ _ _ _) (sign_canonical m w) (sign_nonzero m w)
      (nonzero_of_flag_one _ _ (stage_success_of_factors M m L w m Prf.hyp0))
theorem signed_term_zero_factor (M m L w i : PTm n) (hi : Γ ⊢[PRAAx] lt i m)
    (hz : Γ ⊢[PRAAx] flag (factor M m w i) L ≐ zero) : Γ ⊢[PRAAx] flag (term M m L w) (m*L) ≐ zero :=
  scaled_failure _ _ _ (stage_length _ _ _ _ _) (stage_zero_factor M m L w m i hi hz)
theorem signed_term_first (M m L w : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w m) : Γ ⊢[PRAAx]
    first (term M m L w) (m*L) ≐ firstSum M m L w m :=
  (scaled_first _ _ _ (stage_length _ _ _ _ _) (sign_canonical m w) (sign_nonzero m w)
    (nonzero_of_flag_one _ _ (stage_success_of_factors M m L w m h))).eqTrans (stage_first M m L w m h)
theorem signed_term_degree (M m L w : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w m) : Γ ⊢[PRAAx]
    degree (term M m L w) (m*L) ≐ degreeSum M m L w m :=
  (scaled_degree _ _ _ (stage_length _ _ _ _ _) (sign_canonical m w) (sign_nonzero m w)
    (nonzero_of_flag_one _ _ (stage_success_of_factors M m L w m h))).eqTrans (stage_degree M m L w m h)
theorem signed_term_leading (M m L w : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w m) : Γ ⊢[PRAAx]
    leading (term M m L w) (m*L) ≐ qmul (signPoint m w) (leadingProduct M m L w m) :=
  (scaled_leading _ _ _ (stage_length _ _ _ _ _) (sign_canonical m w) (sign_nonzero m w)
    (nonzero_of_flag_one _ _ (stage_success_of_factors M m L w m h))).eqTrans
      (qmul_congr (.eqRefl _) (stage_leading M m L w m h))


/-! The actual output stores the original stage and signed term together
with the derived-observable programs; there is no replacement product. -/
def output (M m L w j : PTm n) : PTm n := pairT (stage M m L w j)
  (pairT (term M m L w) (pairT (firstSum M m L w j)
    (pairT (degreeSum M m L w j) (pairT (leadingProduct M m L w j) (signPoint m w)))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (M m L w j : PTm n) : PTm n := app outputF ![M,m,L,w,j]
def fields (p : PTm n) (i : Fin 6) : PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),
  fstT (sndT (sndT (sndT p))),fstT (sndT (sndT (sndT (sndT p)))),sndT (sndT (sndT (sndT (sndT p))))] i
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (output M m L w j) = output (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (run M m L w j) = run (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 6) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (M m L w j : PTm n) : Γ ⊢[PRAAx] run M m L w j ≐ output M m L w j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![M,m,L,w,j]
theorem returned_fields (M m L w j : PTm n) (i : Fin 6) : Γ ⊢[PRAAx]
    fields (run M m L w j) i ≐ ![stage M m L w j,term M m L w,firstSum M m L w j,
      degreeSum M m L w j,leadingProduct M m L w j,signPoint m w] i := by
  have e0 := program_at (Γ := Γ) M m L w j
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  have e3 := (congrSnd e2).eqTrans (snd_pair _ _)
  have e4 := (congrSnd e3).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrFst e4).eqTrans (fst_pair _ _)
  · exact (congrSnd e4).eqTrans (snd_pair _ _)
theorem returned_stage_success (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) : Γ ⊢[PRAAx]
    flag (fields (run M m L w j) 0) (j*L) ≐ one :=
  (flag_congr (returned_fields _ _ _ _ _ 0) (.eqRefl _)).eqTrans (stage_success_of_factors M m L w j h)
theorem returned_stage_first (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) : Γ ⊢[PRAAx]
    first (fields (run M m L w j) 0) (j*L) ≐ fields (run M m L w j) 2 :=
  (first_congr (returned_fields _ _ _ _ _ 0) (.eqRefl _)).eqTrans
    ((stage_first M m L w j h).eqTrans (returned_fields _ _ _ _ _ 2).eqSymm)
theorem returned_stage_degree (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) : Γ ⊢[PRAAx]
    degree (fields (run M m L w j) 0) (j*L) ≐ fields (run M m L w j) 3 :=
  (degree_congr (returned_fields _ _ _ _ _ 0) (.eqRefl _)).eqTrans
    ((stage_degree M m L w j h).eqTrans (returned_fields _ _ _ _ _ 3).eqSymm)
theorem returned_stage_leading (M m L w j : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w j) : Γ ⊢[PRAAx]
    leading (fields (run M m L w j) 0) (j*L) ≐ fields (run M m L w j) 4 :=
  (leading_congr (returned_fields _ _ _ _ _ 0) (.eqRefl _)).eqTrans
    ((stage_leading M m L w j h).eqTrans (returned_fields _ _ _ _ _ 4).eqSymm)
theorem returned_term_leading (M m L w : PTm n) (h : Γ ⊢[PRAAx] factorFlags M m L w m) : Γ ⊢[PRAAx]
    leading (fields (run M m L w m) 1) (m*L) ≐
      qmul (fields (run M m L w m) 5) (fields (run M m L w m) 4) :=
  (leading_congr (returned_fields _ _ _ _ _ 1) (.eqRefl _)).eqTrans
    ((signed_term_leading M m L w h).eqTrans
      (qmul_congr (returned_fields _ _ _ _ _ 5) (returned_fields _ _ _ _ _ 4)).eqSymm)

theorem actual_stage_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (flag (stage (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4*var 2) ≐ one)
      (factorFlags (var 0) (var 1) (var 2) (var 3) (var 4))) := closeUniv 5 (stage_success_iff _ _ _ _ _)
theorem actual_zero_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 4) ⟶ flag (factor (var 0) (var 1) (var 3) (var 5)) (var 2) ≐ zero ⟶
      allZero (stage (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4*var 2)) :=
  closeUniv 6 (.impI (.impI (stage_all_zero_factor _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_stage_degree_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (factorFlags (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ stageCertificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (stage_certificate _ _ _ _ _ Prf.hyp0))
theorem actual_signed_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (flag (term (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) ≐ one)
      (factorFlags (var 0) (var 1) (var 2) (var 3) (var 1))) := closeUniv 4 (signed_term_flag_iff _ _ _ _)
theorem actual_signed_zero_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 1) ⟶ flag (factor (var 0) (var 1) (var 3) (var 4)) (var 2) ≐ zero ⟶
      flag (term (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) ≐ zero) :=
  closeUniv 5 (.impI (.impI (signed_term_zero_factor _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_signed_degree_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (factorFlags (var 0) (var 1) (var 2) (var 3) (var 1) ⟶
      ((first (term (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) ≐ firstSum (var 0) (var 1) (var 2) (var 3) (var 1)) ⋏
        ((degree (term (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) ≐ degreeSum (var 0) (var 1) (var 2) (var 3) (var 1)) ⋏
          (leading (term (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) ≐
            qmul (signPoint (var 1) (var 3)) (leadingProduct (var 0) (var 1) (var 2) (var 3) (var 1)))))) :=
  closeUniv 4 (.impI (.andI (signed_term_first _ _ _ _ Prf.hyp0)
    (.andI (signed_term_degree _ _ _ _ Prf.hyp0) (signed_term_leading _ _ _ _ Prf.hyp0))))
theorem actual_stage_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_stage_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (factorFlags (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      degree (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 0) (var 4*var 2) ≐
        fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 3) :=
  closeUniv 5 (.impI (returned_stage_degree _ _ _ _ _ Prf.hyp0))
theorem actual_returned_stage_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (factorFlags (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      leading (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 0) (var 4*var 2) ≐
        fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 4) :=
  closeUniv 5 (.impI (returned_stage_leading _ _ _ _ _ Prf.hyp0))
theorem actual_returned_signed_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (factorFlags (var 0) (var 1) (var 2) (var 3) (var 1) ⟶
      leading (fields (run (var 0) (var 1) (var 2) (var 3) (var 1)) 1) (var 1*var 2) ≐
        qmul (fields (run (var 0) (var 1) (var 2) (var 3) (var 1)) 5) (fields (run (var 0) (var 1) (var 2) (var 3) (var 1)) 4)) :=
  closeUniv 4 (.impI (returned_term_leading _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTermDegree
