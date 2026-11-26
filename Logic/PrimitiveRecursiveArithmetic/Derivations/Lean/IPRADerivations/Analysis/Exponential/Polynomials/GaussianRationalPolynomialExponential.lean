import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialPowers

/-!
# Literal finite factorial exponentials of a stored polynomial

Gamma (C4) requires the actual finite expression
`sum_{k<=J} H(X)^k/k!`, rather than an unlinked formal coefficient rule.
The actual powers are the previously proved fixed-cap product prefixes.
Each new factorial-weighted term is added by the existing normalized
coefficient-buffer operations. All cap, degree and query parameters are
numerical; the evaluator theorem assumes only the original input length.

The coefficient recurrence and literal finite complex evaluation below
are derived from the real constructors. Bell-coefficient reconstruction,
norm estimates and the completed C4 name equality are later obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponential

open_ipra
open GaussianRationalHorner (qzero qadd qmul canonical evaluate ofGaussian represents)
open GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr qmul_congr qzero_add canonicalCoefficients)
open GaussianRationalPolynomialPowers (powerPrefix prefix_length prefix_evaluation)
open GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation added added_length added_evaluation)
open GaussianRationalCoefficientScaling (scaled scaled_length evaluation_linearity)
open GaussianRationalMonicReduction (singleton singleton_length singleton_evaluation evaluate_congr canonical_coefficients_congr)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseFactorial (j : PTm n) : PTm n := ofGaussian ComplexLogarithmRemainder.oneCode (fact j)
ipra_subst inverseFactorial [fact]

theorem factorial_positive (j : PTm n) : Γ ⊢[PRAAx] le one (fact j) :=
  le_congr (.eqRefl _) (AnalyticNumberTheory.Primes.fact_pos j).eqSymm (zero_lt_succ _)
theorem inverse_factorial_represents (j : PTm n) : Γ ⊢[PRAAx]
    represents (inverseFactorial j) ComplexLogarithmRemainder.oneCode (fact j) :=
  GaussianRationalHorner.ofGaussian_represents _ _ (factorial_positive j)
theorem inverse_factorial_canonical (j : PTm n) : Γ ⊢[PRAAx] canonical (inverseFactorial j) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (factorial_positive j)
theorem inverse_factorial_zero : Γ ⊢[PRAAx] inverseFactorial (zero : PTm n) ≐ qone := by
  simpa only [inverseFactorial,GaussianRationalHorner.subst_ofGaussian,
    ComplexLogarithmRemainder.subst_oneCode,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,GaussianRationalSyntheticDivision.qone] using
    (Prf.eqCongr (Γ := Γ) (ofGaussian (var 0) (var 1) : PTm 2)
      (σ := ![ComplexLogarithmRemainder.oneCode,fact zero])
      (σ' := ![ComplexLogarithmRemainder.oneCode,one])
      (fun i => by fin_cases i; exact .eqRefl _; exact fact_zero zero))

def scalarBody : PTm 2 := qmul (inverseFactorial (var 0)) (GaussianRationalReciprocal.power (var 1) (var 0))
def scalarSum (q j : PTm n) : PTm n := GaussianRationalFiniteSum.sum scalarBody (succ j) q
ipra_subst scalarSum
theorem scalar_body_at (q j : PTm n) : inst2 scalarBody j q =
    qmul (inverseFactorial j) (GaussianRationalReciprocal.power q j) := by simp [scalarBody,inst2]
theorem scalar_sum_zero (q : PTm n) : Γ ⊢[PRAAx] scalarSum q zero ≐ qone := by
  have hs : Γ ⊢[PRAAx] scalarSum q zero ≐
      qadd (GaussianRationalFiniteSum.sum scalarBody zero q) (inst2 scalarBody zero q) :=
    GaussianRationalFiniteSum.sum_succ scalarBody zero q
  have ht : Γ ⊢[PRAAx] inst2 scalarBody zero q ≐ qone := by
    rw [scalar_body_at]
    exact (qmul_congr (inverse_factorial_zero (Γ := Γ)) (GaussianRationalReciprocal.power_zero q)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical qone qone_canonical)
  exact hs.eqTrans ((qadd_congr (GaussianRationalFiniteSum.sum_zero scalarBody q) ht).eqTrans
    (qzero_add qone qone_canonical))

theorem scalar_sum_succ (q j : PTm n) : Γ ⊢[PRAAx] scalarSum q (succ j) ≐
    qadd (scalarSum q j) (qmul (inverseFactorial (succ j)) (GaussianRationalReciprocal.power q (succ j))) := by
  simpa only [scalarSum,scalar_body_at] using GaussianRationalFiniteSum.sum_succ (Γ := Γ) scalarBody (succ j) q

def advance (C N K j Q : PTm n) : PTm n :=
  added (leftPad Q N) (scaled (powerPrefix C N K (succ j)) (inverseFactorial (succ j))) (succ (succ j*N))
def data (C N K : PTm n) : PTm n := pairT C (pairT N K)
def stepBody : PTm 3 := advance (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0) (var 1)
def stageF : PR 2 := rec2 (singleton qone : PTm 1) stepBody
def stage (C N K j : PTm n) : PTm n := ap2 stageF j (data C N K)
def polynomial (C N K : PTm n) : PTm n := stage C N K K
ipra_subst advance
ipra_subst data
ipra_subst stage
ipra_subst polynomial

theorem advance_congr {C C' N N' K K' j j' Q Q' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hN : Γ ⊢[PRAAx] N ≐ N') (hK : Γ ⊢[PRAAx] K ≐ K')
    (hj : Γ ⊢[PRAAx] j ≐ j') (hQ : Γ ⊢[PRAAx] Q ≐ Q') : Γ ⊢[PRAAx]
    advance C N K j Q ≐ advance C' N' K' j' Q' := by
  simpa only [subst_advance,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqCongr (Γ := Γ) (advance (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![C,N,K,j,Q]) (σ' := ![C',N',K',j',Q'])
      (fun i => by fin_cases i; exact hC; exact hN; exact hK; exact hj; exact hQ))
theorem stage_congr {C C' N N' K K' j j' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hN : Γ ⊢[PRAAx] N ≐ N') (hK : Γ ⊢[PRAAx] K ≐ K')
    (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] stage C N K j ≐ stage C' N' K' j' := by
  simpa only [subst_stage,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqCongr (Γ := Γ) (stage (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![C,N,K,j]) (σ' := ![C',N',K',j'])
      (fun i => by fin_cases i; exact hC; exact hN; exact hK; exact hj))
theorem stage_zero (C N K : PTm n) : Γ ⊢[PRAAx] stage C N K zero ≐ singleton qone := by
  simpa only [stage,stageF,GaussianRationalMonicReduction.subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (singleton qone : PTm 1) stepBody (data C N K)
theorem stage_succ (C N K j : PTm n) : Γ ⊢[PRAAx] stage C N K (succ j) ≐ advance C N K j (stage C N K j) := by
  have e := rec2_succ (Γ := Γ) (singleton qone : PTm 1) stepBody j (data C N K)
  simp only [stepBody,subst_advance,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at e
  have rest := snd_pair (Γ := Γ) C (pairT N K)
  exact e.eqTrans (advance_congr (fst_pair _ _) rest.fstE
    rest.sndE (.eqRefl _) (.eqRefl _))

theorem advance_length (C N K j Q : PTm n) : Γ ⊢[PRAAx] length (advance C N K j Q) ≐ succ (succ j*N) :=
  added_length _ _ _
theorem stage_length (C N K j : PTm n) : Γ ⊢[PRAAx] length (stage C N K j) ≐ succ (j*N) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact (congrFst ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_zero _ _ _))).eqTrans
      ((singleton_length _).eqTrans (congrSucc ((congrMul Prf.hyp0 (.eqRefl N)).eqTrans (zero_mul _))).eqSymm)
  · exact (congrFst ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_succ _ _ _ _))).eqTrans
      ((advance_length _ _ _ _ _).eqTrans (congrSucc (congrMul Prf.hyp0.eqSymm (.eqRefl N))))
theorem stage_canonical (C N K j : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (stage C N K j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact canonical_coefficients_congr
      ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_zero _ _ _))
      GaussianPolynomialDeterminantTerms.singleton_one_canonical
  · exact canonical_coefficients_congr
      ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_succ _ _ _ _))
      (GaussianRationalMonicReduction.added_canonical _ _ _)

theorem stage_step_evaluation (C N K j z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j K) (ih : Γ ⊢[PRAAx] evaluate (stage C N K j) z ≐ scalarSum (evaluate C z) j) : Γ ⊢[PRAAx]
    evaluate (stage C N K (succ j)) z ≐ scalarSum (evaluate C z) (succ j) := by
  have hPad : Γ ⊢[PRAAx] length (leftPad (stage C N K j) N) ≐ succ (succ j*N) :=
    (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (stage_length _ _ _ _)).eqTrans (by ipra_ring))
  have hTerm : Γ ⊢[PRAAx] length (scaled (powerPrefix C N K (succ j)) (inverseFactorial (succ j))) ≐ succ (succ j*N) :=
    (scaled_length _ _).eqTrans (prefix_length _ _ _ _)
  exact (evaluate_congr (stage_succ C N K j) (.eqRefl _)).eqTrans
    ((added_evaluation _ _ _ _ hPad hTerm).eqTrans
      ((qadd_congr ((pad_evaluation _ _ _).eqTrans ih)
        ((evaluation_linearity _ _ _).eqTrans (qmul_congr (.eqRefl _)
          (prefix_evaluation C N K (succ j) z hC hj)))).eqTrans (scalar_sum_succ _ _).eqSymm))

def evaluationLaw (C N K z j : PTm n) : Fm PTm n := le j K ⟶
  evaluate (stage C N K j) z ≐ scalarSum (evaluate C z) j
ipra_subst evaluationLaw

theorem stage_evaluation (C N K j z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx] evaluate (stage C N K j) z ≐ scalarSum (evaluate C z) j := by
  have hcs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,
      ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift z) (var 0)) := by
    ipra_qfind (by trivial) [subst_evaluationLaw]
    · exact .impI ((evaluate_congr (stage_zero C N K) (.eqRefl _)).eqTrans
        ((singleton_evaluation _ _).eqTrans ((GaussianTranslatedNonconstant.recode_eq _ qone_canonical).eqTrans
          (scalar_sum_zero _).eqSymm)))
    · refine .impI ?_
      exact stage_step_evaluation _ _ _ _ _ hcs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have gate : Γ ⊢[PRAAx] evaluationLaw C N K z j := by
    simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE gate hj

theorem polynomial_length (C N K : PTm n) : Γ ⊢[PRAAx] length (polynomial C N K) ≐ succ (K*N) := stage_length _ _ _ _
theorem polynomial_canonical (C N K : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (polynomial C N K) := stage_canonical _ _ _ _
theorem polynomial_evaluation (C N K z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (polynomial C N K) z ≐ scalarSum (evaluate C z) K := stage_evaluation _ _ _ _ _ hC (le_refl _)

/-- The literal stored coefficient recurrence, with its actual factorial
coefficient and the SAME previously constructed power buffer. -/
theorem stage_coefficient_succ (C N K j s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ j*N)) : Γ ⊢[PRAAx]
    entry (stage C N K (succ j)) s ≐ qadd
      (GaussianRationalPolynomialBuffers.padCoefficient (stage C N K j) N s)
      (qmul (inverseFactorial (succ j)) (entry (powerPrefix C N K (succ j)) s)) := by
  have hi : Γ ⊢[PRAAx] lt s (succ (succ j*N)) := (succ_monus_succ _ _).eqTrans hs
  have hPad : Γ ⊢[PRAAx] N+length (stage C N K j) ≐ succ (succ j*N) :=
    (congrAdd (.eqRefl _) (stage_length _ _ _ _)).eqTrans (by ipra_ring)
  have hPower : Γ ⊢[PRAAx] lt s (length (powerPrefix C N K (succ j))) :=
    lt_congr (.eqRefl _) (prefix_length _ _ _ _).eqSymm hi
  exact (entry_congr (stage_succ C N K j) (.eqRefl _)).eqTrans
    ((GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ hi).eqTrans
      (qadd_congr (GaussianRationalPolynomialBuffers.pad_lookup _ _ _ (lt_congr (.eqRefl _) hPad.eqSymm hi))
        (GaussianRationalCoefficientScaling.scaled_lookup _ _ _ hPower)))

def polynomialF : PR 3 := PTm.toPR (polynomial (var 0) (var 1) (var 2))
def scalarF : PR 2 := PTm.toPR (scalarSum (var 0) (var 1))
def run (C N K : PTm n) : PTm n := PTm.app polynomialF ![C,N,K]
ipra_subst run

theorem program_at (C N K : PTm n) : Γ ⊢[PRAAx] run C N K ≐ polynomial C N K := by
  simpa [run,polynomialF] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) (var 2) : PTm 3) ![C,N,K]
theorem scalar_program_at (q K : PTm n) : Γ ⊢[PRAAx] ap2 scalarF q K ≐ scalarSum q K := by
  simpa [scalarF,ap2] using toPR_eq (Γ := Γ) (scalarSum (var 0) (var 1) : PTm 2) ![q,K]
theorem returned_length (C N K : PTm n) : Γ ⊢[PRAAx] length (run C N K) ≐ succ (K*N) :=
  (congrFst (program_at C N K)).eqTrans (polynomial_length _ _ _)
theorem returned_canonical (C N K : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (run C N K) :=
  canonical_coefficients_congr (program_at C N K) (polynomial_canonical _ _ _)
theorem returned_evaluation (C N K z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (run C N K) z ≐ ap2 scalarF (evaluate C z) K :=
  (evaluate_congr (program_at C N K) (.eqRefl _)).eqTrans
    ((polynomial_evaluation C N K z hC).eqTrans (scalar_program_at _ _).eqSymm)

theorem literal_inverse_factorial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (fact (var 0)) ⋏ (canonical (inverseFactorial (var 0)) ⋏
      represents (inverseFactorial (var 0)) ComplexLogarithmRemainder.oneCode (fact (var 0)))) :=
  closeUniv 1 (.andI (factorial_positive _) (.andI (inverse_factorial_canonical _) (inverse_factorial_represents _)))
theorem actual_exponential_polynomial_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (polynomial (var 0) (var 1) (var 2)) ≐ succ (var 2*var 1) ⋏
      canonicalCoefficients (polynomial (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (polynomial_length _ _ _) (polynomial_canonical _ _ _))
theorem actual_exponential_prefix_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (stage (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 3*var 1) ⋏
      canonicalCoefficients (stage (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (stage_length _ _ _ _) (stage_canonical _ _ _ _))
theorem actual_exponential_coefficient_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (succ (var 3)*var 1) ⟶ entry (stage (var 0) (var 1) (var 2) (succ (var 3))) (var 4) ≐
      qadd (GaussianRationalPolynomialBuffers.padCoefficient (stage (var 0) (var 1) (var 2) (var 3)) (var 1) (var 4))
        (qmul (inverseFactorial (succ (var 3)))
          (entry (powerPrefix (var 0) (var 1) (var 2) (succ (var 3))) (var 4)))) :=
  closeUniv 5 (.impI (stage_coefficient_succ _ _ _ _ _ Prf.hyp0))
theorem literal_finite_exponential_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 2) ⟶
      evaluate (stage (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        scalarSum (evaluate (var 0) (var 4)) (var 3)) :=
  closeUniv 5 (.impI (.impI (stage_evaluation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem literal_finite_exponential_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (polynomial (var 0) (var 1) (var 2)) (var 3) ≐
      scalarSum (evaluate (var 0) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (polynomial_evaluation _ _ _ _ Prf.hyp0))
theorem actual_exponential_polynomial_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ polynomial (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_finite_exponential_scalar_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 scalarF (var 0) (var 1) ≐ scalarSum (var 0) (var 1)) := closeUniv 2 (scalar_program_at _ _)
theorem actual_returned_exponential_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (run (var 0) (var 1) (var 2)) ≐ succ (var 2*var 1) ⋏
      canonicalCoefficients (run (var 0) (var 1) (var 2))) := closeUniv 3 (.andI (returned_length _ _ _) (returned_canonical _ _ _))
theorem actual_returned_finite_exponential_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (run (var 0) (var 1) (var 2)) (var 3) ≐
      ap2 scalarF (evaluate (var 0) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (returned_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponential
