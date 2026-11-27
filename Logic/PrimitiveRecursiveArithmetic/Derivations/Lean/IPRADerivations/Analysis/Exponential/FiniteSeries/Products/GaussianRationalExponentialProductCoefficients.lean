import IPRADerivations.Analysis.Polynomials.Products.Powers.GaussianRationalPolynomialPowerEuler
import IPRADerivations.Analysis.Exponential.Polynomials.Coefficients.GaussianRationalPolynomialExponentialCoefficients
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalFactorialEulerSums

/-!
# Stored product coefficients of the actual finite exponential

The original Product(E(C),stage_j) buffer satisfies a real padded/scaled
addition recurrence. Every-query distributivity and actual finite-grid
coefficient reflection derive this recurrence from the SAME stored
programs. A coefficient induction can therefore link the original finite
product to its actual factorial-weighted summands.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalExponentialProductCoefficients

open_ipra
open GaussianRationalHorner (qzero qadd qmul evaluate)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr canonicalCoefficients)
open GaussianRationalPolynomialProduct (product product_length product_canonical product_evaluation)
open GaussianRationalPolynomialExponential (stage stage_length stage_canonical inverseFactorial)
open GaussianRationalPolynomialPowers (powerPrefix prefix_length)
open GaussianRationalCoefficientScaling (scaled scaled_length evaluation_linearity)
open GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation added added_length added_evaluation)
open GaussianRationalEulerCoefficients (euler euler_length)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialExponentialStability (exponent_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productPrefix (C N K j : PTm n) : PTm n := product (euler C N) (stage C N K j) N (j*N)
def productCoefficient (C N K j e : PTm n) : PTm n := exponentCoefficient (productPrefix C N K j) (N+j*N) e
def productStep (C N K j : PTm n) : PTm n := added
  (leftPad (productPrefix C N K j) N)
  (scaled (product (euler C N) (powerPrefix C N K (succ j)) N (succ j*N)) (inverseFactorial (succ j)))
  (succ (N+succ j*N))
ipra_subst productPrefix
ipra_subst productCoefficient
ipra_subst productStep

theorem product_prefix_length (C N K j : PTm n) : Γ ⊢[PRAAx]
    length (productPrefix C N K j) ≐ succ (N+j*N) := product_length _ _ _ _
theorem padded_length (C N K j : PTm n) : Γ ⊢[PRAAx]
    length (leftPad (productPrefix C N K j) N) ≐ succ (N+succ j*N) :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (product_prefix_length _ _ _ _)).eqTrans (by ipra_ring))
theorem scaled_length_at (C N K j : PTm n) : Γ ⊢[PRAAx]
    length (scaled (product (euler C N) (powerPrefix C N K (succ j)) N (succ j*N)) (inverseFactorial (succ j))) ≐
      succ (N+succ j*N) := (scaled_length _ _).eqTrans (product_length _ _ _ _)
theorem step_length (C N K j : PTm n) : Γ ⊢[PRAAx]
    length (productStep C N K j) ≐ succ (N+succ j*N) := added_length _ _ _

theorem stage_successor_value (C N K j z : PTm n) : Γ ⊢[PRAAx]
    evaluate (stage C N K (succ j)) z ≐ qadd (evaluate (stage C N K j) z)
      (qmul (inverseFactorial (succ j)) (evaluate (powerPrefix C N K (succ j)) z)) := by
  have hPad : Γ ⊢[PRAAx] length (leftPad (stage C N K j) N) ≐ succ (succ j*N) :=
    (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (stage_length _ _ _ _)).eqTrans (by ipra_ring))
  have hTerm : Γ ⊢[PRAAx] length (scaled (powerPrefix C N K (succ j)) (inverseFactorial (succ j))) ≐ succ (succ j*N) :=
    (scaled_length _ _).eqTrans (prefix_length _ _ _ _)
  exact (GaussianRationalMonicReduction.evaluate_congr (GaussianRationalPolynomialExponential.stage_succ C N K j) (.eqRefl _)).eqTrans
    ((added_evaluation _ _ _ _ hPad hTerm).eqTrans
      (qadd_congr (pad_evaluation _ _ _) (evaluation_linearity _ _ _)))

theorem scalar_shuffle (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  GaussianRationalPowerAlgebra.commute_nested a b c

theorem product_successor_value (C N K j z : PTm n) : Γ ⊢[PRAAx]
    evaluate (productPrefix C N K (succ j)) z ≐ evaluate (productStep C N K j) z := by
  have hLeft : Γ ⊢[PRAAx] evaluate (productPrefix C N K (succ j)) z ≐
      qadd (qmul (evaluate (euler C N) z) (evaluate (stage C N K j) z))
        (qmul (inverseFactorial (succ j)) (qmul (evaluate (euler C N) z) (evaluate (powerPrefix C N K (succ j)) z))) :=
    (product_evaluation _ _ _ _ z (euler_length C N) (stage_length C N K (succ j))).eqTrans
      ((qmul_congr (.eqRefl _) (stage_successor_value C N K j z)).eqTrans
        ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans (qadd_congr (.eqRefl _) (scalar_shuffle _ _ _))))
  have hRight : Γ ⊢[PRAAx] evaluate (productStep C N K j) z ≐
      qadd (qmul (evaluate (euler C N) z) (evaluate (stage C N K j) z))
        (qmul (inverseFactorial (succ j)) (qmul (evaluate (euler C N) z) (evaluate (powerPrefix C N K (succ j)) z))) :=
    (added_evaluation _ _ _ _ (padded_length C N K j) (scaled_length_at C N K j)).eqTrans
      (qadd_congr ((pad_evaluation _ _ _).eqTrans
        (product_evaluation _ _ _ _ z (euler_length C N) (stage_length C N K j)))
        ((evaluation_linearity _ _ _).eqTrans
          (qmul_congr (.eqRefl _) (product_evaluation _ _ _ _ z (euler_length C N) (prefix_length C N K (succ j))))))
  exact hLeft.eqTrans hRight.eqSymm

theorem product_successor_coefficient (C N K j i : PTm n) (hi : Γ ⊢[PRAAx] le i (N+succ j*N)) : Γ ⊢[PRAAx]
    entry (productPrefix C N K (succ j)) i ≐ entry (productStep C N K j) i := by
  have hGrid : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.gridEqual
      (productPrefix C N K (succ j)) (productStep C N K j) (N+succ j*N) := by
    refine .allI (.impI ?_)
    let Δ := le (var 0) (Syn.shift (N+succ j*N)) :: Γ.map Fm.shift
    simpa only [Δ,Syn.shift,subst_productPrefix,subst_productStep,PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ] using
      product_successor_value (Γ := Δ) (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j)
        (GaussianRationalFiniteGridIdentity.gridPoint (var 0))
  exact GaussianRationalGridCoefficientEquality.coefficient_equal _ _ _ i (product_prefix_length C N K (succ j))
    (step_length C N K j) (product_canonical _ _ _ _) (GaussianRationalMonicReduction.added_canonical _ _ _) hGrid hi

open GaussianRationalFactorialEulerSums (shiftedTerm shiftedBody shiftedSum)

theorem padded_product_coefficient (C N K j e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    entry (leftPad (productPrefix C N K j) N) (monus (N+succ j*N) e) ≐ productCoefficient C N K j e := by
  let D := N+j*N
  let I := monus (N+succ j*N) e
  have hD : Γ ⊢[PRAAx] le e D := le_trans he (le_add_right N (j*N))
  have hidx : Γ ⊢[PRAAx] I ≐ N+monus D e :=
    (congrMonus (by unfold D; ipra_ring) (.eqRefl e)).eqTrans
      (GaussianRationalLowCoefficientConvolution.index_decompose N D e hD)
  have hNI : Γ ⊢[PRAAx] le N I := le_congr (.eqRefl _) hidx.eqSymm (le_add_right N _)
  have hBound : Γ ⊢[PRAAx] le I (N+succ j*N) := GaussianRationalMonicReconstruction.monus_le_left _ _
  have hRange : Γ ⊢[PRAAx] lt I (N+length (productPrefix C N K j)) :=
    lt_congr (.eqRefl _) ((congrAdd (.eqRefl _) (product_prefix_length C N K j)).eqTrans (by ipra_ring)).eqSymm
      ((succ_monus_succ _ _).eqTrans hBound)
  exact (GaussianRationalPolynomialBuffers.pad_lookup _ _ _ hRange).eqTrans
    ((GaussianRationalPolynomialBuffers.pad_coefficient_after _ _ _ hNI).eqTrans
      ((entry_congr (.eqRefl _) ((congrMonus hidx (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans
        (exponent_inside (productPrefix C N K j) D e hD).eqSymm))

theorem product_coefficient_recurrence (C N K j e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    productCoefficient C N K (succ j) e ≐ qadd (productCoefficient C N K j e) (shiftedTerm C N K e (succ j)) := by
  let T := N+succ j*N
  let I := monus T e
  let P := product (euler C N) (powerPrefix C N K (succ j)) N (succ j*N)
  have hT : Γ ⊢[PRAAx] le e T := le_trans he (le_add_right _ _)
  have hI : Γ ⊢[PRAAx] le I T := GaussianRationalMonicReconstruction.monus_le_left _ _
  have hi : Γ ⊢[PRAAx] lt I (succ T) := (succ_monus_succ _ _).eqTrans hI
  have hP : Γ ⊢[PRAAx] lt I (length P) := lt_congr (.eqRefl _) (product_length _ _ _ _).eqSymm hi
  have hTerm : Γ ⊢[PRAAx] entry (scaled P (inverseFactorial (succ j))) I ≐ shiftedTerm C N K e (succ j) :=
    (GaussianRationalCoefficientScaling.scaled_lookup P _ I hP).eqTrans
      (qmul_congr (.eqRefl _) (exponent_inside P T e hT).eqSymm)
  exact (exponent_inside (productPrefix C N K (succ j)) T e hT).eqTrans
    ((product_successor_coefficient C N K j I hI).eqTrans
      ((GaussianRationalPolynomialBuffers.added_lookup _ _ _ I hi).eqTrans
        (qadd_congr (padded_product_coefficient C N K j e he) hTerm)))

theorem product_zero_coefficient (C N K e : PTm n) : Γ ⊢[PRAAx]
    productCoefficient C N K zero e ≐ shiftedTerm C N K e zero := by
  let P := product (euler C N) (powerPrefix C N K zero) N (zero*N)
  have hP : Γ ⊢[PRAAx] productPrefix C N K zero ≐ P :=
    GaussianPolynomialDeterminantTerms.product_congr (.eqRefl _)
      ((GaussianRationalPolynomialExponential.stage_zero C N K).eqTrans
        (GaussianRationalPolynomialPowers.prefix_zero C N K).eqSymm) (.eqRefl _) (.eqRefl _)
  have hCan := GaussianRationalPolynomialExponentialCoefficients.exponent_canonical (Γ := Γ) P (N+zero*N) e
    (product_canonical _ _ _ _) (product_length _ _ _ _)
  have hTerm : Γ ⊢[PRAAx] shiftedTerm C N K e zero ≐ exponentCoefficient P (N+zero*N) e :=
    (qmul_congr GaussianRationalPolynomialExponential.inverse_factorial_zero (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right _ hCan))
  exact (exponent_congr hP (.eqRefl _) (.eqRefl _)).eqTrans hTerm.eqSymm

def sumLaw (C N K e j : PTm n) : Fm PTm n := productCoefficient C N K j e ≐ shiftedSum C N K e (succ j)
ipra_subst sumLaw
theorem sum_zero (C N K e : PTm n) : Γ ⊢[PRAAx] sumLaw C N K e zero := by
  have hs : Γ ⊢[PRAAx] shiftedSum C N K e (succ zero) ≐ shiftedTerm C N K e zero :=
    GaussianRationalFiniteSum.sum_singleton shiftedBody _
      (GaussianRationalFactorialEulerSums.shifted_body_at C N K e zero)
      (GaussianRationalHorner.qmul_canonical _ _)
  exact (product_zero_coefficient C N K e).eqTrans hs.eqSymm

theorem sum_step (C N K e j : PTm n) (he : Γ ⊢[PRAAx] le e N) (ih : Γ ⊢[PRAAx] sumLaw C N K e j) :
    Γ ⊢[PRAAx] sumLaw C N K e (succ j) :=
  (product_coefficient_recurrence C N K j e he).eqTrans
    ((qadd_congr ih (GaussianRationalFactorialEulerSums.shifted_body_at C N K e (succ j)).eqSymm).eqTrans
      (GaussianRationalFiniteSum.sum_succ shiftedBody (succ j)
        (GaussianRationalPolynomialExponentialCoefficients.data C N K e)).eqSymm)

theorem product_coefficient_sum (C N K e j : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    productCoefficient C N K j e ≐ shiftedSum C N K e (succ j) := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have all : Γ ⊢[PRAAx] .all (sumLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift e) (var 0)) := by
    ipra_qfind [subst_sumLaw]
    · exact sum_zero C N K e
    · exact sum_step _ _ _ _ _ hn.wk Prf.hyp0
  change Γ ⊢[PRAAx] sumLaw C N K e j
  simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem logarithm_product_sum (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    exponentCoefficient
      (product (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) (GaussianFiniteLogarithmPolynomial.composition d K) d (K*d))
      (d+K*d) e ≐ shiftedSum (GaussianFiniteLogarithmPolynomial.polynomial d) d K e (succ K) :=
  product_coefficient_sum _ _ _ _ _ he

def output (C N K e j : PTm n) : PTm n := pairT (productPrefix C N K j) (shiftedSum C N K e (succ j))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C N K e j : PTm n) : PTm n := PTm.app outputF ![C,N,K,e,j]
ipra_subst output
ipra_subst run

theorem program_at (C N K e j : PTm n) : Γ ⊢[PRAAx] run C N K e j ≐ output C N K e j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,K,e,j]
theorem returned_product (C N K e j : PTm n) : Γ ⊢[PRAAx] fstT (run C N K e j) ≐ productPrefix C N K j :=
  (program_at C N K e j).fstE
theorem returned_sum (C N K e j : PTm n) : Γ ⊢[PRAAx] sndT (run C N K e j) ≐ shiftedSum C N K e (succ j) :=
  (program_at C N K e j).sndE
theorem returned_coefficient_sum (C N K e j : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (fstT (run C N K e j)) (N+j*N) e ≐ sndT (run C N K e j) :=
  (exponent_congr (returned_product C N K e j) (.eqRefl _) (.eqRefl _)).eqTrans
    ((product_coefficient_sum C N K e j he).eqTrans (returned_sum C N K e j).eqSymm)

theorem actual_exponential_product_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (productPrefix (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 1+var 3*var 1) ⋏
      canonicalCoefficients (productPrefix (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (product_prefix_length _ _ _ _) (product_canonical _ _ _ _))
theorem actual_exponential_product_step_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (evaluate (productPrefix (var 0) (var 1) (var 2) (succ (var 3))) (var 4) ≐
      evaluate (productStep (var 0) (var 1) (var 2) (var 3)) (var 4)) := closeUniv 5 (product_successor_value _ _ _ _ _)
theorem actual_exponential_product_step_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1+succ (var 3)*var 1) ⟶
      entry (productPrefix (var 0) (var 1) (var 2) (succ (var 3))) (var 4) ≐
        entry (productStep (var 0) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (product_successor_coefficient _ _ _ _ _ Prf.hyp0))
theorem actual_exponential_product_low_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ productCoefficient (var 0) (var 1) (var 2) (succ (var 3)) (var 4) ≐
      qadd (productCoefficient (var 0) (var 1) (var 2) (var 3) (var 4))
        (shiftedTerm (var 0) (var 1) (var 2) (var 4) (succ (var 3)))) :=
  closeUniv 5 (.impI (product_coefficient_recurrence _ _ _ _ _ Prf.hyp0))
theorem actual_exponential_product_coefficient_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 3) (var 1) ⟶ productCoefficient (var 0) (var 1) (var 2) (var 4) (var 3) ≐
      shiftedSum (var 0) (var 1) (var 2) (var 3) (succ (var 4))) :=
  closeUniv 5 (.impI (product_coefficient_sum _ _ _ _ _ Prf.hyp0))
theorem original_logarithm_product_coefficient_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ exponentCoefficient
      (product (euler (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0))
        (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 0) (var 1*var 0))
      (var 0+var 1*var 0) (var 2) ≐
      shiftedSum (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2) (succ (var 1))) :=
  closeUniv 3 (.impI (logarithm_product_sum _ _ _ Prf.hyp0))
theorem actual_exponential_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_exponential_product_coefficient_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 3) (var 1) ⟶ exponentCoefficient (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))
      (var 1+var 4*var 1) (var 3) ≐ sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (returned_coefficient_sum _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalExponentialProductCoefficients
