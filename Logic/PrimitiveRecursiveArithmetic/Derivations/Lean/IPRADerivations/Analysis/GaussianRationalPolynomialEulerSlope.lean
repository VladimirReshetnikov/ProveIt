import IPRADerivations.Analysis.GaussianRationalFirstOrderPolynomial
import IPRADerivations.Analysis.GaussianRationalSumAlgebra
import IPRADerivations.Analysis.GaussianEulerBetaPoleGuard

/-!
# The actual synthetic slope is the original Euler polynomial value

A genuine guarded Horner-prefix induction identifies the SAME original
Euler coefficient buffer with t times the computed synthetic slope.
Every degree is internal, including degree zero. The original Beta
primitive consequently satisfies its literal finite first-order equation.
No differentiability or Euler evaluation identity is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialEulerSlope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul horner evaluate canonical)
open GaussianRationalSyntheticDivision (quotient qadd_congr qmul_congr)
open GaussianRationalFirstOrderPolynomial (slope)
open GaussianRationalEulerCoefficients (euler)
open GaussianRationalNaturalScale (natScale natScale_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianReciprocalHorner (qadd_commutative)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem right_distribute (a b t : PTm n) : Γ ⊢[PRAAx]
    qmul (qadd a b) t ≐ qadd (qmul a t) (qmul b t) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

private theorem scale_sum (m a b : PTm n) : Γ ⊢[PRAAx]
    natScale m (qadd a b) ≐ qadd (natScale m a) (natScale m b) :=
  (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm))

private theorem triple_exchange (a b c : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd a b) c ≐ qadd (qadd a c) b :=
  (qadd_associative _ _ _).eqTrans
    ((qadd_congr (.eqRefl _) (qadd_commutative _ _)).eqTrans (qadd_associative _ _ _).eqSymm)

private theorem four_exchange (a b c d : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd (qadd a b) c) d ≐ qadd (qadd a d) (qadd b c) :=
  (qadd_congr (qadd_associative _ _ _) (.eqRefl _)).eqTrans (triple_exchange _ _ _)

/-- Exact algebra used in the real original Horner successor. -/
theorem successor_algebra (m H J c t : PTm n) (hH : Γ ⊢[PRAAx] canonical H) : Γ ⊢[PRAAx]
    qadd (qmul (qadd (natScale (succ m) H) (qmul J t)) t) (natScale m c) ≐
      qadd (natScale m (qadd (qmul H t) c)) (qmul (qadd (qmul J t) H) t) := by
  have scaling : Γ ⊢[PRAAx] natScale (succ m) H ≐ qadd (natScale m H) H :=
    (natScale_congr (by ipra_ring) (.eqRefl _)).eqTrans
      ((GaussianRationalNaturalScale.natScale_add m one H).eqTrans
        (qadd_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_one_canonical H hH)))
  have expanded : Γ ⊢[PRAAx]
      qadd (qmul (qadd (natScale (succ m) H) (qmul J t)) t) (natScale m c) ≐
        qadd (qadd (qmul (natScale m H) t) (natScale m c)) (qadd (qmul H t) (qmul (qmul J t) t)) := (qadd_congr (qmul_congr (qadd_congr scaling (.eqRefl _)) (.eqRefl _)) (.eqRefl (natScale m c))).eqTrans
    ((qadd_congr ((right_distribute _ _ _).eqTrans (qadd_congr (right_distribute _ _ _) (.eqRefl _))) (.eqRefl _)).eqTrans
      (four_exchange _ _ _ _))
  have first : Γ ⊢[PRAAx] qadd (qmul (natScale m H) t) (natScale m c) ≐ natScale m (qadd (qmul H t) c) :=
    (qadd_congr (GaussianRationalWeightedCoefficientConvolution.left_scale_product m H t).eqSymm (.eqRefl _)).eqTrans
      (scale_sum m (qmul H t) c).eqSymm
  have second : Γ ⊢[PRAAx] qadd (qmul H t) (qmul (qmul J t) t) ≐ qmul (qadd (qmul J t) H) t :=
    (right_distribute H (qmul J t) t).eqSymm.eqTrans (qmul_congr (qadd_commutative _ _) (.eqRefl _))
  exact expanded.eqTrans (qadd_congr first second)

private theorem horner_first (C t : PTm n) : Γ ⊢[PRAAx]
    horner C t one ≐ GaussianTranslatedNonconstant.recode (entry C zero) :=
  (GaussianRationalHorner.horner_succ C t zero).eqTrans
    (qadd_congr ((qmul_congr (GaussianRationalHorner.horner_zero C t) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_left t)) (.eqRefl _))

private theorem scale_recode (m a : PTm n) : Γ ⊢[PRAAx]
    natScale m (GaussianTranslatedNonconstant.recode a) ≐ natScale m a :=
  (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
    ((GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqTrans
      (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm)

def prefixLaw (C N t k : PTm n) : Fm PTm n := le k N ⟶
  horner (euler C N) t (succ k) ≐ qadd (natScale (monus N k) (horner C t (succ k))) (qmul (horner (quotient C t N) t k) t)
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C N t k : PTm n) :
    (prefixLaw C N t k).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ k) := by simp [prefixLaw]

theorem prefix_zero (C N t : PTm n) : Γ ⊢[PRAAx]
    horner (euler C N) t one ≐ qadd (natScale (monus N zero) (horner C t one)) (qmul (horner (quotient C t N) t zero) t) := by
  have row : Γ ⊢[PRAAx] entry (euler C N) zero ≐ natScale N (entry C zero) :=
    (GaussianRationalEulerCoefficients.euler_lookup C N zero (zero_le N)).eqTrans (natScale_congr (monus_zero N) (.eqRefl _))
  have left := (horner_first (euler C N) t).eqTrans
    ((GaussianTranslatedNonconstant.recode_congr row).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (GaussianRationalNaturalScale.natScale_canonical _ _)))
  have right : Γ ⊢[PRAAx]
      qadd (natScale (monus N zero) (horner C t one)) (qmul (horner (quotient C t N) t zero) t) ≐ natScale N (entry C zero) :=
    (qadd_congr (natScale_congr (monus_zero N) (horner_first C t))
    ((qmul_congr (GaussianRationalHorner.horner_zero _ _) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left t))).eqTrans
      ((qadd_congr (scale_recode N (entry C zero)) (.eqRefl _)).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalNaturalScale.natScale_canonical _ _)))
  exact left.eqTrans right.eqSymm

theorem weight_successor (N k : PTm n) (hk : Γ ⊢[PRAAx] le (succ k) N) : Γ ⊢[PRAAx]
    monus N k ≐ succ (monus N (succ k)) := by
  have e := natEq (eq_add_of_le hk)
  have f := natEq (eq_add_of_le (le_trans (le_succ_self k) hk))
  apply deriveNat
  ipra_simps
  linear_combination e-f

theorem prefix_step (C N t k : PTm n) (hk : Γ ⊢[PRAAx] le (succ k) N)
    (ih : Γ ⊢[PRAAx] horner (euler C N) t (succ k) ≐
      qadd (natScale (monus N k) (horner C t (succ k))) (qmul (horner (quotient C t N) t k) t)) : Γ ⊢[PRAAx]
    horner (euler C N) t (succ (succ k)) ≐
      qadd (natScale (monus N (succ k)) (horner C t (succ (succ k)))) (qmul (horner (quotient C t N) t (succ k)) t) := by
  have row := GaussianRationalEulerCoefficients.euler_lookup C N (succ k) hk
  have product := (GaussianRationalHorner.horner_succ (euler C N) t (succ k)).eqTrans
    ((qadd_congr (qmul_congr ih (.eqRefl _)) row).eqTrans
      ((qadd_congr (qmul_congr (qadd_congr (natScale_congr (weight_successor N k hk) (.eqRefl _)) (.eqRefl _)) (.eqRefl _)) (.eqRefl _)).eqTrans
        (successor_algebra (monus N (succ k)) (horner C t (succ k)) (horner (quotient C t N) t k) (entry C (succ k)) t (GaussianRationalHorner.horner_canonical _ _ _))))
  have qstep : Γ ⊢[PRAAx] horner (quotient C t N) t (succ k) ≐
      qadd (qmul (horner (quotient C t N) t k) t) (horner C t (succ k)) :=
    (GaussianRationalHorner.horner_succ _ _ _).eqTrans
      (qadd_congr (.eqRefl _) (GaussianRationalSyntheticDivision.quotient_lookup C t N k hk))
  exact product.eqTrans (qadd_congr (natScale_congr (.eqRefl _) (GaussianRationalHorner.horner_succ C t (succ k)).eqSymm)
    (qmul_congr qstep.eqSymm (.eqRefl _)))

theorem horner_prefix (C N t k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    horner (euler C N) t (succ k) ≐ qadd (natScale (monus N k) (horner C t (succ k))) (qmul (horner (quotient C t N) t k) t) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift t) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero C N t).wk
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (prefix_step _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] prefixLaw C N t k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem euler_slope (C N t : PTm n) : Γ ⊢[PRAAx]
    evaluate (euler C N) t ≐ qmul t (slope C t N) := by
  have terminal := horner_prefix (Γ := Γ) C N t N (le_refl N)
  have left : Γ ⊢[PRAAx] evaluate (euler C N) t ≐ horner (euler C N) t (succ N) :=
    congrAp3 GaussianRationalHorner.hornerF (GaussianRationalEulerCoefficients.euler_length C N) (.eqRefl _) (.eqRefl _)
  have right : Γ ⊢[PRAAx]
      qadd (natScale (monus N N) (horner C t (succ N))) (qmul (horner (quotient C t N) t N) t) ≐ qmul t (slope C t N) :=
    (qadd_congr ((natScale_congr (monus_self N) (.eqRefl _)).eqTrans (GaussianRationalNaturalScale.natScale_zero _))
    (qmul_congr (congrAp3 GaussianRationalHorner.hornerF (GaussianRationalSyntheticDivision.quotient_length C t N).eqSymm (.eqRefl _) (.eqRefl _)) (.eqRefl _))).eqTrans
      ((GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  exact left.eqTrans (terminal.eqTrans right)

/-- Literal decomposition of the SAME existing Beta Euler operator. -/
theorem beta_operator_slope (z B N t : PTm n) : Γ ⊢[PRAAx]
    evaluate (GaussianEulerBetaPolynomialPrimitive.eulerOperator z B N) t ≐
      qadd (qmul (GaussianRationalHorner.ofGaussian z B) (evaluate (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t))
        (qmul t (GaussianRationalFirstOrderPolynomial.betaSlope z B N t)) := by
  let C := GaussianEulerBetaPolynomialPrimitive.primitive z B N
  let S := GaussianRationalMonicReduction.singleton (GaussianRationalHorner.ofGaussian z B)
  have shape : Γ ⊢[PRAAx] length (GaussianRationalPolynomialProduct.product S C zero N) ≐ succ N :=
    (GaussianRationalPolynomialProduct.product_length S C zero N).eqTrans (congrSucc (zero_add N))
  have sum := GaussianRationalPolynomialBuffers.added_evaluation (GaussianRationalPolynomialProduct.product S C zero N)
    (euler C N) (succ N) t shape (GaussianRationalEulerCoefficients.euler_length C N)
  have product := GaussianRationalPolynomialProduct.product_evaluation (Γ := Γ) S C zero N t
    (GaussianRationalMonicReduction.singleton_length _) (GaussianEulerBetaPolynomialPrimitive.primitive_length z B N)
  have factor : Γ ⊢[PRAAx] qmul (evaluate S t) (evaluate C t) ≐ qmul (GaussianRationalHorner.ofGaussian z B) (evaluate C t) :=
    (qmul_congr (GaussianRationalMonicReduction.singleton_evaluation _ _) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticCoefficientValues.qmul_recode_left _ _)
  exact sum.eqTrans (qadd_congr (product.eqTrans factor) (euler_slope C N t))

/-- Genuine finite first-order Beta identity, using only the original
positive real-part source and the unchanged actual primitive/slope. -/
theorem beta_first_order_equation (z B A N t : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerBetaPoleGuard.source z B A) (ht : Γ ⊢[PRAAx] canonical t) : Γ ⊢[PRAAx]
    qadd (qmul (GaussianRationalHorner.ofGaussian z B) (evaluate (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t))
      (qmul t (GaussianRationalFirstOrderPolynomial.betaSlope z B N t)) ≐
        GaussianRationalReciprocal.power (GaussianRationalMetric.qsub GaussianRationalReciprocal.qone t) N :=
  (beta_operator_slope z B N t).eqSymm.eqTrans
    (GaussianEulerBetaPolynomialPrimitive.operator_evaluation z B A N t (GaussianEulerBetaPoleGuard.primitive_input z B A N h) ht)

theorem original_beta_first_order_equation (z R B A N t : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) (ht : Γ ⊢[PRAAx] canonical t) : Γ ⊢[PRAAx]
    qadd (qmul (GaussianRationalHorner.ofGaussian z B) (evaluate (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t))
      (qmul t (GaussianRationalFirstOrderPolynomial.betaSlope z B N t)) ≐
        GaussianRationalReciprocal.power (GaussianRationalMetric.qsub GaussianRationalReciprocal.qone t) N :=
  beta_first_order_equation z B A N t (GaussianEulerBetaPoleGuard.original_integral_source z R B A N h).andE₁ ht

/-- The original Euler value, actual slope, and their exact product are
computed together by an actual primitive-recursive program. -/
def output (C N t : PTm n) : PTm n := pairT (evaluate (euler C N) t) (pairT (slope C t N) (qmul t (slope C t N)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N t : PTm n) : PTm n := ap3 outputF C N t
theorem program_at (C N t : PTm n) : Γ ⊢[PRAAx] run C N t ≐ output C N t := by
  simpa [run,outputF,output,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,t]

theorem actual_Euler_polynomial_synthetic_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (euler (var 0) (var 1)) (var 2) ≐ qmul (var 2) (slope (var 0) (var 2) (var 1))) :=
  closeUniv 3 (euler_slope _ _ _)
theorem original_Beta_primitive_first_order_equation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((GaussianEulerLowerPowerCoefficients.source (var 0) (var 1) (var 2) (var 3) ⋏ canonical (var 5)) ⟶
      qadd (qmul (GaussianRationalHorner.ofGaussian (var 0) (var 2)) (evaluate (GaussianEulerBetaPolynomialPrimitive.primitive (var 0) (var 2) (var 4)) (var 5)))
        (qmul (var 5) (GaussianRationalFirstOrderPolynomial.betaSlope (var 0) (var 2) (var 4) (var 5))) ≐
          GaussianRationalReciprocal.power (GaussianRationalMetric.qsub GaussianRationalReciprocal.qone (var 5)) (var 4)) :=
  closeUniv 6 (.impI (original_beta_first_order_equation _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_Beta_primitive_Euler_operator_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (evaluate (GaussianEulerBetaPolynomialPrimitive.eulerOperator (var 0) (var 1) (var 2)) (var 3) ≐
      qadd (qmul (GaussianRationalHorner.ofGaussian (var 0) (var 1)) (evaluate (GaussianEulerBetaPolynomialPrimitive.primitive (var 0) (var 1) (var 2)) (var 3)))
        (qmul (var 3) (GaussianRationalFirstOrderPolynomial.betaSlope (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (beta_operator_slope _ _ _ _)
theorem actual_Euler_slope_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialEulerSlope
