import IPRADerivations.Analysis.Exponential.FiniteSeries.GaussianScalarExponentialDiagonal
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariatePowerExpansion
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower

/-!
# The exact low degrees of the original rectangular exponential product

Each original scalar truncation has an actual descending coefficient
buffer in a formal variable. Its evaluation at one is the original
scalar sum. The product of the two buffers agrees in low degrees with
the finite scalar exponential at the sum of the original arguments.
The exact discrepancy is the actual high part of the original buffer.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarExponentialProductLowDegrees

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul evaluate canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianRationalPolynomialExponential (scalarBody scalarSum)
open GaussianScalarExponentialDiagonal (coefficient coefficient_congr coefficient_canonical original_term
  diagonal diagonal_at_sum)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside product_exponent)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def bufferBody : PTm 2 := coefficient (fstT (var 1)) (monus (sndT (var 1)) (var 0))
def buffer (q K : PTm n) : PTm n := sequence bufferBody (succ K) (pairT q K)

@[simp] theorem subst_buffer {m : ℕ} (σ : Fin n → PTm m) (q K : PTm n) :
    Syn.subst σ (buffer q K) = buffer (Syn.subst σ q) (Syn.subst σ K) := by simp [buffer]

theorem buffer_length (q K : PTm n) : Γ ⊢[PRAAx] length (buffer q K) ≐ succ K :=
  sequence_length _ _ _

theorem descending_at (q K i : PTm n) (hi : Γ ⊢[PRAAx] le i K) :
    Γ ⊢[PRAAx] entry (buffer q K) i ≐ coefficient q (monus K i) := by
  have e := sequence_decode bufferBody (x := pairT q K) ((succ_monus_succ _ _).eqTrans hi)
  simp only [inst2,bufferBody,GaussianScalarExponentialDiagonal.subst_coefficient,PTm.subst_monus,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at e
  exact e.eqTrans (coefficient_congr (fst_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _)))

theorem ascending_at (q K e : PTm n) (he : Γ ⊢[PRAAx] le e K) :
    Γ ⊢[PRAAx] entry (buffer q K) (monus K e) ≐ coefficient q e :=
  (descending_at q K _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (coefficient_congr (.eqRefl _) (GaussianRationalMonicReconstruction.complement K e he))

theorem term_at_one (C K e : PTm n) (he : Γ ⊢[PRAAx] le e K)
    (hc : Γ ⊢[PRAAx] canonical (entry C (monus K e))) :
    Γ ⊢[PRAAx] inst2 GaussianRationalPowerExpansion.termBody e (GaussianRationalPowerExpansion.data C K qone) ≐
      exponentCoefficient C K e := by
  have eq : Γ ⊢[PRAAx] GaussianOffDominantTerms.term C K qone e ≐ qmul (entry C (monus K e))
      (GaussianRationalReciprocal.power qone e) := .eqRefl _
  exact (GaussianRationalPowerExpansion.term_body_at C K qone e).eqTrans (eq.eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalRoundedPower.qone_power e)).eqTrans
      ((qmul_one_right _ hc).eqTrans (exponent_inside C K e he).eqSymm)))

theorem buffer_at_one (q K : PTm n) : Γ ⊢[PRAAx] evaluate (buffer q K) qone ≐ scalarSum q K := by
  apply (GaussianBivariatePowerExpansion.evaluate_power_sum _ _ _ (buffer_length q K)).eqTrans
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift K)) :: Γ.map Fm.shift
  let v := Syn.shift q
  let T := Syn.shift K
  have hi : Δ ⊢[PRAAx] le (var 0) T := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have c := ascending_at v T (var 0) hi
  have can := GaussianRationalHorner.canonical_congr c (coefficient_canonical v (var 0))
  have eq := (term_at_one (buffer v T) T (var 0) hi can).eqTrans
    ((exponent_inside _ _ _ hi).eqTrans c)
  simpa only [Δ,v,T,Syn.shift,subst_buffer,GaussianRationalPowerExpansion.subst_data,
    GaussianRationalSyntheticDivision.subst_qone,ConciseIPRA.PTm.subst_succ,original_term] using eq

def product (u v K : PTm n) : PTm n :=
  GaussianRationalPolynomialProduct.product (buffer u K) (buffer v K) K K

@[simp] theorem subst_product {m : ℕ} (σ : Fin n → PTm m) (u v K : PTm n) :
    Syn.subst σ (product u v K) = product (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ K) := by simp [product]

theorem product_length (u v K : PTm n) : Γ ⊢[PRAAx] length (product u v K) ≐ succ (K+K) :=
  GaussianRationalPolynomialProduct.product_length _ _ _ _

theorem product_at_one (u v K : PTm n) :
    Γ ⊢[PRAAx] evaluate (product u v K) qone ≐ qmul (scalarSum u K) (scalarSum v K) :=
  (GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _ (buffer_length u K) (buffer_length v K)).eqTrans
    (qmul_congr (buffer_at_one u K) (buffer_at_one v K))

theorem product_low_degree (u v K e : PTm n) (he : Γ ⊢[PRAAx] le e K) :
    Γ ⊢[PRAAx] exponentCoefficient (product u v K) (K+K) e ≐ coefficient (qadd u v) e := by
  have before : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift K) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  apply (product_exponent (buffer u K) (buffer v K) K K e he he).eqTrans
  refine (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqTrans (diagonal_at_sum u v e)
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let a := Syn.shift u
  let b := Syn.shift v
  let T := Syn.shift K
  let E := Syn.shift e
  have leE : Δ ⊢[PRAAx] le i E := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have l := ascending_at a T i (le_trans leE before.wk)
  have r := ascending_at (Γ := Δ) b T (monus E i)
    (le_trans (GaussianRationalMonicReconstruction.monus_le_left E i) before.wk)
  have eq := (GaussianRationalLowCoefficientConvolution.term_at (buffer a T) (buffer b T) T T E i).eqTrans
    ((qmul_congr l r).eqTrans (GaussianScalarExponentialDiagonal.term_at a b E i).eqSymm)
  simpa only [Δ,i,a,b,T,E,Syn.shift,subst_buffer,GaussianRationalLowCoefficientConvolution.subst_data,
    GaussianScalarExponentialDiagonal.subst_data,ConciseIPRA.PTm.subst_succ] using eq

def evaluationData (u v K : PTm n) : PTm n :=
  GaussianRationalPowerExpansion.data (product u v K) (K+K) qone

def highPart (u v K : PTm n) : PTm n := GaussianRationalFiniteSum.sum (offB GaussianRationalPowerExpansion.termBody)
  K (pairT (succ K) (evaluationData u v K))

@[simp] theorem subst_evaluationData {m : ℕ} (σ : Fin n → PTm m) (u v K : PTm n) :
    Syn.subst σ (evaluationData u v K) = evaluationData (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ K) := by
  simp [evaluationData]

@[simp] theorem subst_highPart {m : ℕ} (σ : Fin n → PTm m) (u v K : PTm n) :
    Syn.subst σ (highPart u v K) = highPart (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ K) := by
  simp [highPart]

theorem original_low_part (u v K : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ K) (evaluationData u v K) ≐
      scalarSum (qadd u v) K := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift K)) :: Γ.map Fm.shift
  let a := Syn.shift u
  let b := Syn.shift v
  let T := Syn.shift K
  let i : PTm (n+1) := var 0
  let C := product a b T
  have h : Δ ⊢[PRAAx] le i T := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have h' := le_trans h (le_add_right T T)
  have productEntry := (exponent_inside C (T+T) i h').eqSymm.eqTrans (product_low_degree a b T i h)
  have can := GaussianRationalHorner.canonical_congr productEntry (coefficient_canonical (qadd a b) i)
  have eq := (term_at_one C (T+T) i h' can).eqTrans (product_low_degree a b T i h)
  simpa only [Δ,a,b,T,i,C,Syn.shift,subst_evaluationData,evaluationData,GaussianRationalHorner.subst_qadd,
    GaussianRationalPowerExpansion.subst_data,subst_product,PTm.subst_add,
    GaussianRationalSyntheticDivision.subst_qone,ConciseIPRA.PTm.subst_succ,original_term] using eq

theorem high_part_term (u v K i : PTm n) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] inst2 (offB GaussianRationalPowerExpansion.termBody) i (pairT (succ K) (evaluationData u v K)) ≐
      exponentCoefficient (product u v K) (K+K) (succ K+i) := by
  let C := product u v K
  let e := succ K+i
  have h : Γ ⊢[PRAAx] le e (K+K) :=
    le_congr ((add_comm (succ i) K).eqTrans ((add_succ K i).eqTrans (succ_add K i).eqSymm))
      (.eqRefl _) (add_le_add_right K hi)
  have can : Γ ⊢[PRAAx] canonical (exponentCoefficient C (K+K) e) :=
    GaussianRationalPolynomialExponentialCoefficients.exponent_canonical _ _ _
      (GaussianRationalPolynomialProduct.product_canonical (buffer u K) (buffer v K) K K)
      (product_length _ _ _)
  exact (GaussianRationalFiniteProduct.offset_at _ _ _ _).eqTrans
    (term_at_one C (K+K) e h (GaussianRationalHorner.canonical_congr (exponent_inside _ _ _ h).eqSymm can))

theorem exact_rectangular_product_split (u v K : PTm n) :
    Γ ⊢[PRAAx] qmul (scalarSum u K) (scalarSum v K) ≐ qadd (scalarSum (qadd u v) K) (highPart u v K) := by
  let f := GaussianRationalPowerExpansion.termBody
  let D := evaluationData u v K
  let C := product u v K
  have evaluation : Γ ⊢[PRAAx] evaluate C qone ≐ GaussianRationalFiniteSum.sum f (succ (K+K)) D :=
    GaussianBivariatePowerExpansion.evaluate_power_sum _ _ _ (product_length u v K)
  have split := (GaussianRationalFiniteSum.sum_index_congr (Γ := Γ) f (succ_add K K).eqSymm (.eqRefl D)).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split f (succ K) K D)
  exact (product_at_one u v K).eqSymm.eqTrans (evaluation.eqTrans
    (split.eqTrans (GaussianRationalSyntheticDivision.qadd_congr (original_low_part u v K) (.eqRefl _))))

theorem original_scalar_buffer_at_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (evaluate (buffer (var 0) (var 1)) qone ≐ scalarSum (var 0) (var 1)) :=
  closeUniv 2 (buffer_at_one _ _)

theorem exact_rectangular_low_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 2) ⟶ exponentCoefficient (product (var 0) (var 1) (var 2)) (var 2+var 2) (var 3) ≐
      coefficient (qadd (var 0) (var 1)) (var 3)) :=
  closeUniv 4 (.impI (product_low_degree _ _ _ _ Prf.hyp0))

theorem exact_rectangular_high_entry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶
      inst2 (offB GaussianRationalPowerExpansion.termBody) (var 3)
        (pairT (succ (var 2)) (evaluationData (var 0) (var 1) (var 2))) ≐
      exponentCoefficient (product (var 0) (var 1) (var 2)) (var 2+var 2) (succ (var 2)+var 3)) :=
  closeUniv 4 (.impI (high_part_term _ _ _ _ Prf.hyp0))

theorem exact_rectangular_product_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qmul (scalarSum (var 0) (var 2)) (scalarSum (var 1) (var 2)) ≐
      qadd (scalarSum (qadd (var 0) (var 1)) (var 2)) (highPart (var 0) (var 1) (var 2))) :=
  closeUniv 3 (exact_rectangular_product_split _ _ _)

end LeanProofs.IPRA.Analysis.GaussianScalarExponentialProductLowDegrees
