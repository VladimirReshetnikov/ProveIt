import IPRADerivations.Analysis.GaussianRationalLinearCancellation

/-!
# Degree of an actual padded factorization

A coefficient certificate for the padded original polynomial transports its
nonzero flag to the actual convolution. The zero-product branches establish
that both factors are nonzero. Their computed degrees add to the original
degree, independently of the amount of padding.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPaddedProductDegree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality (coefficientsEqual)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearCancellation (coefficients_at pad_first pad_degree)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
  (degree first flag nonzeroCoefficients first_from_witness first_nonzero
   flag_one_of_found flag_one_of_nonzero flag_cases found_of_flag_one nonzero_of_flag_one success_index)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct (product)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree
  (product_degree product_failure_left product_failure_right)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem search_transfer (A B N : PTm n) (hA : Γ ⊢[PRAAx] nonzeroCoefficients A N)
    (hEntry : Γ ⊢[PRAAx] entry A (first A N) ≐ entry B (first A N)) :
    Γ ⊢[PRAAx] lt (first B N) (succ N) ⋏ le (first B N) (first A N) := by
  have found := found_of_flag_one A N (flag_one_of_nonzero A N hA)
  have nonzero := first_nonzero A N found
  exact first_from_witness B N (first A N) found
    (.impI (.impE nonzero.wk ((recode_congr hEntry).wk.eqTrans Prf.hyp0)))

theorem coefficient_nonzero (A B N : PTm n) (hA : Γ ⊢[PRAAx] nonzeroCoefficients A N)
    (hEq : Γ ⊢[PRAAx] coefficientsEqual A B N) : Γ ⊢[PRAAx] nonzeroCoefficients B N := by
  have bound := success_index A N (flag_one_of_nonzero A N hA)
  have result := search_transfer A B N hA (coefficients_at A B N (first A N) hEq bound)
  exact nonzero_of_flag_one B N (flag_one_of_found B N (.andE₁ result))

theorem coefficient_degree (A B N : PTm n) (hA : Γ ⊢[PRAAx] nonzeroCoefficients A N)
    (hEq : Γ ⊢[PRAAx] coefficientsEqual A B N) : Γ ⊢[PRAAx] degree A N ≐ degree B N := by
  have boundA := success_index A N (flag_one_of_nonzero A N hA)
  have hB := coefficient_nonzero A B N hA hEq
  have boundB := success_index B N (flag_one_of_nonzero B N hB)
  have forward := search_transfer A B N hA (coefficients_at A B N (first A N) hEq boundA)
  have backward := search_transfer B A N hB (coefficients_at A B N (first B N) hEq boundB).eqSymm
  exact congrMonus (.eqRefl _) (le_antisymm (.andE₂ backward) (.andE₂ forward))

theorem padded_nonzero (P D T : PTm n) (hLength : Γ ⊢[PRAAx] length P ≐ succ D)
    (hP : Γ ⊢[PRAAx] nonzeroCoefficients P D) : Γ ⊢[PRAAx] nonzeroCoefficients (leftPad P T) (T+D) := by
  have bound := add_le_add₂ (le_refl T) (success_index P D (flag_one_of_nonzero P D hP))
  have found := (succ_monus_succ (T+first P D) (T+D)).eqTrans bound
  have padded := lt_congr (pad_first P D T hLength hP).eqSymm (.eqRefl _) found
  exact nonzero_of_flag_one _ _ (flag_one_of_found _ _ padded)

theorem factors_nonzero (C Q T D : PTm n)
    (hProduct : Γ ⊢[PRAAx] nonzeroCoefficients (product C Q T D) (T+D)) :
    Γ ⊢[PRAAx] nonzeroCoefficients C T ⋏ nonzeroCoefficients Q D := by
  have success := flag_one_of_nonzero _ _ hProduct
  apply Prf.andI
  · refine .orE (flag_cases C T) ?_ (nonzero_of_flag_one _ _ Prf.hyp0)
    exact .botE _ (succ_ne_zero (success.wk.eqSymm.eqTrans (product_failure_left C Q T D Prf.hyp0)))
  · refine .orE (flag_cases Q D) ?_ (nonzero_of_flag_one _ _ Prf.hyp0)
    exact .botE _ (succ_ne_zero (success.wk.eqSymm.eqTrans (product_failure_right C Q T D Prf.hyp0)))

def input (P C Q T D : PTm n) : Fm PTm n := (length P ≐ succ D) ⋏
  (nonzeroCoefficients P D ⋏ coefficientsEqual (leftPad P T) (product C Q T D) (T+D))

def certificate (P C Q T D : PTm n) : Fm PTm n := nonzeroCoefficients C T ⋏
  (nonzeroCoefficients Q D ⋏ degree P D ≐ degree C T+degree Q D)

theorem padded_factorization (P C Q T D : PTm n) (h : Γ ⊢[PRAAx] input P C Q T D) :
    Γ ⊢[PRAAx] certificate P C Q T D := by
  have shape := Prf.andE₁ h
  have nonzero := Prf.andE₁ (Prf.andE₂ h)
  have coefficients := Prf.andE₂ (Prf.andE₂ h)
  have original := padded_nonzero P D T shape nonzero
  have productNonzero := coefficient_nonzero _ _ _ original coefficients
  have factors := factors_nonzero C Q T D productNonzero
  have degrees := (pad_degree P D T shape nonzero).eqSymm.eqTrans
    ((coefficient_degree _ _ _ original coefficients).eqTrans
      (product_degree C Q T D (.andE₁ factors) (.andE₂ factors)))
  exact .andI (.andE₁ factors) (.andI (.andE₂ factors) degrees)

theorem factor_degree_le (P C Q T D : PTm n) (h : Γ ⊢[PRAAx] input P C Q T D) :
    Γ ⊢[PRAAx] le (degree C T) (degree P D) := by
  have degrees := Prf.andE₂ (Prf.andE₂ (padded_factorization P C Q T D h))
  exact le_congr (.eqRefl _) degrees.eqSymm (le_add_right (degree C T) (degree Q D))

theorem full_width_factor_le (P C Q T D : PTm n) (h : Γ ⊢[PRAAx] input P C Q T D)
    (hDegree : Γ ⊢[PRAAx] degree C T ≐ T) : Γ ⊢[PRAAx] le T (degree P D) :=
  le_congr hDegree (.eqRefl _) (factor_degree_le P C Q T D h)

theorem actual_padded_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ certificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (padded_factorization _ _ _ _ _ Prf.hyp0))

theorem actual_full_width_factor_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ degree (var 1) (var 3) ≐ var 3 ⟶
      le (var 3) (degree (var 0) (var 4))) :=
  closeUniv 5 (.impI (.impI (full_width_factor_le _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalPaddedProductDegree
