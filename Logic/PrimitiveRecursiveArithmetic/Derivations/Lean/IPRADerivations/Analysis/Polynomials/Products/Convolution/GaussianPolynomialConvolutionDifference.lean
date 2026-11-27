import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianRationalConvolutionNorm
import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianRationalGridCoefficientEquality
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference

/-!
# Coefficient error of the original convolution

The stored difference of two computed products equals the sum of the
two product differences coefficient by coefficient. The exact finite
product norm then bounds the stored error by the two individual errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialConvolutionDifference

open_ipra
open GaussianRationalPolynomialProduct (product product_length product_evaluation)
open GaussianRationalPolynomialBuffers (added added_length added_lookup added_evaluation)
open GaussianCoefficientL1 (coefficientNorm subCoefficients sub_lookup)
open GaussianRationalMonicCompanion (sub_length difference_evaluation)
open GaussianRationalConvolutionNorm (product_norm)
open GaussianPolynomialNormBuffers (norm_entries norm_added)
open GaussianRationalHorner (evaluate canonical qadd_canonical)
open GaussianRationalMetric (qsub_canonical)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qadd_congr)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianRationalGridCoefficientEquality (gridEqual coefficient_recode_equal)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianTranslatedNonconstant (recode_eq)
open GaussianRationalSumSegments (entriesEqual)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (P Q A B d e : PTm n) : Fm PTm n :=
  length P ≐ succ d ⋏ (length Q ≐ succ e ⋏ (length A ≐ succ d ⋏ length B ≐ succ e))

def difference (P Q A B d e : PTm n) : PTm n :=
  subCoefficients (product P Q d e) (product A B d e) (succ (d + e))

def leftTerm (P Q A d e : PTm n) : PTm n := product (subCoefficients P A (succ d)) Q d e
def rightTerm (Q A B d e : PTm n) : PTm n := product A (subCoefficients Q B (succ e)) d e

def expansion (P Q A B d e : PTm n) : PTm n :=
  added (leftTerm P Q A d e) (rightTerm Q A B d e) (succ (d + e))

ipra_subst input
ipra_subst difference
ipra_subst expansion [leftTerm, rightTerm]

theorem evaluation_identity (P Q A B d e z : PTm n) (h : Γ ⊢[PRAAx] input P Q A B d e) :
    Γ ⊢[PRAAx] evaluate (difference P Q A B d e) z ≐ evaluate (expansion P Q A B d e) z := by
  have hp := Prf.andE₁ h
  have hq := Prf.andE₁ (Prf.andE₂ h)
  have ha := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hb := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have left := (difference_evaluation (product P Q d e) (product A B d e) (succ (d + e)) z
    (product_length _ _ _ _) (product_length _ _ _ _)).eqTrans
      (qsub_congr (product_evaluation _ _ _ _ _ hp hq) (product_evaluation _ _ _ _ _ ha hb))
  have right := (added_evaluation (leftTerm P Q A d e) (rightTerm Q A B d e) (succ (d + e)) z
    (product_length _ _ _ _) (product_length _ _ _ _)).eqTrans
      (qadd_congr
        ((product_evaluation (subCoefficients P A (succ d)) Q d e z (sub_length _ _ _) hq).eqTrans
          (qmul_congr (difference_evaluation _ _ _ _ hp ha) (.eqRefl _)))
        ((product_evaluation A (subCoefficients Q B (succ e)) d e z ha (sub_length _ _ _)).eqTrans
          (qmul_congr (.eqRefl _) (difference_evaluation _ _ _ _ hq hb))))
  exact left.eqTrans ((GaussianRationalPowerDifference.product_difference _ _ _ _).eqTrans right.eqSymm)

theorem coefficient_identity (P Q A B d e i : PTm n) (h : Γ ⊢[PRAAx] input P Q A B d e)
    (hi : Γ ⊢[PRAAx] le i (d + e)) :
    Γ ⊢[PRAAx] entry (difference P Q A B d e) i ≐ entry (expansion P Q A B d e) i := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift P) (Syn.shift Q) (Syn.shift A) (Syn.shift B)
      (Syn.shift d) (Syn.shift e) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  have grid : Γ ⊢[PRAAx] gridEqual (difference P Q A B d e) (expansion P Q A B d e) (d + e) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift, subst_difference, subst_expansion] using
      evaluation_identity (Syn.shift P) (Syn.shift Q) (Syn.shift A) (Syn.shift B)
        (Syn.shift d) (Syn.shift e) (gridPoint (var 0)) hs.wk
  have bound : Γ ⊢[PRAAx] lt i (succ (d + e)) := (succ_monus_succ _ _).eqTrans hi
  have hl : Γ ⊢[PRAAx] canonical (entry (difference P Q A B d e) i) :=
    GaussianRationalHorner.canonical_congr (sub_lookup _ _ _ _ bound) (qsub_canonical _ _)
  have hr : Γ ⊢[PRAAx] canonical (entry (expansion P Q A B d e) i) :=
    GaussianRationalHorner.canonical_congr (added_lookup _ _ _ _ bound) (qadd_canonical _ _)
  exact (recode_eq _ hl).eqSymm.eqTrans
    ((coefficient_recode_equal _ _ _ _ (sub_length _ _ _) (added_length _ _ _) grid hi).eqTrans (recode_eq _ hr))

theorem error_norm_bound (P Q A B d e : PTm n) (h : Γ ⊢[PRAAx] input P Q A B d e) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (difference P Q A B d e))
      (add (multiply (coefficientNorm (subCoefficients P A (succ d))) (coefficientNorm Q))
        (multiply (coefficientNorm A) (coefficientNorm (subCoefficients Q B (succ e))))) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift P) (Syn.shift Q) (Syn.shift A) (Syn.shift B)
      (Syn.shift d) (Syn.shift e) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  have entries : Γ ⊢[PRAAx] entriesEqual (difference P Q A B d e) (expansion P Q A B d e) (succ (d + e)) := by
    refine .allI (.impI ?_)
    have range : lt (var 0) (Syn.shift (succ (d + e))) :: Γ.map Fm.shift ⊢[PRAAx]
        le (var 0) (Syn.shift d + Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans
      (by simpa only [Syn.shift, PTm.subst_add, ConciseIPRA.PTm.subst_succ, lt, le] using
        (Prf.hyp0 : lt (var 0) (Syn.shift (succ (d + e))) :: Γ.map Fm.shift ⊢[PRAAx] _))
    simpa only [Syn.shift, subst_difference, subst_expansion] using
      coefficient_identity (Syn.shift P) (Syn.shift Q) (Syn.shift A) (Syn.shift B) (Syn.shift d) (Syn.shift e)
        (var 0) hs.wk range
  have eq := norm_entries _ _ _ (sub_length _ _ _) (added_length _ _ _) entries
  have triangle := norm_added (Γ := Γ) (leftTerm P Q A d e) (rightTerm Q A B d e) (succ (d + e))
    (product_length _ _ _ _) (product_length _ _ _ _)
  exact RationalArgmin.transitive (rationalLE_congr eq.eqSymm (.eqRefl _) triangle)
    (add_monotone _ _ _ _ (product_norm _ _ _ _ (sub_length _ _ _) (.andE₁ (.andE₂ h)))
      (product_norm _ _ _ _ (.andE₁ (.andE₂ (.andE₂ h))) (sub_length _ _ _)))

theorem actual_convolution_error_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      rationalLE (coefficientNorm (difference (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
        (add (multiply (coefficientNorm (subCoefficients (var 0) (var 2) (succ (var 4)))) (coefficientNorm (var 1)))
          (multiply (coefficientNorm (var 2)) (coefficientNorm (subCoefficients (var 1) (var 3) (succ (var 5))))))) :=
  closeUniv 6 (.impI (error_norm_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialConvolutionDifference
