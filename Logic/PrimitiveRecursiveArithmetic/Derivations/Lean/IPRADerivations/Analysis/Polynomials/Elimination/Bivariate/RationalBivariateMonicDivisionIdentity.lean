import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.RationalBivariateMonicFactorGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.RationalBivariatePolynomialProductGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Horner.MonicDivision.RationalPolynomialMonicHornerQuotientGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.RationalBivariateGridCoefficients

/-!
# The actual stored original rational monic-division identity

The original input, genuine monic-factor/quotient product and SAME actual
remainder are padded and added as original rational polynomial buffers.
Every-query reconstruction and a finite rectangular grid derive their
stored coefficient identity from only original monic-division input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalBivariateMonicDivisionIdentity

open_ipra
open RationalPolynomialMonicHornerReductionGaussianEmbedding
  (width input remainder remainder_length remainder_computed_shape row_shape_congr)
open RationalPolynomialMonicHornerQuotientGaussianEmbedding (finalQuotient quotient_length quotient_computed_shape reconstruction)
open RationalBivariatePolynomialBuffersGaussianEmbedding (pad pad_shape add_shape)
open RationalBivariatePolynomialProductGaussianEmbedding (product product_shape bivariate_congr)
open RationalBivariateMonicFactorGaussianEmbedding (table table_shape)
open RationalPolynomialGaussianEmbedding (embed_congr)
open GaussianPolynomialMonicCompanion (rowShape)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def xBound (a c N : PTm n) : PTm n := c+width a c (succ N)
def yBound (m N : PTm n) : PTm n := m+succ N
def original (H m a c N : PTm n) : PTm n := pad H (succ N) a (succ N*c+c) (succ m)
def factorProduct (F H m a c N : PTm n) : PTm n := product (table F m c) (finalQuotient F H m a c N) m (succ N) c (width a c (succ N))
def paddedRemainder (F H m a c N : PTm n) : PTm n := pad (remainder F H m a c N) m (width a c (succ N)) c (succ (succ N))
def reconstructed (F H m a c N : PTm n) : PTm n := RationalBivariatePolynomialBuffersGaussianEmbedding.add
  (factorProduct F H m a c N) (paddedRemainder F H m a c N) (succ (yBound m N)) (xBound a c N)

ipra_subst xBound
ipra_subst yBound
ipra_subst original
ipra_subst factorProduct
ipra_subst paddedRemainder
ipra_subst reconstructed

theorem original_shape (H m a c N : PTm n) (hH : Γ ⊢[PRAAx] rowShape H (succ N) a) : Γ ⊢[PRAAx]
    rowShape (original H m a c N) (succ (yBound m N)) (xBound a c N) :=
  row_shape_congr (.eqRefl _) (by unfold yBound; ipra_ring) (by unfold xBound width; ipra_ring) (pad_shape _ _ _ _ _ hH)
theorem factor_product_shape (F H m a c N : PTm n) : Γ ⊢[PRAAx]
    rowShape (factorProduct F H m a c N) (succ (yBound m N)) (xBound a c N) := product_shape _ _ _ _ _ _
theorem padded_remainder_shape (F H m a c N : PTm n) : Γ ⊢[PRAAx]
    rowShape (paddedRemainder F H m a c N) (succ (yBound m N)) (xBound a c N) :=
  row_shape_congr (.eqRefl _) (by unfold yBound; ipra_ring) (add_comm _ _)
    (pad_shape _ _ _ _ _ (remainder_computed_shape _ _ _ _ _ _))
theorem reconstructed_shape (F H m a c N : PTm n) : Γ ⊢[PRAAx]
    rowShape (reconstructed F H m a c N) (succ (yBound m N)) (xBound a c N) := add_shape _ _ _ _

theorem original_evaluation (H m a c N x y : PTm n) (hH : Γ ⊢[PRAAx] rowShape H (succ N) a) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (original H m a c N) (succ (yBound m N)) x y ≐
      RationalBivariateGaussianEmbedding.bivariate H (succ N) x y :=
  (bivariate_congr (.eqRefl _) (by unfold yBound; ipra_ring) (.eqRefl _) (.eqRefl _)).eqTrans
    (RationalBivariatePolynomialBuffersGaussianEmbedding.pad_evaluation _ _ _ _ _ _ _ hH)
theorem padded_remainder_evaluation (F H m a c N x y : PTm n) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (paddedRemainder F H m a c N) (succ (yBound m N)) x y ≐
      RationalBivariateGaussianEmbedding.bivariate (remainder F H m a c N) m x y :=
  (bivariate_congr (.eqRefl _) (by unfold yBound; ipra_ring) (.eqRefl _) (.eqRefl _)).eqTrans
    (RationalBivariatePolynomialBuffersGaussianEmbedding.pad_evaluation _ _ _ _ _ _ _ (remainder_computed_shape _ _ _ _ _ _))
theorem factor_product_evaluation (F H m a c N x y : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (factorProduct F H m a c N) (succ (yBound m N)) x y ≐
      RationalArithmetic.multiply (RationalBivariateGaussianEmbedding.monic F m x y)
        (RationalBivariateGaussianEmbedding.bivariate (finalQuotient F H m a c N) (succ (succ N)) x y) :=
  (RationalBivariatePolynomialProductGaussianEmbedding.product_evaluation _ _ _ _ _ _ _ _
    (table_shape _ _ _ hF) (quotient_computed_shape _ _ _ _ _ _)).eqTrans
      (RationalAlgebra.multiply_congr (RationalBivariateMonicFactorGaussianEmbedding.table_evaluation _ _ _ _ _ hF) (.eqRefl _))
theorem reconstructed_evaluation (F H m a c N x y : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (reconstructed F H m a c N) (succ (yBound m N)) x y ≐ RationalArithmetic.add
      (RationalArithmetic.multiply (RationalBivariateGaussianEmbedding.monic F m x y)
        (RationalBivariateGaussianEmbedding.bivariate (finalQuotient F H m a c N) (succ (succ N)) x y))
      (RationalBivariateGaussianEmbedding.bivariate (remainder F H m a c N) m x y) :=
  (RationalBivariatePolynomialBuffersGaussianEmbedding.add_evaluation _ _ _ _ _ _ (factor_product_shape _ _ _ _ _ _) (padded_remainder_shape _ _ _ _ _ _)).eqTrans
    (RationalAlgebra.add_congr (factor_product_evaluation _ _ _ _ _ _ _ _ hF) (padded_remainder_evaluation _ _ _ _ _ _ _ _))

theorem equality_at (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (original H m a c N) (succ (yBound m N)) x y ≐
      RationalBivariateGaussianEmbedding.bivariate (reconstructed F H m a c N) (succ (yBound m N)) x y :=
  (original_evaluation _ _ _ _ _ _ _ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h))))).eqTrans
    ((reconstruction _ _ _ _ _ _ _ _ h).eqTrans (reconstructed_evaluation _ _ _ _ _ _ _ _ (.andE₁ (.andE₂ (.andE₂ h)))).eqSymm)

theorem original_coefficient_well_formed (H m a c N r s : PTm n) (hH : Γ ⊢[PRAAx] rowShape H (succ N) a)
    (hr : Γ ⊢[PRAAx] le r (yBound m N)) (hs : Γ ⊢[PRAAx] le s (xBound a c N)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (entry (original H m a c N) r) s) :=
  RationalBivariatePolynomialBuffersGaussianEmbedding.pad_coefficient_well_formed _ _ _ _ _ _ _ hH
    (lt_congr (.eqRefl _) (by unfold yBound; ipra_ring) ((succ_monus_succ _ _).eqTrans hr))
    (le_congr (.eqRefl _) (by unfold xBound width; ipra_ring) hs)
theorem reconstructed_coefficient_well_formed (F H m a c N r s : PTm n)
    (hr : Γ ⊢[PRAAx] le r (yBound m N)) (hs : Γ ⊢[PRAAx] le s (xBound a c N)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (entry (reconstructed F H m a c N) r) s) :=
  RationalBivariatePolynomialBuffersGaussianEmbedding.add_coefficient_well_formed _ _ _ _ _ _ ((succ_monus_succ _ _).eqTrans hr) hs


theorem rectangle (F H m a c N : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N) : Γ ⊢[PRAAx]
    RationalBivariateGridCoefficients.rectangleEqual (original H m a c N) (reconstructed F H m a c N) (xBound a c N) (yBound m N) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let F' := Syn.shift (Syn.shift F)
  let H' := Syn.shift (Syn.shift H)
  let m' := Syn.shift (Syn.shift m)
  let a' := Syn.shift (Syn.shift a)
  let c' := Syn.shift (Syn.shift c)
  let N' := Syn.shift (Syn.shift N)
  let Δ := le (var 0) (yBound m' N') :: le (var 1) (xBound a' c' N') :: (Γ.map Fm.shift).map Fm.shift
  have source : Δ ⊢[PRAAx] input F' H' m' a' c' N' := by
    simpa [Δ,F',H',m',a',c',N',Fm.shift,Syn.shift] using h.shift.shift.wk.wk
  have actual := RationalGaussianEmbedding.rational_equal_of_embed _ _
    (embed_congr (equality_at F' H' m' a' c' N' (RationalBivariateGridCoefficients.gridPoint (var 1))
      (RationalBivariateGridCoefficients.gridPoint (var 0)) source))
  simpa only [Δ,F',H',m',a',c',N',List.map_cons,Fm.shift,subst_le,Syn.shift,subst_xBound,subst_yBound,
    subst_original,subst_reconstructed,RationalBivariateGridCoefficients.observation,
    Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one] using actual

theorem coefficient_identity (F H m a c N r s : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hr : Γ ⊢[PRAAx] le r (yBound m N)) (hs : Γ ⊢[PRAAx] le s (xBound a c N)) : Γ ⊢[PRAAx]
    entry (entry (original H m a c N) r) s ≐ entry (entry (reconstructed F H m a c N) r) s := by
  have hH := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact RationalBivariateGridCoefficients.canonical_coefficient _ _ _ _ _ _
    (original_shape _ _ _ _ _ hH) (reconstructed_shape _ _ _ _ _ _) (rectangle _ _ _ _ _ _ h) hr hs
    (original_coefficient_well_formed _ _ _ _ _ _ _ hH hr hs) (reconstructed_coefficient_well_formed _ _ _ _ _ _ _ _ hr hs)

theorem coefficient_field_identity (F H m a c N r s : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hr : Γ ⊢[PRAAx] le r (yBound m N)) (hs : Γ ⊢[PRAAx] le s (xBound a c N)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalEq (entry (entry (original H m a c N) r) s) (entry (entry (reconstructed F H m a c N) r) s) :=
  RationalGaussianEmbedding.rational_equal_of_embed _ _ (embed_congr (coefficient_identity _ _ _ _ _ _ _ _ h hr hs))

theorem literal_coefficients (F H m a c N : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N) : Γ ⊢[PRAAx]
    RationalBivariateGridCoefficients.literalCoefficientsEqual (original H m a c N) (reconstructed F H m a c N) (xBound a c N) (yBound m N) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let F' := Syn.shift (Syn.shift F)
  let H' := Syn.shift (Syn.shift H)
  let m' := Syn.shift (Syn.shift m)
  let a' := Syn.shift (Syn.shift a)
  let c' := Syn.shift (Syn.shift c)
  let N' := Syn.shift (Syn.shift N)
  let Δ := le (var 0) (xBound a' c' N') :: le (var 1) (yBound m' N') :: (Γ.map Fm.shift).map Fm.shift
  have source : Δ ⊢[PRAAx] input F' H' m' a' c' N' := by simpa [Δ,F',H',m',a',c',N',Fm.shift,Syn.shift] using h.shift.shift.wk.wk
  simpa only [Δ,F',H',m',a',c',N',List.map_cons,Fm.shift,subst_le,Syn.shift,subst_xBound,subst_yBound,
    subst_original,subst_reconstructed,Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one] using
    coefficient_identity F' H' m' a' c' N' (var 1) (var 0) source Prf.hyp1 Prf.hyp0


theorem original_length (H m a c N : PTm n) : Γ ⊢[PRAAx] length (original H m a c N) ≐ succ (yBound m N) :=
  (RationalBivariatePolynomialBuffersGaussianEmbedding.pad_length _ _ _ _ _).eqTrans (by unfold yBound; ipra_ring)
theorem reconstructed_length (F H m a c N : PTm n) : Γ ⊢[PRAAx] length (reconstructed F H m a c N) ≐ succ (yBound m N) :=
  RationalBivariatePolynomialBuffersGaussianEmbedding.add_length _ _ _ _

def output (F H m a c N : PTm n) : PTm n := pairT (original H m a c N)
  (pairT (reconstructed F H m a c N) (pairT (finalQuotient F H m a c N) (remainder F H m a c N)))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (F H m a c N : PTm n) : PTm n := PTm.app outputF ![F,H,m,a,c,N]
ipra_subst output
ipra_subst run
theorem program_at (F H m a c N : PTm n) : Γ ⊢[PRAAx] run F H m a c N ≐ output F H m a c N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,H,m,a,c,N]
theorem returned_original (F H m a c N : PTm n) : Γ ⊢[PRAAx] fstT (run F H m a c N) ≐ original H m a c N :=
  (program_at _ _ _ _ _ _).fstE
theorem returned_reconstructed (F H m a c N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run F H m a c N)) ≐ reconstructed F H m a c N :=
  (program_at _ _ _ _ _ _).sndE.fstE
theorem returned_quotient (F H m a c N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run F H m a c N))) ≐ finalQuotient F H m a c N :=
  (program_at _ _ _ _ _ _).sndE.sndE.fstE
theorem returned_remainder (F H m a c N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run F H m a c N))) ≐ remainder F H m a c N :=
  (program_at _ _ _ _ _ _).sndE.sndE.sndE

theorem returned_coefficient_identity (F H m a c N r s : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hr : Γ ⊢[PRAAx] le r (yBound m N)) (hs : Γ ⊢[PRAAx] le s (xBound a c N)) : Γ ⊢[PRAAx]
    entry (entry (fstT (run F H m a c N)) r) s ≐ entry (entry (fstT (sndT (run F H m a c N))) r) s :=
  (Foundations.SequenceComposition.entry_congr (Foundations.SequenceComposition.entry_congr (returned_original _ _ _ _ _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((coefficient_identity _ _ _ _ _ _ _ _ h hr hs).eqTrans
      (Foundations.SequenceComposition.entry_congr (Foundations.SequenceComposition.entry_congr (returned_reconstructed _ _ _ _ _ _) (.eqRefl _)) (.eqRefl _)).eqSymm)

theorem actual_original_rational_division_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      (length (original (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ succ (yBound (var 2) (var 5)) ⋏
        (rowShape (original (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (yBound (var 2) (var 5))) (xBound (var 3) (var 4) (var 5)) ⋏
          (length (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ succ (yBound (var 2) (var 5)) ⋏
            rowShape (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (yBound (var 2) (var 5))) (xBound (var 3) (var 4) (var 5)))))) :=
  closeUniv 6 (.impI (.andI (original_length _ _ _ _ _) (.andI
    (original_shape _ _ _ _ _ (.andE₂ (.andE₂ (.andE₂ (.andE₂ Prf.hyp0)))))
    (.andI (reconstructed_length _ _ _ _ _ _) (reconstructed_shape _ _ _ _ _ _)))))
theorem actual_original_rational_division_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalBivariateGaussianEmbedding.bivariate (original (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (yBound (var 2) (var 5))) (var 6) (var 7) ≐
        RationalBivariateGaussianEmbedding.bivariate (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (yBound (var 2) (var 5))) (var 6) (var 7)) :=
  closeUniv 8 (.impI (equality_at _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_rational_division_rectangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalBivariateGridCoefficients.rectangleEqual (original (var 1) (var 2) (var 3) (var 4) (var 5))
        (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (xBound (var 3) (var 4) (var 5)) (yBound (var 2) (var 5))) :=
  closeUniv 6 (.impI (rectangle _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_rational_division_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (var 6) (yBound (var 2) (var 5)) ⟶ le (var 7) (xBound (var 3) (var 4) (var 5)) ⟶
      entry (entry (original (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7) ≐
        entry (entry (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (coefficient_identity _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_original_rational_division_field_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (var 6) (yBound (var 2) (var 5)) ⟶ le (var 7) (xBound (var 3) (var 4) (var 5)) ⟶
      RationalArgmin.rationalEq (entry (entry (original (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7))
        (entry (entry (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (coefficient_field_identity _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_original_rational_division_all_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalBivariateGridCoefficients.literalCoefficientsEqual (original (var 1) (var 2) (var 3) (var 4) (var 5))
        (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (xBound (var 3) (var 4) (var 5)) (yBound (var 2) (var 5))) :=
  closeUniv 6 (.impI (literal_coefficients _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_rational_division_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_original_rational_division_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ original (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ reconstructed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ finalQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
          sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (.andI (returned_original _ _ _ _ _ _) (.andI (returned_reconstructed _ _ _ _ _ _)
    (.andI (returned_quotient _ _ _ _ _ _) (returned_remainder _ _ _ _ _ _))))
theorem actual_returned_original_rational_division_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (var 6) (yBound (var 2) (var 5)) ⟶ le (var 7) (xBound (var 3) (var 4) (var 5)) ⟶
      entry (entry (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) (var 6)) (var 7) ≐
        entry (entry (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (returned_coefficient_identity _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalBivariateMonicDivisionIdentity
