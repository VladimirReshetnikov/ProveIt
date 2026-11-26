import IPRADerivations.Analysis.Polynomials.Elimination.GaussianBivariateMonicFactor
import IPRADerivations.Analysis.Polynomials.Elimination.GaussianBivariatePolynomialBuffers
import IPRADerivations.Analysis.Polynomials.Elimination.GaussianBivariatePolynomialProduct
import IPRADerivations.Analysis.Polynomials.Elimination.GaussianBivariateGridCoefficients
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialMonicHornerQuotient

/-!
# The literal stored coefficient identity for monic division

Pad the original input and the actual remainder to the bounds of the
actual convolution of the quotient and full monic factor. The previous
reconstruction identity supplies equality at numerical queries. The
rectangular grid proof then yields equality of the stored coefficients.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBivariateMonicDivisionIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBivariateMonicFactor (table table_shape table_evaluation)
open GaussianBivariatePolynomialBuffers (pad pad_stored pad_evaluation add_stored add_evaluation)
open GaussianBivariatePolynomialProduct (product product_stored product_evaluation)
open GaussianBivariateGridCoefficients (rectangleEqual specializationGrid canonical_coefficient)
open GaussianPolynomialMonicHornerReduction (width stage stage_shape)
open GaussianPolynomialMonicHornerQuotient (quotient quotient_stored qvalue rvalue original_reconstruction)
open GaussianPolynomialMultiplicationMatrix (stored stored_congr)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at values values_congr evaluation_congr)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianRationalGridCoefficientEquality (gridEqual)
open GaussianRationalHorner (canonical evaluate qadd qmul)
open GaussianRationalSyntheticDivision
  (canonicalCoefficients subst_canonicalCoefficients canonical_coefficient_at qadd_congr qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def xBound (H a c : PTm n) : PTm n := c + width a c (length H)
def yBound (H m : PTm n) : PTm n := m + length H

def original (H m a c : PTm n) : PTm n :=
  pad H (length H) a (length H * c + c) (succ m)

def factorProduct (F H m a c : PTm n) : PTm n :=
  product (table F m c) (quotient F H m a c (length H)) m (length H) c (width a c (length H))

def remainder (F H m a c : PTm n) : PTm n :=
  pad (stage F H m a c (length H)) m (width a c (length H)) c (succ (length H))

def reconstructed (F H m a c : PTm n) : PTm n :=
  GaussianBivariatePolynomialBuffers.add (factorProduct F H m a c) (remainder F H m a c)
    (succ (yBound H m)) (xBound H a c)

@[simp] theorem subst_xBound {k : ℕ} (σ : Fin n → PTm k) (H a c : PTm n) :
    Syn.subst σ (xBound H a c) = xBound (Syn.subst σ H) (Syn.subst σ a) (Syn.subst σ c) := by simp [xBound]
@[simp] theorem subst_yBound {k : ℕ} (σ : Fin n → PTm k) (H m : PTm n) :
    Syn.subst σ (yBound H m) = yBound (Syn.subst σ H) (Syn.subst σ m) := by simp [yBound]
@[simp] theorem subst_original {k : ℕ} (σ : Fin n → PTm k) (H m a c : PTm n) :
    Syn.subst σ (original H m a c) = original (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [original]
@[simp] theorem subst_factorProduct {k : ℕ} (σ : Fin n → PTm k) (F H m a c : PTm n) :
    Syn.subst σ (factorProduct F H m a c) =
      factorProduct (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [factorProduct]
@[simp] theorem subst_remainder {k : ℕ} (σ : Fin n → PTm k) (F H m a c : PTm n) :
    Syn.subst σ (remainder F H m a c) =
      remainder (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [remainder]
@[simp] theorem subst_reconstructed {k : ℕ} (σ : Fin n → PTm k) (F H m a c : PTm n) :
    Syn.subst σ (reconstructed F H m a c) =
      reconstructed (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [reconstructed]

theorem original_stored (H m a c : PTm n) (hH : Γ ⊢[PRAAx] rowShape H (length H) a) :
    Γ ⊢[PRAAx] stored (original H m a c) (succ (yBound H m)) (xBound H a c) :=
  stored_congr (.eqRefl _) (by unfold yBound; ipra_ring) (by unfold xBound width; ipra_ring)
    (pad_stored H (length H) a (length H * c + c) (succ m) hH)

theorem factor_product_stored (F H m a c : PTm n) :
    Γ ⊢[PRAAx] stored (factorProduct F H m a c) (succ (yBound H m)) (xBound H a c) :=
  product_stored _ _ _ _ _ _

theorem remainder_stored (F H m a c : PTm n) :
    Γ ⊢[PRAAx] stored (remainder F H m a c) (succ (yBound H m)) (xBound H a c) :=
  stored_congr (.eqRefl _) (by unfold yBound; ipra_ring) (add_comm _ _)
    (pad_stored _ _ _ _ _ (stage_shape F H m a c (length H)))

theorem reconstructed_stored (F H m a c : PTm n) :
    Γ ⊢[PRAAx] stored (reconstructed F H m a c) (succ (yBound H m)) (xBound H a c) :=
  add_stored _ _ _ _

theorem original_evaluation (H m a c x y : PTm n) :
    Γ ⊢[PRAAx] evaluate (values (original H m a c) (succ (yBound H m)) x) y ≐
      evaluate (values H (length H) x) y :=
  (evaluation_congr (values_congr (.eqRefl _) (by unfold yBound; ipra_ring) (.eqRefl _)) (.eqRefl _)).eqTrans
    (pad_evaluation _ _ _ _ _ _ _)

theorem remainder_evaluation (F H m a c x y : PTm n) :
    Γ ⊢[PRAAx] evaluate (values (remainder F H m a c) (succ (yBound H m)) x) y ≐
      rvalue F H m a c (length H) x y :=
  (evaluation_congr (values_congr (.eqRefl _) (by unfold yBound; ipra_ring) (.eqRefl _)) (.eqRefl _)).eqTrans
    (pad_evaluation _ _ _ _ _ _ _)

theorem reconstructed_evaluation (F H m a c x y : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c) :
    Γ ⊢[PRAAx] evaluate (values (reconstructed F H m a c) (succ (yBound H m)) x) y ≐
      qadd (qmul (evaluate (GaussianPolynomialMonicCompanion.monicValues F m x) y)
        (qvalue F H m a c (length H) x y)) (rvalue F H m a c (length H) x y) := by
  have mulEval := product_evaluation (table F m c) (quotient F H m a c (length H)) m (length H) c
      (width a c (length H)) x y (table_shape F m c hF)
      (.andE₁ (.andE₂ (quotient_stored F H m a c (length H))))
  exact (add_evaluation _ _ _ _ x y (.andE₁ (.andE₂ (factor_product_stored F H m a c)))
    (.andE₁ (.andE₂ (remainder_stored F H m a c)))).eqTrans
      (qadd_congr (mulEval.eqTrans (qmul_congr (table_evaluation F m c x y) (.eqRefl _)))
        (remainder_evaluation F H m a c x y))

theorem equality_at (F H m a c x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H (length H) a) :
    Γ ⊢[PRAAx] evaluate (values (original H m a c) (succ (yBound H m)) x) y ≐
      evaluate (values (reconstructed F H m a c) (succ (yBound H m)) x) y :=
  (original_evaluation H m a c x y).eqTrans ((original_reconstruction F H m a c x y hm hF hH).eqTrans
    (reconstructed_evaluation F H m a c x y hF).eqSymm)

theorem specialized_grid (F H m a c x : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H (length H) a) :
    Γ ⊢[PRAAx] specializationGrid (original H m a c) (reconstructed F H m a c) (yBound H m) x := by
  have hms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift, Syn.shift] using hm.shift
  have hFs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
    simpa [Fm.shift, Syn.shift] using hF.shift
  have hHs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (length (Syn.shift H)) (Syn.shift a) := by
    simpa [Fm.shift, Syn.shift] using hH.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_original, subst_reconstructed, subst_yBound,
    GaussianPolynomialMonicCompanion.subst_values, ConciseIPRA.PTm.subst_succ] using
    equality_at (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift x)
      (gridPoint (var 0)) hms.wk hFs.wk hHs.wk

theorem rectangle (F H m a c : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H (length H) a) :
    Γ ⊢[PRAAx] rectangleEqual (original H m a c) (reconstructed F H m a c) (xBound H a c) (yBound H m) := by
  have hms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift, Syn.shift] using hm.shift
  have hFs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
    simpa [Fm.shift, Syn.shift] using hF.shift
  have hHs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (length (Syn.shift H)) (Syn.shift a) := by
    simpa [Fm.shift, Syn.shift] using hH.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_original, subst_reconstructed, subst_yBound] using
    specialized_grid (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (gridPoint (var 0))
      hms.wk hFs.wk hHs.wk

theorem stored_coefficient_at (A m a r s : PTm n) (h : Γ ⊢[PRAAx] stored A m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s a) :
    Γ ⊢[PRAAx] canonical (entry (entry A r) s) := by
  have rowRule : Γ ⊢[PRAAx] lt r m ⟶ canonicalCoefficients (entry A r) := by
    simpa only [Fm.subst_imp, subst_lt, subst_canonicalCoefficients, subst_entry,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using (Prf.andE₂ (Prf.andE₂ h)).allE r
  have size := row_shape_at A m a r (.andE₁ (.andE₂ h)) hr
  exact canonical_coefficient_at _ _ (.impE rowRule hr)
    (lt_congr (.eqRefl _) size.eqSymm ((succ_monus_succ _ _).eqTrans hs))

theorem coefficient_identity (F H m a c r s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H (length H) a)
    (hr : Γ ⊢[PRAAx] le r (yBound H m)) (hs : Γ ⊢[PRAAx] le s (xBound H a c)) :
    Γ ⊢[PRAAx] entry (entry (original H m a c) r) s ≐ entry (entry (reconstructed F H m a c) r) s := by
  have leftStored := original_stored H m a c hH
  have rightStored := reconstructed_stored (Γ := Γ) F H m a c
  have hi := (succ_monus_succ _ _).eqTrans hr
  exact canonical_coefficient _ _ _ _ r s (.andE₁ (.andE₂ leftStored)) (.andE₁ (.andE₂ rightStored))
    (rectangle F H m a c hm hF hH) hr hs
    (stored_coefficient_at _ _ _ r s leftStored hi hs) (stored_coefficient_at _ _ _ r s rightStored hi hs)

theorem actual_bivariate_monic_division_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (length (var 1)) (var 3) ⟶
      le (var 5) (yBound (var 1) (var 2)) ⟶ le (var 6) (xBound (var 1) (var 3) (var 4)) ⟶
      entry (entry (original (var 1) (var 2) (var 3) (var 4)) (var 5)) (var 6) ≐
        entry (entry (reconstructed (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (coefficient_identity _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianBivariateMonicDivisionIdentity
