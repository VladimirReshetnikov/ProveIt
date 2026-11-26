import IPRADerivations.Analysis.Polynomials.Elimination.RationalBivariateGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Elimination.GaussianBivariateGridCoefficients

/-!
# Original rational coefficient reflection from the actual rectangular grid

Two original rational tables of b+1 polynomial rows and width a+1 agree
by FIELD value on the actual natural grid 0..a times 0..b. Their original
bounded coefficients then agree by FIELD value. Canonical individual
coefficients give literal code equality. All rectangles, tables, indices and
query data are numerical, including a=b=0. No all-point identity, coefficient
law, Gaussian-grid premise or raw outer-code extensionality is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalBivariateGridCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed)
open RationalArgmin (rationalEq)
open RationalBivariateGaussianEmbedding (bivariate embedded_row_shape bivariate_conjugacy)
open RationalRowSpanGaussianEmbedding (matrix matrix_lookup)
open GaussianPolynomialMonicCompanion (rowShape values)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gridPoint (i : PTm n) : PTm n := RationalIntegerNormalization.normalize (ZT.ofNat i) one
def observation (A b i j : PTm n) : PTm n := bivariate A (succ b) (gridPoint i) (gridPoint j)

def rectangleEqual (A B a b : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift a) ⟶ .all (le (var 0) (Syn.shift (Syn.shift b)) ⟶
    rationalEq (observation (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift b)) (var 1) (var 0))
      (observation (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift b)) (var 1) (var 0))))

def coefficientsEqual (A B a b : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift b) ⟶ .all (le (var 0) (Syn.shift (Syn.shift a)) ⟶
    rationalEq (entry (entry (Syn.shift (Syn.shift A)) (var 1)) (var 0))
      (entry (entry (Syn.shift (Syn.shift B)) (var 1)) (var 0))))

def literalCoefficientsEqual (A B a b : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift b) ⟶ .all (le (var 0) (Syn.shift (Syn.shift a)) ⟶
    entry (entry (Syn.shift (Syn.shift A)) (var 1)) (var 0) ≐
      entry (entry (Syn.shift (Syn.shift B)) (var 1)) (var 0)))

@[simp] theorem subst_gridPoint {l : ℕ} (σ : Fin n → PTm l) (i : PTm n) :
    Syn.subst σ (gridPoint i) = gridPoint (Syn.subst σ i) := by simp [gridPoint]
@[simp] theorem subst_observation {l : ℕ} (σ : Fin n → PTm l) (A b i j : PTm n) :
    Syn.subst σ (observation A b i j) = observation (Syn.subst σ A) (Syn.subst σ b) (Syn.subst σ i) (Syn.subst σ j) := by simp [observation]
@[simp] theorem subst_rectangleEqual {l : ℕ} (σ : Fin n → PTm l) (A B a b : PTm n) :
    (rectangleEqual A B a b).subst σ = rectangleEqual (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [rectangleEqual,Fm.subst_all,Fm.subst_imp,subst_le,RationalArgmin.subst_rationalEq,subst_observation,
    Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Syn.subst_shift,Syn.shift_subst,Syn.shift_var,Fin.succ_zero_eq_one]
@[simp] theorem subst_coefficientsEqual {l : ℕ} (σ : Fin n → PTm l) (A B a b : PTm n) :
    (coefficientsEqual A B a b).subst σ = coefficientsEqual (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [coefficientsEqual,Fm.subst_all,Fm.subst_imp,subst_le,RationalArgmin.subst_rationalEq,
    Foundations.MasterCertificate.subst_entry,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst,Syn.shift_var,Fin.succ_zero_eq_one]
@[simp] theorem subst_literalCoefficientsEqual {l : ℕ} (σ : Fin n → PTm l) (A B a b : PTm n) :
    (literalCoefficientsEqual A B a b).subst σ = literalCoefficientsEqual (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [literalCoefficientsEqual,Fm.subst_all,Fm.subst_imp,subst_le,Fm.subst_eq,
    Foundations.MasterCertificate.subst_entry,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst,Syn.shift_var,Fin.succ_zero_eq_one]

theorem grid_point_canonical (i : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (gridPoint i) :=
  RationalNormalForm.normalize_well_formed _ _ (le_refl one)

theorem grid_point_embedding (i : PTm n) : Γ ⊢[PRAAx]
    embed (gridPoint i) ≐ GaussianRationalFiniteGridIdentity.gridPoint i :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (RationalGaussianEmbedding.embed_canonical _)
    (GaussianRationalFiniteGridIdentity.point_canonical i) (le_refl one)
    (RationalGaussianEmbedding.embed_from_representation _ _ _
      (RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)))
    (GaussianRationalFiniteGridIdentity.point_represents i)

theorem rectangle_at (A B a b i j : PTm n) (h : Γ ⊢[PRAAx] rectangleEqual A B a b)
    (hi : Γ ⊢[PRAAx] le i a) (hj : Γ ⊢[PRAAx] le j b) : Γ ⊢[PRAAx]
    rationalEq (observation A b i j) (observation B b i j) := by
  have first : Γ ⊢[PRAAx] le i a ⟶ .all (le (var 0) (Syn.shift b) ⟶
      rationalEq (observation (Syn.shift A) (Syn.shift b) (Syn.shift i) (var 0))
        (observation (Syn.shift B) (Syn.shift b) (Syn.shift i) (var 0))) := by
    simpa only [rectangleEqual,Fm.subst_imp,Fm.subst_all,subst_le,RationalArgmin.subst_rationalEq,subst_observation,
      Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,AnalyticNumberTheory.Fermat.subst_up_shift',
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE i
  have last : Γ ⊢[PRAAx] le j b ⟶ rationalEq (observation A b i j) (observation B b i j) := by
    simpa [Syn.subst_inst_shift] using (Prf.impE first hi).allE j
  exact .impE last hj

theorem observation_embedding (A a b i j : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a) : Γ ⊢[PRAAx]
    embed (observation A b i j) ≐ GaussianRationalHorner.evaluate
      (values (matrix A (succ b) (succ a)) (succ b) (GaussianRationalFiniteGridIdentity.gridPoint i))
      (GaussianRationalFiniteGridIdentity.gridPoint j) :=
  (bivariate_conjugacy A (succ b) a (gridPoint i) (gridPoint j) hA).eqTrans
    (GaussianRationalMonicReduction.evaluate_congr
      (GaussianPolynomialMonicCompanion.values_congr (.eqRefl _) (.eqRefl _) (grid_point_embedding i))
      (grid_point_embedding j))

theorem gaussian_rectangle (A B a b : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual A B a b) : Γ ⊢[PRAAx]
    GaussianBivariateGridCoefficients.rectangleEqual (matrix A (succ b) (succ a)) (matrix B (succ b) (succ a)) a b := by
  refine .allI (.impI (.allI (.impI ?_)))
  let A' := Syn.shift (Syn.shift A)
  let B' := Syn.shift (Syn.shift B)
  let a' := Syn.shift (Syn.shift a)
  let b' := Syn.shift (Syn.shift b)
  let Δ := le (var 0) b' :: le (var 1) a' :: (Γ.map Fm.shift).map Fm.shift
  have shapeA : Δ ⊢[PRAAx] rowShape A' (succ b') a' := by simpa [Δ,A',a',b',Fm.shift,Syn.shift] using hA.shift.shift.wk.wk
  have shapeB : Δ ⊢[PRAAx] rowShape B' (succ b') a' := by simpa [Δ,B',a',b',Fm.shift,Syn.shift] using hB.shift.shift.wk.wk
  have rect : Δ ⊢[PRAAx] rectangleEqual A' B' a' b' := by simpa [Δ,A',B',a',b',List.map_cons,Fm.shift,Syn.shift] using h.shift.shift.wk.wk
  have actual := RationalGaussianEmbedding.embed_equal _ _ (rectangle_at A' B' a' b' (var 1) (var 0) rect Prf.hyp1 Prf.hyp0)
  have eq := (observation_embedding (Γ := Δ) A' a' b' (var 1) (var 0) shapeA).eqSymm.eqTrans
    (actual.eqTrans (observation_embedding B' a' b' (var 1) (var 0) shapeB))
  simpa only [Δ,A',B',a',b',List.map_cons,Fm.shift,subst_le,Syn.shift,RationalRowSpanGaussianEmbedding.subst_matrix,
    GaussianPolynomialMonicCompanion.subst_values,GaussianRationalFiniteGridIdentity.subst_gridPoint,
    Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one,ConciseIPRA.PTm.subst_succ] using eq

theorem coefficient_embedding_equal (A B a b r s : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual A B a b)
    (hr : Γ ⊢[PRAAx] le r b) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    embed (entry (entry A r) s) ≐ embed (entry (entry B r) s) := by
  have ri : Γ ⊢[PRAAx] lt r (succ b) := (succ_monus_succ _ _).eqTrans hr
  have si : Γ ⊢[PRAAx] lt s (succ a) := (succ_monus_succ _ _).eqTrans hs
  have ea := matrix_lookup (Γ := Γ) A (succ b) (succ a) r s ri si
  have eb := matrix_lookup (Γ := Γ) B (succ b) (succ a) r s ri si
  have ca : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (entry (entry (matrix A (succ b) (succ a)) r) s) :=
    GaussianRationalHorner.canonical_congr ea (RationalGaussianEmbedding.embed_canonical _)
  have cb : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (entry (entry (matrix B (succ b) (succ a)) r) s) :=
    GaussianRationalHorner.canonical_congr eb (RationalGaussianEmbedding.embed_canonical _)
  have eq := GaussianBivariateGridCoefficients.canonical_coefficient _ _ a b r s
    (embedded_row_shape A (succ b) a) (embedded_row_shape B (succ b) a) (gaussian_rectangle A B a b hA hB h) hr hs ca cb
  exact ea.eqSymm.eqTrans (eq.eqTrans eb)

theorem coefficient_equal (A B a b r s : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual A B a b)
    (hr : Γ ⊢[PRAAx] le r b) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    rationalEq (entry (entry A r) s) (entry (entry B r) s) :=
  RationalGaussianEmbedding.rational_equal_of_embed _ _ (coefficient_embedding_equal A B a b r s hA hB h hr hs)

theorem canonical_coefficient (A B a b r s : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual A B a b)
    (hr : Γ ⊢[PRAAx] le r b) (hs : Γ ⊢[PRAAx] le s a)
    (hcA : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry (entry A r) s))
    (hcB : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry (entry B r) s)) : Γ ⊢[PRAAx]
    entry (entry A r) s ≐ entry (entry B r) s :=
  RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _ hcA hcB
    (coefficient_embedding_equal A B a b r s hA hB h hr hs)

theorem rectangle_coefficients (A B a b : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual A B a b) :
    Γ ⊢[PRAAx] coefficientsEqual A B a b := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := le (var 0) (Syn.shift (Syn.shift a)) :: le (var 1) (Syn.shift (Syn.shift b)) :: (Γ.map Fm.shift).map Fm.shift
  have shapeA : Δ ⊢[PRAAx] rowShape (Syn.shift (Syn.shift A)) (succ (Syn.shift (Syn.shift b))) (Syn.shift (Syn.shift a)) := by
    simpa [Δ,Fm.shift,Syn.shift] using hA.shift.shift.wk.wk
  have shapeB : Δ ⊢[PRAAx] rowShape (Syn.shift (Syn.shift B)) (succ (Syn.shift (Syn.shift b))) (Syn.shift (Syn.shift a)) := by
    simpa [Δ,Fm.shift,Syn.shift] using hB.shift.shift.wk.wk
  have rect : Δ ⊢[PRAAx] rectangleEqual (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) := by
    simpa [Δ,Fm.shift,Syn.shift] using h.shift.shift.wk.wk
  simpa only [Δ,List.map_cons,Fm.shift,subst_le,Syn.shift,Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one] using coefficient_equal (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B))
    (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) (var 1) (var 0) shapeA shapeB rect Prf.hyp1 Prf.hyp0

def gridPointF : PR 1 := PTm.toPR (gridPoint (var 0))
def observationF : PR 4 := PTm.toPR (observation (var 0) (var 1) (var 2) (var 3))
def output (A B r s : PTm n) : PTm n := pairT (entry (entry A r) s) (entry (entry B r) s)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (A B r s : PTm n) : PTm n := app outputF ![A,B,r,s]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (A B r s : PTm n) :
    Syn.subst σ (output A B r s) = output (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ s) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (A B r s : PTm n) :
    Syn.subst σ (run A B r s) = run (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ s) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem grid_point_at (i : PTm n) : Γ ⊢[PRAAx] ap1 gridPointF i ≐ gridPoint i := by
  simpa [gridPointF,ap1] using toPR_eq (Γ := Γ) (gridPoint (var 0) : PTm 1) ![i]
theorem observation_at (A b i j : PTm n) : Γ ⊢[PRAAx] app observationF ![A,b,i,j] ≐ observation A b i j := by
  simpa [observationF] using toPR_eq (Γ := Γ) (observation (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,b,i,j]
theorem program_at (A B r s : PTm n) : Γ ⊢[PRAAx] run A B r s ≐ output A B r s := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,B,r,s]
theorem returned_left (A B r s : PTm n) : Γ ⊢[PRAAx] fstT (run A B r s) ≐ entry (entry A r) s :=
  (congrFst (program_at A B r s)).eqTrans (fst_pair _ _)
theorem returned_right (A B r s : PTm n) : Γ ⊢[PRAAx] sndT (run A B r s) ≐ entry (entry B r) s :=
  (congrSnd (program_at A B r s)).eqTrans (snd_pair _ _)

theorem returned_field_equal (A B a b r s : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual A B a b)
    (hr : Γ ⊢[PRAAx] le r b) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    rationalEq (fstT (run A B r s)) (sndT (run A B r s)) :=
  RationalArgmin.rationalEq_congr (returned_left A B r s).eqSymm (returned_right A B r s).eqSymm
    (coefficient_equal A B a b r s hA hB h hr hs)

theorem returned_literal_equal (A B a b r s : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ b) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual A B a b)
    (hr : Γ ⊢[PRAAx] le r b) (hs : Γ ⊢[PRAAx] le s a)
    (hcA : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry (entry A r) s))
    (hcB : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry (entry B r) s)) : Γ ⊢[PRAAx]
    fstT (run A B r s) ≐ sndT (run A B r s) :=
  (returned_left A B r s).eqTrans ((canonical_coefficient A B a b r s hA hB h hr hs hcA hcB).eqTrans
    (returned_right A B r s).eqSymm)

theorem actual_rational_natural_grid_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (embed (gridPoint (var 0)) ≐ GaussianRationalFiniteGridIdentity.gridPoint (var 0)) :=
  closeUniv 1 (grid_point_embedding _)

theorem actual_rational_rectangle_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rowShape (var 0) (succ (var 3)) (var 2) ⟶ rowShape (var 1) (succ (var 3)) (var 2) ⟶
      rectangleEqual (var 0) (var 1) (var 2) (var 3) ⟶ coefficientsEqual (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (rectangle_coefficients _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_rational_coefficient_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (succ (var 3)) (var 2) ⟶ rowShape (var 1) (succ (var 3)) (var 2) ⟶
      rectangleEqual (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 3) ⟶ le (var 5) (var 2) ⟶
      rationalEq (entry (entry (var 0) (var 4)) (var 5)) (entry (entry (var 1) (var 4)) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (coefficient_equal _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem actual_canonical_rational_coefficient_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (succ (var 3)) (var 2) ⟶ rowShape (var 1) (succ (var 3)) (var 2) ⟶
      rectangleEqual (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 3) ⟶ le (var 5) (var 2) ⟶
      RationalNormalForm.wellFormed (entry (entry (var 0) (var 4)) (var 5)) ⟶
      RationalNormalForm.wellFormed (entry (entry (var 1) (var 4)) (var 5)) ⟶
      entry (entry (var 0) (var 4)) (var 5) ≐ entry (entry (var 1) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (canonical_coefficient _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk.wk Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))))

theorem actual_rational_grid_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (app observationF ![var 0,var 1,var 2,var 3] ≐ observation (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (observation_at _ _ _ _)

theorem actual_rational_grid_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

theorem actual_returned_rational_grid_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (succ (var 3)) (var 2) ⟶ rowShape (var 1) (succ (var 3)) (var 2) ⟶
      rectangleEqual (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 3) ⟶ le (var 5) (var 2) ⟶
      rationalEq (fstT (run (var 0) (var 1) (var 4) (var 5))) (sndT (run (var 0) (var 1) (var 4) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (returned_field_equal _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.RationalBivariateGridCoefficients
