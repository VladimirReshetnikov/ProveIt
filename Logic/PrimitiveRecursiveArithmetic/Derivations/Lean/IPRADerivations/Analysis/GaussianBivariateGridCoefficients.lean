import IPRADerivations.Analysis.GaussianPolynomialMonicCompanion
import IPRADerivations.Analysis.GaussianRationalGridCoefficientEquality

/-!
# Coefficient equality from the actual rectangular bivariate grid

At each fixed grid abscissa, the scalar grid theorem identifies the
evaluations of the original stored rows. Applying it again across the
grid abscissas identifies every stored coefficient by field value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBivariateGridCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialMonicCompanion (values values_length values_lookup rowShape row_shape_at)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianRationalGridCoefficientEquality (gridEqual coefficient_recode_equal)
open GaussianRationalHorner (canonical canonical_congr evaluate horner_canonical)
open GaussianRationalSyntheticDivision (canonicalCoefficients canonical_coefficient_at)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def specializationGrid (G H b x : PTm n) : Fm PTm n :=
  gridEqual (values G (succ b) x) (values H (succ b) x) b

def rectangleEqual (G H a b : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift a) ⟶ specializationGrid (Syn.shift G) (Syn.shift H) (Syn.shift b) (gridPoint (var 0)))

def recodedEntriesEqual (G H a b : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift b) ⟶ .all (le (var 0) (Syn.shift (Syn.shift a)) ⟶
    recode (entry (entry (Syn.shift (Syn.shift G)) (Syn.shift (var 0))) (var 0)) ≐
    recode (entry (entry (Syn.shift (Syn.shift H)) (Syn.shift (var 0))) (var 0))))

@[simp] theorem subst_specializationGrid {k : ℕ} (σ : Fin n → PTm k) (G H b x : PTm n) :
    (specializationGrid G H b x).subst σ =
      specializationGrid (Syn.subst σ G) (Syn.subst σ H) (Syn.subst σ b) (Syn.subst σ x) := by
  simp [specializationGrid]
@[simp] theorem subst_rectangleEqual {k : ℕ} (σ : Fin n → PTm k) (G H a b : PTm n) :
    (rectangleEqual G H a b).subst σ = rectangleEqual (Syn.subst σ G) (Syn.subst σ H)
      (Syn.subst σ a) (Syn.subst σ b) := by simp [rectangleEqual,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_recodedEntriesEqual {k : ℕ} (σ : Fin n → PTm k) (G H a b : PTm n) :
    (recodedEntriesEqual G H a b).subst σ = recodedEntriesEqual (Syn.subst σ G) (Syn.subst σ H)
      (Syn.subst σ a) (Syn.subst σ b) := by simp [recodedEntriesEqual,Syn.subst_shift,Syn.shift_subst]

theorem specialization_at (G H a b i : PTm n) (h : Γ ⊢[PRAAx] rectangleEqual G H a b) (hi : Γ ⊢[PRAAx] le i a) :
    Γ ⊢[PRAAx] specializationGrid G H b (gridPoint i) := by
  have rule : Γ ⊢[PRAAx] le i a ⟶ specializationGrid G H b (gridPoint i) := by
    simpa [rectangleEqual] using h.allE i
  exact .impE rule hi

theorem row_at_specialization (G H b x r : PTm n) (hr : Γ ⊢[PRAAx] le r b)
    (h : Γ ⊢[PRAAx] specializationGrid G H b x) : Γ ⊢[PRAAx] evaluate (entry G r) x ≐ evaluate (entry H r) x := by
  let C := values G (succ b) x
  let D := values H (succ b) x
  have bound : Γ ⊢[PRAAx] lt r (succ b) := (succ_monus_succ _ _).eqTrans hr
  have g := values_lookup (Γ := Γ) G (succ b) x r bound
  have hh := values_lookup (Γ := Γ) H (succ b) x r bound
  have fields := coefficient_recode_equal C D b r (values_length _ _ _) (values_length _ _ _) h hr
  exact (recode_eq _ (horner_canonical _ _ _)).eqSymm.eqTrans
    ((recode_congr g).eqSymm.eqTrans
      (fields.eqTrans ((recode_congr hh).eqTrans (recode_eq _ (horner_canonical _ _ _)))))

theorem row_grid (G H a b r : PTm n) (h : Γ ⊢[PRAAx] rectangleEqual G H a b) (hr : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] gridEqual (entry G r) (entry H r) a := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] rectangleEqual (Syn.shift G) (Syn.shift H) (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift r) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  simpa [Syn.shift] using row_at_specialization (Syn.shift G) (Syn.shift H) (Syn.shift b) (gridPoint (var 0))
    (Syn.shift r) hrs.wk (specialization_at _ _ _ _ _ hs.wk Prf.hyp0)

theorem recoded_coefficient (G H a b r s : PTm n) (hG : Γ ⊢[PRAAx] rowShape G (succ b) a)
    (hH : Γ ⊢[PRAAx] rowShape H (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual G H a b)
    (hr : Γ ⊢[PRAAx] le r b) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    recode (entry (entry G r) s) ≐ recode (entry (entry H r) s) :=
  coefficient_recode_equal _ _ _ _
    (row_shape_at _ _ _ _ hG ((succ_monus_succ _ _).eqTrans hr))
    (row_shape_at _ _ _ _ hH ((succ_monus_succ _ _).eqTrans hr)) (row_grid G H a b r h hr) hs

theorem canonical_coefficient (G H a b r s : PTm n) (hG : Γ ⊢[PRAAx] rowShape G (succ b) a)
    (hH : Γ ⊢[PRAAx] rowShape H (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual G H a b)
    (hr : Γ ⊢[PRAAx] le r b) (hs : Γ ⊢[PRAAx] le s a)
    (hGC : Γ ⊢[PRAAx] canonical (entry (entry G r) s)) (hHC : Γ ⊢[PRAAx] canonical (entry (entry H r) s)) :
    Γ ⊢[PRAAx] entry (entry G r) s ≐ entry (entry H r) s :=
  (recode_eq _ hGC).eqSymm.eqTrans ((recoded_coefficient G H a b r s hG hH h hr hs).eqTrans (recode_eq _ hHC))

private theorem row_recodes (G H a b r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G (succ b) a)
    (hH : Γ ⊢[PRAAx] rowShape H (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual G H a b)
    (hr : Γ ⊢[PRAAx] le r b) : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift a) ⟶
      recode (entry (entry (Syn.shift G) (Syn.shift r)) (var 0)) ≐ recode (entry (entry (Syn.shift H) (Syn.shift r)) (var 0))) := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (succ (Syn.shift b)) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hG.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (succ (Syn.shift b)) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hH.shift
  have equal : Γ.map Fm.shift ⊢[PRAAx] rectangleEqual (Syn.shift G) (Syn.shift H) (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have bound : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift r) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hr.shift
  exact .allI (.impI (recoded_coefficient (Syn.shift G) (Syn.shift H) (Syn.shift a) (Syn.shift b)
    (Syn.shift r) (var 0) gs.wk hs.wk equal.wk bound.wk Prf.hyp0))

theorem rectangle_coefficients (G H a b : PTm n) (hG : Γ ⊢[PRAAx] rowShape G (succ b) a)
    (hH : Γ ⊢[PRAAx] rowShape H (succ b) a) (h : Γ ⊢[PRAAx] rectangleEqual G H a b) :
    Γ ⊢[PRAAx] recodedEntriesEqual G H a b := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (succ (Syn.shift b)) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hG.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (succ (Syn.shift b)) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hH.shift
  have equal : Γ.map Fm.shift ⊢[PRAAx] rectangleEqual (Syn.shift G) (Syn.shift H) (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  exact .allI (.impI (row_recodes (Syn.shift G) (Syn.shift H) (Syn.shift a) (Syn.shift b) (var 0)
    gs.wk hs.wk equal.wk Prf.hyp0))

theorem actual_rectangle_coefficient_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rowShape (var 0) (succ (var 3)) (var 2) ⟶ rowShape (var 1) (succ (var 3)) (var 2) ⟶
      rectangleEqual (var 0) (var 1) (var 2) (var 3) ⟶ recodedEntriesEqual (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (rectangle_coefficients _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBivariateGridCoefficients
