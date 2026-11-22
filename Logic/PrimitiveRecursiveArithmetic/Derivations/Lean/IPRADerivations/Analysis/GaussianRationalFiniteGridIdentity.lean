import IPRADerivations.Analysis.GaussianRationalPolynomialDegree

/-!
# A genuine numerical grid detects the zero polynomial

The actual grid contains the natural Gaussian points 0 through n. Its
field-value distinctness is derived from the actual rational constructors.
The computed-degree root bound then forces a polynomial of width n+1
vanishing on this grid to have zero original coefficient values. There
is no supplied evaluation-to-coefficient law or fixed external degree.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiniteGridIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero canonical evaluate ofGaussian represents_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nativePoint (i : PTm n) : PTm n := ComplexLogarithmRemainder.code (ZT.ofNat i) (ZT.ofNat zero)
def gridPoint (i : PTm n) : PTm n := ofGaussian (nativePoint i) one
def gridBody : PTm 2 := gridPoint (var 0)
def grid (N : PTm n) : PTm n := sequence gridBody (succ N) zero
@[simp] theorem subst_nativePoint {l : ℕ} (σ : Fin n → PTm l) (i : PTm n) :
    Syn.subst σ (nativePoint i) = nativePoint (Syn.subst σ i) := by simp [nativePoint]
@[simp] theorem subst_gridPoint {l : ℕ} (σ : Fin n → PTm l) (i : PTm n) :
    Syn.subst σ (gridPoint i) = gridPoint (Syn.subst σ i) := by simp [gridPoint]
@[simp] theorem subst_grid {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (grid N) = grid (Syn.subst σ N) := by simp [grid]
theorem point_represents (i : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.represents (gridPoint i) (nativePoint i) one :=
  GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _)
theorem point_canonical (i : PTm n) : Γ ⊢[PRAAx] canonical (gridPoint i) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)
theorem grid_length (N : PTm n) : Γ ⊢[PRAAx] length (grid N) ≐ succ N := sequence_length _ _ _
theorem grid_lookup (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N)) : Γ ⊢[PRAAx]
    entry (grid N) i ≐ gridPoint i := by
  simpa only [grid,gridBody,inst2,subst_gridPoint,Syn.subst_var,Matrix.cons_val_zero] using sequence_decode gridBody (x := zero) hi

/-- Only actual positive decoded denominators are cancelled by
numerator_unique. No natural point numerator is assumed positive. -/
theorem point_difference_zero_reflect (i j : PTm n) (h : Γ ⊢[PRAAx] qsub (gridPoint i) (gridPoint j) ≐ qzero) : Γ ⊢[PRAAx] i ≐ j := by
  have rep := GaussianRationalMetric.qsub_represents _ _ _ _ one (le_refl _)
    (point_represents (Γ := Γ) i) (point_represents j)
  have eq := GaussianReciprocalHorner.numerator_unique qzero
    (GaussianRootAlgebra.sub (nativePoint i) (nativePoint j)) ComplexLogarithmRemainder.zeroCode one
    (represents_congr h (GaussianRootAlgebra.equal_refl _) (.eqRefl _) rep)
    (GaussianRationalHorner.zero_represents _)
  have real := GaussianRootAlgebra.equal_re eq
  simp only [nativePoint,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_zero,
    ComplexLogarithmRemainder.eval_re_code,ZT.toZ_ofNat] at real
  apply deriveNat
  linear_combination real

theorem grid_pair_nonzero (N i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N))
    (hj : Γ ⊢[PRAAx] lt j (succ N)) (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (qsub (entry (grid N) j) (entry (grid N) i) ≐ qzero) := by
  refine .impI (lt_irrefl i Fm.bot ?_)
  have equal := point_difference_zero_reflect j i
    ((GaussianRationalSyntheticDivision.qsub_congr (grid_lookup _ _ hj) (grid_lookup _ _ hi)).wk.eqSymm.eqTrans Prf.hyp0)
  exact lt_congr (.eqRefl _) equal hij.wk

theorem grid_distinct_from (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N)) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.distinctFrom (grid N) i := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (succ (Syn.shift N)) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hi.shift
  refine .allI (.impI (.impI ?_))
  let Δ := lt (Syn.shift i) (var 0) :: lt (var 0) (length (Syn.shift (grid N))) :: Γ.map Fm.shift
  have hj : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) :=
    lt_congr (.eqRefl _) (grid_length _) (by
      simpa only [Δ,Syn.shift,subst_grid] using
        (Prf.hyp1 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (grid N)))))
  have e := grid_pair_nonzero (Syn.shift N) (Syn.shift i) (var 0) hs.wk.wk hj (Prf.hyp0 (Ax := PRAAx) (Γ := lt (var 0) (length (Syn.shift (grid N))) :: Γ.map Fm.shift))
  simpa only [Δ,Syn.shift,subst_grid,subst_entry] using e
theorem grid_distinct (N : PTm n) : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct (grid N) := by
  refine .allI (.impI ?_)
  have hi : lt (var 0) (length (Syn.shift (grid N))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (succ (Syn.shift N)) :=
    lt_congr (.eqRefl _) (grid_length _) (by
      simpa only [Syn.shift,subst_grid] using (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift)
        (φ := lt (var 0) (length (Syn.shift (grid N))))))
  simpa only [Syn.shift,subst_grid] using grid_distinct_from (Syn.shift N) (var 0) hi

/-- The actual nonzero/zero bit decides the branch. A nonzero polynomial
would have n+1 distinct listed roots but computed degree at most n. -/
theorem finite_grid_zero (C N : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hRoots : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C (grid N)) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialDegree.allZero C N := by
  refine .orE (GaussianRationalPolynomialDegree.flag_cases C N) ?_ ?_
  · exact GaussianRationalPolynomialDegree.all_zero_of_flag_zero _ _ Prf.hyp0
  · have bound := GaussianRationalPolynomialDegree.computed_root_bound C N (grid N) hLen.wk
      (GaussianRationalPolynomialDegree.nonzero_of_flag_one _ _ Prf.hyp0) hRoots.wk (grid_distinct _)
    exact not_succ_le_self N _ (le_trans (le_congr (grid_length _) (.eqRefl _) (.andE₁ bound)) (.andE₂ bound))
theorem coefficient_zero (C N i : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hRoots : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C (grid N)) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianTranslatedNonconstant.recode (entry C i) ≐ qzero :=
  GaussianTranslatedNonconstant.zero_prefix_at _ _ _ (finite_grid_zero _ _ hLen hRoots) ((succ_monus_succ _ _).eqTrans hi)

def output (C N : PTm n) : PTm n := pairT (grid N) (GaussianRationalPolynomialDegree.run C N)
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (output C N) = output (Syn.subst σ C) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (run C N) = run (Syn.subst σ C) (Syn.subst σ N) := by simp [run]
theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1)) ![C,N]
theorem returned_grid (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ grid N :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_degree_program (C N : PTm n) : Γ ⊢[PRAAx] sndT (run C N) ≐ GaussianRationalPolynomialDegree.run C N :=
  (congrSnd (program_at _ _)).eqTrans (snd_pair _ _)
theorem returned_flag (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ GaussianRationalPolynomialDegree.flag C N :=
  (congrFst (returned_degree_program _ _)).eqTrans (GaussianRationalPolynomialDegree.returned_flag _ _)
theorem returned_grid_length (C N : PTm n) : Γ ⊢[PRAAx] length (fstT (run C N)) ≐ succ N :=
  (congrFst (returned_grid _ _)).eqTrans (grid_length _)
theorem returned_flag_zero (C N : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hRoots : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C (grid N)) : Γ ⊢[PRAAx]
    fstT (sndT (run C N)) ≐ zero :=
  (returned_flag _ _).eqTrans (GaussianRationalPolynomialDegree.flag_zero_of_all_zero _ _ (finite_grid_zero _ _ hLen hRoots))

/-! Every degree, original raw coefficient list and query index is bound
numerically. The root hypothesis is a finite grid contract, not a global
polynomial identity or an evaluator oracle. -/
theorem actual_grid_geometry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((length (grid (var 0)) ≐ succ (var 0)) ⋏ GaussianRationalFiniteRoots.distinct (grid (var 0))) :=
  closeUniv 1 (.andI (grid_length _) (grid_distinct _))
theorem actual_grid_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (succ (var 0)) ⟶ entry (grid (var 0)) (var 1) ≐ gridPoint (var 1)) :=
  closeUniv 2 (.impI (grid_lookup _ _ Prf.hyp0))
theorem actual_grid_difference_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qsub (gridPoint (var 0)) (gridPoint (var 1)) ≐ qzero ⟶ var 0 ≐ var 1) :=
  closeUniv 2 (.impI (point_difference_zero_reflect _ _ Prf.hyp0))
theorem finite_grid_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (var 0) ≐ succ (var 1) ⟶ GaussianRationalFiniteRoots.roots (var 0) (grid (var 1)) ⟶
      GaussianRationalPolynomialDegree.allZero (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (finite_grid_zero _ _ Prf.hyp1 Prf.hyp0)))
theorem finite_grid_coefficient_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ GaussianRationalFiniteRoots.roots (var 0) (grid (var 1)) ⟶ le (var 2) (var 1) ⟶
      GaussianTranslatedNonconstant.recode (entry (var 0) (var 2)) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (.impI (coefficient_zero _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_grid_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem returned_grid_zero_flag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (var 0) ≐ succ (var 1) ⟶ GaussianRationalFiniteRoots.roots (var 0) (grid (var 1)) ⟶
      fstT (sndT (run (var 0) (var 1))) ≐ zero) :=
  closeUniv 2 (.impI (.impI (returned_flag_zero _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalFiniteGridIdentity
