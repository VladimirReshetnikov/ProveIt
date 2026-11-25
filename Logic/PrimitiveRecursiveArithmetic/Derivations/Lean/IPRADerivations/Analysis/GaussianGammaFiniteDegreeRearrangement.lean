import IPRADerivations.Analysis.GaussianGammaCanonicalTailFiniteSplit
import IPRADerivations.Analysis.GaussianRationalFubini
import IPRADerivations.Analysis.GaussianGammaCanonicalExponent
import IPRADerivations.Core.CongruenceTactic

/-!
# Uniform finite degree rearrangement of the original canonical Gamma tail

The original finite cleared tail is exactly the degree-major rectangular
sum of its genuine quadratic-and-higher Taylor terms. All factor counts,
Taylor cutoffs and rational input codes remain internal. The original
R²/N bound transfers to the rearranged output, uniformly in both cutoffs.
This is the finite rearrangement underlying C16; the zeta-name limit and
the sharp degree remainder are separate statements.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteDegreeRearrangement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian canonical represents_congr canonical_unique ofGaussian_represents ofGaussian_canonical
  qmul_canonical positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianRationalFiniteSum (sum sum_canonical sum_index_congr sum_congr_bounded termsEqual)
open GaussianFiniteLogarithmPolynomial (sourceTerm value coefficient)
open GaussianGammaCanonicalTailFiniteSplit (term gaussianSum)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def localSeries (z D L : PTm n) : PTm n := sum (shiftBody sourceTerm) (succ L) (ofGaussian z D)
@[simp] theorem subst_localSeries {m : ℕ} (σ : Fin n → PTm m) (z D L : PTm n) :
    Syn.subst σ (localSeries z D L) = localSeries (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ L) := by simp [localSeries]

theorem linear_term (z D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    inst2 sourceTerm zero (ofGaussian z D) ≐ ofGaussian z D := by
  have rep := represents_congr (.eqRefl _) (GaussianFiniteLogarithmSampler.term_numerator_zero z)
    (GaussianFiniteLogarithmSampler.term_denominator_zero D)
    (GaussianFiniteLogarithmSampler.source_term_represents z D zero hD)
  have can : Γ ⊢[PRAAx] canonical (inst2 sourceTerm zero (ofGaussian z D)) := by
    rw [GaussianFiniteLogarithmPolynomial.source_term_at]
    exact qmul_canonical _ _
  exact canonical_unique _ _ z D can (ofGaussian_canonical z D hD) hD rep (ofGaussian_represents z D hD)

theorem original_factor_as_series (z D L : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GammaLogarithmFactorBridge.localFactor z D L ≐ localSeries z D L := by
  have full : Γ ⊢[PRAAx] value (L+two) (ofGaussian z D) ≐
      GaussianRationalHorner.qadd (ofGaussian z D) (localSeries z D L) :=
    (sum_index_congr sourceTerm (by ipra_ring) (.eqRefl _)).eqTrans
      ((GaussianRationalFiniteSum.sum_shift_first sourceTerm (succ L) (ofGaussian z D)).eqTrans
        (qadd_congr (linear_term z D hD) (.eqRefl _)))
  have same := ((GammaLogarithmFactorBridge.sum_is_original_sample z D L hD).eqTrans
    (GaussianFiniteLogarithmSampler.value_eq_original_sample z D L hD).eqSymm).eqTrans full
  exact (qadd_sub_cancel (ofGaussian z D) (GammaLogarithmFactorBridge.localFactor z D L)
    (ofGaussian_canonical _ _ (GammaCanonicalFactors.factorDenominator_positive D L hD))).eqSymm.eqTrans
      ((qsub_congr same (.eqRefl _)).eqTrans (qadd_sub_cancel _ _ (sum_canonical _ _ _)))

def matrixData (z B N : PTm n) : PTm n := pairT z (pairT B N)
def degreeTerm (z B N i j : PTm n) : PTm n :=
  inst2 (shiftBody sourceTerm) j (ofGaussian z (B*succ (N+i)))
def matrix : PTm 3 := degreeTerm (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0) (var 1)
def degreeMajor (z B N r L : PTm n) : PTm n :=
  GaussianRationalFubini.columnFirst matrix r (succ L) (matrixData z B N)
@[simp] theorem subst_matrixData {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (matrixData z B N) = matrixData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [matrixData]
@[simp] theorem subst_degreeTerm {m : ℕ} (σ : Fin n → PTm m) (z B N i j : PTm n) :
    Syn.subst σ (degreeTerm z B N i j) = degreeTerm (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ i) (Syn.subst σ j) := by
  simp [degreeTerm]
@[simp] theorem subst_degreeMajor {m : ℕ} (σ : Fin n → PTm m) (z B N r L : PTm n) :
    Syn.subst σ (degreeMajor z B N r L) = degreeMajor (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) := by
  simp [degreeMajor]

theorem degree_term_congr {z z' B B' N N' i i' j j' : PTm n}
    (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B') (hN : Γ ⊢[PRAAx] N ≐ N')
    (hi : Γ ⊢[PRAAx] i ≐ i') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    degreeTerm z B N i j ≐ degreeTerm z' B' N' i' j' := by
  ipra_congr (degreeTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hz, hB, hN, hi, hj]

theorem matrix_entry (i j z B N : PTm n) : Γ ⊢[PRAAx]
    inst3 matrix i j (matrixData z B N) ≐ degreeTerm z B N i j := by
  simp only [matrix,inst3,subst_degreeTerm,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact degree_term_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _) (.eqRefl _)

theorem original_degree_entry (i j z B N : PTm n) : Γ ⊢[PRAAx]
    inst3 matrix i j (matrixData z B N) ≐
      GaussianRationalHorner.qmul (coefficient (succ j))
        (GaussianRationalReciprocal.power (ofGaussian z (B*succ (N+i))) (succ (succ j))) := by
  simpa only [degreeTerm,inst2_shiftBody,GaussianFiniteLogarithmPolynomial.source_term_at] using matrix_entry (Γ := Γ) i j z B N

theorem matrix_row_as_series (i z B N L : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row matrix i (succ L) (matrixData z B N) ≐ localSeries z (B*succ (N+i)) L := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have entry := (GaussianRationalFubini.row_entry (Γ := lt (var 0) (succ (Syn.shift L)) :: Γ.map Fm.shift)
    matrix (Syn.shift i) (var 0) (matrixData (Syn.shift z) (Syn.shift B) (Syn.shift N))).eqTrans
    (matrix_entry (Syn.shift i) (var 0) (Syn.shift z) (Syn.shift B) (Syn.shift N))
  simpa only [termsEqual,GaussianRationalFubini.subst_row,matrixData,subst_matrixData,degreeTerm,
    Syn.shift,subst_pairT,GaussianRationalHorner.subst_ofGaussian,PTm.subst_mul,PTm.subst_add,ConciseIPRA.PTm.subst_succ] using entry

theorem row_as_original_factor (i z B N L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row matrix i (succ L) (matrixData z B N) ≐ term z B (succ (N+i)) L :=
  (matrix_row_as_series i z B N L).eqTrans
    (original_factor_as_series z (B*succ (N+i)) L (positive_product _ _ hB (zero_lt_succ _))).eqSymm

theorem original_sum_as_rows (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    gaussianSum z B N r L ≐ GaussianRationalFubini.rowFirst matrix r (succ L) (matrixData z B N) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have left := GaussianGammaCanonicalTailFiniteSplit.body_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
    (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift L) (var 0)
  have right := (GaussianRationalFubini.row_sum_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) matrix (var 0) (succ (Syn.shift L))
    (matrixData (Syn.shift z) (Syn.shift B) (Syn.shift N))).eqTrans
    (row_as_original_factor (var 0) (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift L) bs.wk)
  simpa only [termsEqual,GaussianGammaCanonicalTailFiniteSplit.subst_data,subst_matrixData,subst_pairT,
    ConciseIPRA.PTm.subst_succ,Syn.shift] using left.eqTrans right.eqSymm

theorem original_finite_rearrangement (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalTailFiniteSplit.value z B N r L ≐ degreeMajor z B N r L :=
  (GaussianGammaCanonicalTailFiniteSplit.finite_value_as_sum z B N r L hB).eqTrans
    ((original_sum_as_rows z B N r L hB).eqTrans (GaussianRationalFubini.fubini matrix r (succ L) (matrixData z B N)))

theorem degree_major_canonical (z B N r L : PTm n) : Γ ⊢[PRAAx] canonical (degreeMajor z B N r L) :=
  GaussianRationalFubini.column_first_canonical _ _ _ _

theorem uniform_rearranged_bound (z R B N r L : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    bounded (degreeMajor z B N r L) (R*R) N := by
  let a := GammaCanonicalFactors.finiteTail z B N r L
  let D := GammaCanonicalFactors.tailDenominator B N r L
  have den : Γ ⊢[PRAAx] le one D := GammaCanonicalFactors.tailDenominator_positive B N r L h.andE₁
  have native := GammaCanonicalFactors.rational_disk_tail_bound z R B N r L
    h.andE₂.andE₂.andE₁ h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂
  have clear : Γ ⊢[PRAAx] le ((N*N)*ComplexLogarithmRemainder.normSq a) (((R*R)*(R*R))*(D*D)) :=
    le_congr (ComplexLogarithmRemainder.normSq_scale N a) (by ipra_ring) native
  exact GaussianRationalMetric.bounded_of_cleared _ a D (R*R) N den h.andE₂.andE₁
    (represents_congr (original_finite_rearrangement z B N r L h.andE₁) (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
      (ofGaussian_represents a D den)) clear

theorem original_two_radius_rearranged_bound (z R B r L : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    bounded (degreeMajor z B (two*R) r L) (R*R) (two*R) :=
  uniform_rearranged_bound z R B (two*R) r L (GaussianGammaCanonicalExponent.tail_source z R B h)

/-- The existing fixed Fubini program is specialized to the actual Gamma
Taylor cell, and returns both orders of the same finite rectangle. -/
def run (z B N r L : PTm n) : PTm n := GaussianRationalFubini.run matrix r (succ L) (matrixData z B N)
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (z B N r L : PTm n) :
    Syn.subst σ (run z B N r L) = run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) := by
  simp [run]
theorem returned_original_value (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (run z B N r L) ≐ GaussianGammaCanonicalTailFiniteSplit.value z B N r L :=
  (GaussianRationalFubini.returned_rows matrix r (succ L) (matrixData z B N)).eqTrans
    ((original_sum_as_rows z B N r L hB).eqSymm.eqTrans
      (GaussianGammaCanonicalTailFiniteSplit.finite_value_as_sum z B N r L hB).eqSymm)
theorem returned_degree_major (z B N r L : PTm n) : Γ ⊢[PRAAx] sndT (run z B N r L) ≐ degreeMajor z B N r L :=
  GaussianRationalFubini.returned_columns _ _ _ _
theorem returned_uniform_bound (z R B N r L : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    bounded (sndT (run z B N r L)) (R*R) N :=
  GaussianRationalReciprocal.bound_congr (returned_degree_major z B N r L).eqSymm (.eqRefl _) (.eqRefl _)
    (uniform_rearranged_bound z R B N r L h)

theorem original_local_factor_degree_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GammaLogarithmFactorBridge.localFactor (var 0) (var 1) (var 2) ≐ localSeries (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (original_factor_as_series _ _ _ Prf.hyp0))
theorem original_finite_C16_rearrangement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ GaussianGammaCanonicalTailFiniteSplit.value (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      degreeMajor (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (original_finite_rearrangement _ _ _ _ _ Prf.hyp0))
theorem uniform_finite_C16_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (degreeMajor (var 0) (var 2) (var 3) (var 4) (var 5)) (var 1*var 1) (var 3)) :=
  closeUniv 6 (.impI (uniform_rearranged_bound _ _ _ _ _ _ Prf.hyp0))
theorem original_K_two_R_degree_major_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      bounded (degreeMajor (var 0) (var 2) (two*var 1) (var 3) (var 4)) (var 1*var 1) (two*var 1)) :=
  closeUniv 5 (.impI (original_two_radius_rearranged_bound _ _ _ _ _ Prf.hyp0))
theorem actual_returned_finite_rearrangement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ GaussianGammaCanonicalTailFiniteSplit.value (var 0) (var 1) (var 2) (var 3) (var 4) ⋏
       sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ degreeMajor (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.andI (returned_original_value _ _ _ _ _ Prf.hyp0) (returned_degree_major _ _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteDegreeRearrangement
