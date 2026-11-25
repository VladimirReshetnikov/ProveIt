import IPRADerivations.Analysis.GaussianGammaEulerShiftLimit
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual native successor trajectory in the Gamma shift

The recursion retains every original native point code. Its successor is
literally the old shifted constructor. Native coordinate equality, rather
than false raw-code equality, identifies it with z+B*i. Numerical QF
induction also derives the original disk at radius R+i.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShiftTrajectory

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaCanonicalExponent (source)
open GaussianRootAlgebra (equal equal_of_code equal_trans equal_symm equal_refl equal_of_values)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z B : PTm n) : PTm n := pairT z B
def trajectoryF : PR 2 := rec2 (fstT (var 0) : PTm 1) (shifted (var 1) (sndT (var 2)))
def point (z B i : PTm n) : PTm n := ap2 trajectoryF i (data z B)

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z B : PTm n) :
    Syn.subst σ (data z B) = data (Syn.subst σ z) (Syn.subst σ B) := by simp [data]
@[simp] theorem subst_point {l : ℕ} (σ : Fin n → PTm l) (z B i : PTm n) :
    Syn.subst σ (point z B i) = point (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ i) := by simp [point]

theorem point_zero (z B : PTm n) : Γ ⊢[PRAAx] point z B zero ≐ z := by
  have h : Γ ⊢[PRAAx] point z B zero ≐ fstT (data z B) := by
    simpa only [point,trajectoryF,subst_fstT,Syn.subst_var,Syn.inst_zero,
      Matrix.cons_val_zero,Matrix.head_cons] using
      rec2_zero (Γ := Γ) (fstT (var 0) : PTm 1) (shifted (var 1) (sndT (var 2))) (data z B)
  exact h.eqTrans (fst_pair z B)

theorem point_succ (z B i : PTm n) : Γ ⊢[PRAAx] point z B (succ i) ≐ shifted (point z B i) B := by
  have h := rec2_succ (Γ := Γ) (fstT (var 0) : PTm 1) (shifted (var 1) (sndT (var 2))) i (data z B)
  simp only [GaussianGammaEulerHeadShift.subst_shifted,Syn.subst_var,subst_sndT,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h
  have finish : Γ ⊢[PRAAx] shifted (point z B i) (sndT (data z B)) ≐ shifted (point z B i) B := by
    ipra_congr (shifted (var 0) (var 1) : PTm 2) with
      [.eqRefl (point z B i), (show _ ⊢[PRAAx] sndT (data z B) ≐ B from snd_pair z B)]
  exact h.eqTrans finish

theorem point_native_step (z B i : PTm n) (ih : Γ ⊢[PRAAx] equal (point z B i) (translated z B i)) : Γ ⊢[PRAAx]
    equal (point z B (succ i)) (translated z B (succ i)) := by
  apply equal_trans (equal_of_code (point_succ z B i))
  apply equal_trans (GaussianRootAlgebra.add_equal ih (equal_refl _))
  apply equal_of_values <;>
    simp only [shifted,translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals (ipra_simps; ring)

/-- Equality is at the native signed coordinate values, for every raw z. -/
theorem point_native (z B i : PTm n) : Γ ⊢[PRAAx] equal (point z B i) (translated z B i) := by
  have hall : Γ ⊢[PRAAx] .all (equal (point (Syn.shift z) (Syn.shift B) (var 0))
      (translated (Syn.shift z) (Syn.shift B) (var 0))) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [GaussianRootAlgebra.subst_equal,subst_point,GaussianGammaEulerHeadLower.subst_translated,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact equal_trans (equal_of_code (point_zero z B)) (equal_symm (GaussianGammaEulerHeadLower.translated_zero z B))
    · simp only [GaussianRootAlgebra.subst_equal,subst_point,GaussianGammaEulerHeadLower.subst_translated,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact point_native_step _ _ _ Prf.hyp0
  simpa only [GaussianRootAlgebra.subst_equal,subst_point,GaussianGammaEulerHeadLower.subst_translated,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i

theorem point_source_zero (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    source (point z B zero) (R+zero) B := by
  exact .andI (le_congr (.eqRefl _) (add_zero R).eqSymm h.andE₁)
    (.andI h.andE₂.andE₁ (le_congr
      (GaussianRootAlgebra.normSq_equal (equal_of_code (point_zero z B))).eqSymm
      (by ipra_ring) h.andE₂.andE₂))

theorem point_source_step (z R B i : PTm n) (ih : Γ ⊢[PRAAx] source (point z B i) (R+i) B) : Γ ⊢[PRAAx]
    source (point z B (succ i)) (R+succ i) B := by
  have h := GaussianGammaEulerShiftLimit.shifted_source (point z B i) (R+i) B ih
  exact .andI (le_congr (.eqRefl _) (by ipra_ring) h.andE₁)
    (.andI h.andE₂.andE₁ (le_congr
      (GaussianRootAlgebra.normSq_equal (equal_of_code (point_succ z B i))).eqSymm
      (by ipra_ring) h.andE₂.andE₂))

/-- The original source disk is derived along the actual recursion. -/
theorem point_source (z R B i : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    source (point z B i) (R+i) B := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have hall : Γ ⊢[PRAAx] .all (source (point (Syn.shift z) (Syn.shift B) (var 0)) (Syn.shift R+var 0) (Syn.shift B)) := by
    refine PRA.qfInd _ ⟨trivial,⟨trivial,trivial⟩⟩ ?_ ?_
    · simp only [GaussianGammaCanonicalExponent.subst_source,subst_point,PTm.subst_add,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact point_source_zero z R B h
    · simp only [GaussianGammaCanonicalExponent.subst_source,subst_point,PTm.subst_add,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact point_source_step _ _ _ _ Prf.hyp0
  simpa only [GaussianGammaCanonicalExponent.subst_source,subst_point,PTm.subst_add,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i

/-- The stored trajectory normalizes to the literal rising linear factor. -/
theorem point_linear (z B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianRationalHorner.ofGaussian (point z B i) B ≐ GaussianGammaEulerHeadShift.linear z B i :=
  GaussianRationalHorner.canonical_unique _ _ _ _
    (GaussianRationalHorner.ofGaussian_canonical _ _ hB) (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hB
    (GaussianRationalHorner.represents_congr (.eqRefl _) (point_native z B i) (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hB))
    (GaussianRationalHorner.ofGaussian_represents _ _ hB)

/-- All further native translations retain their actual signed values. -/
theorem translated_native (z B i k : PTm n) : Γ ⊢[PRAAx]
    equal (translated (point z B i) B k) (translated z B (i+k)) := by
  apply equal_trans (GaussianRootAlgebra.add_equal (point_native z B i) (equal_refl _))
  apply equal_of_values <;>
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals (ipra_simps; ring)

theorem actual_shift_trajectory_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point (var 0) (var 1) zero ≐ var 0) := closeUniv 2 (point_zero _ _)
theorem actual_shift_trajectory_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (point (var 0) (var 1) (succ (var 2)) ≐ shifted (point (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (point_succ _ _ _)
theorem original_shift_trajectory_native_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equal (point (var 0) (var 1) (var 2)) (translated (var 0) (var 1) (var 2))) := closeUniv 3 (point_native _ _ _)
theorem original_shift_trajectory_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ source (point (var 0) (var 2) (var 3)) (var 1+var 3) (var 2)) :=
  closeUniv 4 (.impI (point_source _ _ _ _ Prf.hyp0))
theorem original_shift_trajectory_linear_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalHorner.ofGaussian (point (var 0) (var 1) (var 2)) (var 1) ≐
      GaussianGammaEulerHeadShift.linear (var 0) (var 1) (var 2)) := closeUniv 3 (.impI (point_linear _ _ _ Prf.hyp0))
theorem original_shift_trajectory_pole_coordinates_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equal (translated (point (var 0) (var 1) (var 2)) (var 1) (var 3))
      (translated (var 0) (var 1) (var 2+var 3))) := closeUniv 4 (translated_native _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaShiftTrajectory
