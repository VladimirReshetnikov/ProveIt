import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateInjection {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : κ => ℝ) (f i)).comp (ContinuousLinearMap.proj i)

theorem coordinateInjection_apply {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (x : ι → ℝ) :
    coordinateInjection f x = ∑ i, Pi.single (f i) (x i) := by
  simp only [coordinateInjection, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply, ContinuousLinearMap.proj_apply]

theorem coordinateInjection_at_image {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (x : ι → ℝ) (i : ι) :
    coordinateInjection f x (f i) = x i := by
  classical
  simp only [coordinateInjection_apply, Finset.sum_apply, Pi.single_apply]
  simp [hf.eq_iff]

theorem coordinateInjection_off_image {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (x : ι → ℝ) (j : κ) (hj : ∀ i, f i ≠ j) :
    coordinateInjection f x j = 0 := by
  have hji : ∀ i, j ≠ f i := fun i => (hj i).symm
  simp only [coordinateInjection_apply, Finset.sum_apply, Pi.single_apply, hji, ite_false,
    Finset.sum_const_zero]

theorem coordinateInjection_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) : ‖coordinateInjection f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [coordinateInjection_at_image f hf]
    exact norm_le_pi_norm x i
  · rw [coordinateInjection_off_image f x j (not_exists.mp hj), norm_zero]
    exact norm_nonneg x

theorem coordinateInjection_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (i : ι) :
    coordinateInjection f (Pi.single i 1) = Pi.single (f i) 1 := by
  rw [coordinateInjection_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

end Erdos3

end

end OAI
