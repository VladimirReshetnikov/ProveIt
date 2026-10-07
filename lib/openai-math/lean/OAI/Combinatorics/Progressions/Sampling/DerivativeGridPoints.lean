/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {σ κ : Type*} [Fintype κ]

noncomputable def derivativeGridPoint (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r : κ → ℝ) : (σ → ℝ) × (κ → ℝ) :=
  (fun i => (h i : ℝ) / T i, fun j => scale j * (Y (fun i => (h i : ℝ)) - M *ᵥ r) j)

def derivativeGridPoints (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ) :
    Set ((σ → ℝ) × (κ → ℝ)) :=
  {v | ∃ h : σ → ℤ, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
    v = derivativeGridPoint T scale Y M h r}

theorem derivativeGridPoint_mem (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ)
    (h : σ → ℤ) (r : κ → ℝ) (hr : r ∈ realDenominatorGrid l) :
    derivativeGridPoint T scale Y M h r ∈ derivativeGridPoints T scale Y M l :=
  ⟨h, r, hr, rfl⟩

theorem derivativeGridPoint_bound [Fintype σ] (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (scale : κ → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r e : κ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : ∀ i, |(h i : ℝ)| ≤ A * T i)
    (heq : Y (fun i => (h i : ℝ)) = e + M *ᵥ r)
    (he : ∀ j, |e j| ≤ B / scale j) :
    ‖derivativeGridPoint T scale Y M h r‖ ≤ max A B := by
  have hv : Y (fun i => (h i : ℝ)) - M *ᵥ r = e := by rw [heq, add_sub_cancel_right]
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (hA.trans (le_max_left _ _))).mpr
    intro i
    change ‖(h i : ℝ) / T i‖ ≤ max A B
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hT i)]
    exact ((div_le_iff₀ (hT i)).mpr (hh i)).trans (le_max_left _ _)
  · apply (pi_norm_le_iff_of_nonneg (hB.trans (le_max_right _ _))).mpr
    intro j
    change ‖scale j * (Y (fun i => (h i : ℝ)) - M *ᵥ r) j‖ ≤ max A B
    rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (hscale j)]
    have hj : scale j * |e j| ≤ B := by
      simpa only [mul_comm] using (le_div_iff₀ (hscale j)).mp (he j)
    exact hj.trans (le_max_right _ _)

theorem derivativeGridPoint_eq_imp_shift_eq (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h k : σ → ℤ) (r t : κ → ℝ)
    (heq : derivativeGridPoint T scale Y M h r = derivativeGridPoint T scale Y M k t) : h = k := by
  funext i
  have hi := congrArg (fun v : (σ → ℝ) × (κ → ℝ) => v.1 i * T i) heq
  simp only [derivativeGridPoint, div_mul_cancel₀ _ (hT i)] at hi
  exact_mod_cast hi

open scoped Classical in
theorem derivativeGridPoint_card (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ) :
    (H.image (fun h => derivativeGridPoint T scale Y M h (r h))).card = H.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro h _ k _ heq
  exact derivativeGridPoint_eq_imp_shift_eq T hT scale Y M h k (r h) (r k) heq

open scoped Classical in
theorem derivativeGridPoint_difference_card (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (r : (σ → ℤ) → κ → ℝ) :
    (H.image (fun h => derivativeGridPoint T scale Y M (h - h₀) (r h))).card = H.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro h _ k _ heq
  have hd := derivativeGridPoint_eq_imp_shift_eq T hT scale Y M (h - h₀) (k - h₀) (r h) (r k) heq
  simpa only [sub_add_cancel] using congrArg (fun z => z + h₀) hd

theorem exists_bounded_derivativeGridPoint_family [Fintype σ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (R : ℝ)
    (hexists : ∀ h ∈ H, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y M (h - h₀) r‖ ≤ R) :
    ∃ P : Finset ((σ → ℝ) × (κ → ℝ)), P.card = H.card ∧
      ∀ v ∈ P, v ∈ derivativeGridPoints T scale Y M l ∧ ‖v‖ ≤ R := by
  classical
  let r : (σ → ℤ) → κ → ℝ := fun h => if hh : h ∈ H then (hexists h hh).choose else 0
  have hr (h : σ → ℤ) (hh : h ∈ H) : r h ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y M (h - h₀) (r h)‖ ≤ R := by
    simpa only [r, dite_eq_left hh] using (hexists h hh).choose_spec
  refine ⟨H.image (fun h => derivativeGridPoint T scale Y M (h - h₀) (r h)), ?_, ?_⟩
  · apply Finset.card_image_iff.mpr
    intro h _ k _ heq
    have hd := derivativeGridPoint_eq_imp_shift_eq T hT scale Y M (h - h₀) (k - h₀) (r h) (r k) heq
    simpa only [sub_add_cancel] using congrArg (fun z => z + h₀) hd
  · intro v hv
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨derivativeGridPoint_mem T scale Y M l (h - h₀) (r h) (hr h hh).1, (hr h hh).2⟩

end Erdos3

end

end OAI
