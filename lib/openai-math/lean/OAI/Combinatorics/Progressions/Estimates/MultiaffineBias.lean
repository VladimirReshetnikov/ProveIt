import OAI.Combinatorics.Progressions.Dynamics.MultiaffineBiasBudget
import OAI.Combinatorics.Progressions.Polynomial.MultiaffinePhaseDifference

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearInteger_rational_approximation {θ ε : ℝ} {q : ℕ} (hq : 0 < q)
    (hnear : NearInteger ε ((q : ℝ)*θ)) :
    ∃ m : ℤ, |θ-(m : ℝ)/q| ≤ ε := by
  obtain ⟨m,hm⟩ := hnear
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have he : θ-(m : ℝ)/q = ((q : ℝ)*θ-m)/q := by field_simp
  refine ⟨m, ?_⟩
  rw [he, abs_div, abs_of_pos hqp]
  exact (div_le_div_of_nonneg_right hm hqp.le).trans
    (div_le_self ((abs_nonneg _).trans hm) hq1)

theorem multiaffine_bias_approximation {n : ℕ} (N : Fin n → ℕ) (M : ℕ)
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i), 𝔼 t : Fin M,
      multiaffineIntervalPhase a b u w x t‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |a Finset.univ-(m : ℝ)/q| ≤
        multiaffineBiasBudget n ζ / ((M : ℝ)*∏ i, (N i : ℝ)) := by
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ i, 0 < N i := fun i => by exact_mod_cast hQ.trans_le (hN i)
  have hMp : 0 < M := by exact_mod_cast hQ.trans_le hM
  have hp : 0 < ζ^(2^n) := pow_pos hζ _
  have hp1 : ζ^(2^n) ≤ 1 := pow_le_one₀ hζ.le hζ1
  obtain ⟨hLQ,hQmul⟩ := multiaffineBiasBudget_bounds n hζ hζ1
  have hMlarge : denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) ≤ (M : ℝ)*ζ^(2^n) := by
    rw [← hQmul]
    exact mul_le_mul_of_nonneg_right hM hp.le
  obtain ⟨q,hq,hqL,hnear⟩ := product_difference_bias_approximation n N M hMp hp hp1
    (fun i => hLQ.trans (hN i)) hMlarge
    (multiaffine_phase_box_bias N hNp M hMp a b u w hζ.le hbias)
  refine ⟨q,hq,hqL.trans hLQ,nearInteger_rational_approximation hq ?_⟩
  convert hnear using 1
  unfold multiaffineBiasBudget
  ring

end Erdos3

end

end OAI
