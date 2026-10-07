import Mathlib

namespace OAI

section

namespace Erdos3

theorem integer_lift_offset_eq {d m : ℕ} (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ)
    (x x' : Fin d → ℝ) (k k' : Fin d → ℤ) (β β' : Fin m → ℤ) {K r : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hr : 0 ≤ r) (hgap : 2 * K * r + 1 / 2 < 1)
    (hx : ∀ j, |x j - (k j : ℝ) - a j| ≤ r)
    (hx' : ∀ j, |x' j - (k' j : ℝ) - a j| ≤ r)
    (hβ : ∀ i, |(∑ j, (M i j : ℝ) * x j) - β i| ≤ 1 / 4)
    (hβ' : ∀ i, |(∑ j, (M i j : ℝ) * x' j) - β' i| ≤ 1 / 4) :
    (fun i => β i - ∑ j, M i j * k j) = fun i => β' i - ∑ j, M i j * k' j := by
  funext i
  have herr (j : Fin d) :
      |(x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j)| ≤ 2 * r :=
    (abs_sub _ _).trans (by linarith [hx j, hx' j])
  have hsum : |∑ j, (M i j : ℝ) *
      ((x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j))| ≤ K * (2 * r) := by
    calc
      _ ≤ ∑ j, |(M i j : ℝ) *
          ((x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |(M i j : ℝ)| * (2 * r) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herr j) (abs_nonneg _)
      _ = (∑ j, |(M i j : ℝ)|) * (2 * r) := (Finset.sum_mul _ _ _).symm
      _ ≤ K * (2 * r) := mul_le_mul_of_nonneg_right (hM i) (by positivity)
  have hlifts : |((∑ j, (M i j : ℝ) * x j) - β i) -
      ((∑ j, (M i j : ℝ) * x' j) - β' i)| ≤ 1 / 2 :=
    (abs_sub _ _).trans (by linarith [hβ i, hβ' i])
  have hid : (((β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) : ℤ) : ℝ) =
      (∑ j, (M i j : ℝ) *
        ((x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j))) -
      (((∑ j, (M i j : ℝ) * x j) - β i) - ((∑ j, (M i j : ℝ) * x' j) - β' i)) := by
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hbound := (abs_sub _ _).trans (add_le_add hsum hlifts)
  rw [← hid] at hbound
  have habs : |(((β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) : ℤ) : ℝ)| < 1 :=
    hbound.trans_lt (by nlinarith [hgap])
  have hlo : (-1 : ℤ) < (β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) := by
    exact_mod_cast (abs_lt.mp habs).1
  have hhi : (β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) < (1 : ℤ) := by
    exact_mod_cast (abs_lt.mp habs).2
  omega

theorem exists_integer_lift_offset {Ω : Type*} {d m : ℕ} (S : Set Ω)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (x : Ω → Fin d → ℝ)
    (k : Ω → Fin d → ℤ) (β : Ω → Fin m → ℤ) {K r : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hr : 0 ≤ r) (hgap : 2 * K * r + 1 / 2 < 1)
    (hx : ∀ u ∈ S, ∀ j, |x u j - (k u j : ℝ) - a j| ≤ r)
    (hβ : ∀ u ∈ S, ∀ i, |(∑ j, (M i j : ℝ) * x u j) - β u i| ≤ 1 / 4) :
    ∃ c : Fin m → ℤ, ∀ u ∈ S, β u = fun i => c i + ∑ j, M i j * k u j := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    refine ⟨fun i => β v i - ∑ j, M i j * k v j, ?_⟩
    intro u hu
    have heq := integer_lift_offset_eq M a (x u) (x v) (k u) (k v) (β u) (β v)
      hM hr hgap (hx u hu) (hx v hv) (hβ u hu) (hβ v hv)
    funext i
    have hi := congrFun heq i
    dsimp only at hi ⊢
    omega
  · exact ⟨0, fun u hu => (hS ⟨u, hu⟩).elim⟩

end Erdos3

end

end OAI
