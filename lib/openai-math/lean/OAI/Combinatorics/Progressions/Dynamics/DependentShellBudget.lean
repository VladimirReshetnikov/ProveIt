import OAI.Combinatorics.Progressions.Estimates.WeightedListError
import OAI.Combinatorics.Progressions.Geometry.GeometricSpectralBudgets

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem list_dependent_shell_sum_le {α : Type*} (xs : List α)
    (β : α → Type*) [∀ x, Fintype (β x)] (size : α → ℕ)
    (E B : ∀ x, β x → ℝ) {κ : ℝ} {j b : ℕ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsize : ∀ x ∈ xs, size x ≤ j) (hB : ∀ x ∈ xs, ∀ y, 0 ≤ B x y)
    (hE : ∀ x ∈ xs, ∀ y, E x y ≤ κ ^ (b - size x) * B x y) :
    (xs.map (fun x => ∑ y, E x y)).sum ≤
      κ ^ (b - j) * (xs.map (fun x => ∑ y, B x y)).sum := by
  have h := list_weighted_error_sum xs (fun x => ∑ y, E x y)
    (fun x => ∑ y, B x y) (fun _ => 0) (κ ^ (b - j)) (by
      intro x hx
      have hp : κ ^ (b - size x) ≤ κ ^ (b - j) :=
        pow_le_pow_of_le_one hκ0 hκ1 (by have := hsize x hx; omega)
      have hs : (∑ y, E x y) ≤ ∑ y, κ ^ (b - j) * B x y :=
        Finset.sum_le_sum (fun y _ => (hE x hx y).trans
          (mul_le_mul_of_nonneg_right hp (hB x hx y)))
      simpa only [← Finset.mul_sum, add_zero] using hs)
  simpa using h

theorem list_dependent_shell_sum_after_cutoff {α : Type*} (xs : List α)
    (β : α → Type*) [∀ x, Fintype (β x)] (size : α → ℕ)
    (E B : ∀ x, β x → ℝ) {ε P κ : ℝ} {j b : ℕ}
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hsize : ∀ x ∈ xs, size x ≤ j) (hB : ∀ x ∈ xs, ∀ y, 0 ≤ B x y)
    (hE : ∀ x ∈ xs, ∀ y, E x y ≤ κ ^ (b - size x) * B x y)
    (hbudget : (xs.map (fun x => ∑ y, B x y)).sum ≤ Real.exp P)
    (hb : j + CyclicCrootSisask.spectralIterations ε P ≤ b) :
    (xs.map (fun x => ∑ y, E x y)).sum ≤ ε / 16 := by
  have hs := list_dependent_shell_sum_le xs β size E B hκ0 (by linarith) hsize hB hE
  exact (hs.trans (mul_le_mul_of_nonneg_left hbudget (pow_nonneg hκ0 _))).trans
    (geometric_shell_after_cutoff hε hκ0 hκhalf (Real.exp_pos P).le le_rfl le_rfl hb)

theorem list_dependent_uniform_sum_le {α : Type*} (xs : List α)
    (β : α → Type*) [∀ x, Fintype (β x)] (B : ∀ x, β x → ℝ) {R : ℝ} {N : ℕ}
    (hR : 0 ≤ R) (hcard : ∀ x ∈ xs, Fintype.card (β x) ≤ N)
    (hB : ∀ x ∈ xs, ∀ y, B x y ≤ R) :
    (xs.map (fun x => ∑ y, B x y)).sum ≤ (xs.length : ℝ) * N * R := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : (∑ y, B x y) ≤ (N : ℝ) * R := by
      calc
        _ ≤ ∑ _y : β x, R := Finset.sum_le_sum (fun y _ => hB x (by simp) y)
        _ = (Fintype.card (β x) : ℝ) * R := by simp
        _ ≤ (N : ℝ) * R := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard x (by simp)) hR
    have ht := ih (fun y hy => hcard y (by simp [hy])) (fun y hy => hB y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

end Erdos3

end

end OAI
