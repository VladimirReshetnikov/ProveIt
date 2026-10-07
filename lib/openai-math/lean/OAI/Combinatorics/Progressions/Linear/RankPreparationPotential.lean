import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def layerRankPotential {s : ℕ} (d : Fin s → ℕ) : ℕ :=
  ∑ i, (i.val + 1) * d i

theorem layerRankPotential_add {s : ℕ} (d e : Fin s → ℕ) :
    layerRankPotential (d + e) = layerRankPotential d + layerRankPotential e := by
  simp only [layerRankPotential, Pi.add_apply, Nat.mul_add, Finset.sum_add_distrib]

theorem layerRankPotential_mono {s : ℕ} {d e : Fin s → ℕ}
    (h : ∀ i, d i ≤ e i) : layerRankPotential d ≤ layerRankPotential e :=
  Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (h i))

theorem layerRankPotential_single {s : ℕ} (i : Fin s) (n : ℕ) :
    layerRankPotential (Pi.single i n) = (i.val + 1) * n := by
  classical
  simp [layerRankPotential, Pi.single_apply]

theorem sum_ranks_le_potential {s : ℕ} (d : Fin s → ℕ) :
    ∑ i, d i ≤ layerRankPotential d := by
  apply Finset.sum_le_sum
  intro i _
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem layerRankPotential_transfer {s : ℕ} (upper lower : Fin s)
    (hlevel : upper.val = lower.val + 1) {d e : Fin s → ℕ}
    (hstep : ∀ i, (e + Pi.single upper 1 : Fin s → ℕ) i ≤ (d + Pi.single lower 1 : Fin s → ℕ) i) :
    layerRankPotential e + 1 ≤ layerRankPotential d := by
  have h := layerRankPotential_mono hstep
  rw [layerRankPotential_add, layerRankPotential_add,
    layerRankPotential_single, layerRankPotential_single, Nat.mul_one, Nat.mul_one] at h
  omega

theorem layerRankPotential_absorb_constant {s : ℕ} (lowest : Fin s) (hlowest : lowest.val = 0)
    {d e : Fin s → ℕ} (hstep : ∀ i, (e + Pi.single lowest 1 : Fin s → ℕ) i ≤ d i) :
    layerRankPotential e + 1 ≤ layerRankPotential d := by
  have h := layerRankPotential_mono hstep
  simpa only [layerRankPotential_add, layerRankPotential_single, hlowest] using h

theorem layerRankPotential_iteration_bound {s n : ℕ} (d : ℕ → Fin s → ℕ)
    (hstep : ∀ t < n, layerRankPotential (d (t + 1)) + 1 ≤ layerRankPotential (d t)) :
    n + layerRankPotential (d n) ≤ layerRankPotential (d 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun t ht => hstep t (by omega))
    have hlast := hstep n (Nat.lt_succ_self n)
    omega

theorem layerRankPotential_initial {s : ℕ} (D : ℕ) :
    layerRankPotential (Pi.single (Fin.last s) D) = (s + 1) * D :=
  layerRankPotential_single (Fin.last s) D

end Erdos3

end

end OAI
