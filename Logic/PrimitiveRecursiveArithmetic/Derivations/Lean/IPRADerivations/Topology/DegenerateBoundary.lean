import Mathlib.Algebra.Module.NatInt
import IPRADerivations.Topology.PrismIdentity

/-!
# The boundary of a degenerate tuple vanishes under an alternating functional

Packet: `topology/hairy_ball_ipra`, `sections/degree.tex`, "Oriented chains": "A tuple `[v_0, …, v_p]` changes
sign under a transposition and denotes zero if two entries coincide … If the image has repeated entries,
choose two equal entries in positions `a < b`. All deletion terms except possibly `a, b` still have a repeat.
The two exceptional lists differ by moving one entry across `b − a − 1` others. Their orientation signs,
combined with their deletion signs, cancel." This is the hypothesis `hdegen` of
`Topology/AntipodalObstruction` (S04 of `general_topology_ipra_2026-11-19`): a prism tuple in a target of
lower dimension has a repeated vertex.

Tuples are sequences `τ : ℕ → W`; `φ` reads the first `K` entries, changes sign under the adjacent
transpositions `swapAt a` (`a + 1 < K`) and vanishes on tuples with two equal entries among the first `K`.

* `face_swap_last`, `face_swap_lt`: deleting an entry commutes with an adjacent transposition, up to the shift
  of positions;
* `face_adjacent`: if `τ p = τ (p + 1)`, deleting either of the two gives the same tuple;
* `face_repeat`: if `τ p = τ (p + d + 1)` then `φ(∂_p τ) = (−1)^d φ(∂_{p+d+1} τ)`;
* `degenerate_boundary`: `∑_j (−1)^j φ(∂_j τ) = 0` for a tuple with a repeated entry.
-/

namespace LeanProofs.IPRA.Topology.DegenerateBoundary

open Finset
open LeanProofs.IPRA.Topology.PrismIdentity (face)

variable {W M : Type*} [AddCommGroup M]

/-- Exchange the entries at positions `a` and `a + 1`. -/
def swapAt (a : ℕ) (τ : ℕ → W) : ℕ → W :=
  fun m => if m = a then τ (a + 1) else if m = a + 1 then τ a else τ m

theorem face_swap_last (q : ℕ) (τ : ℕ → W) : face q (swapAt q τ) = face (q + 1) τ := by
  funext m
  simp only [face, swapAt]
  split_ifs <;> first | rfl | (congr 1; omega) | omega

theorem face_swap_lt {p a : ℕ} (h : p ≤ a) (τ : ℕ → W) :
    face p (swapAt (a + 1) τ) = swapAt a (face p τ) := by
  funext m
  simp only [face, swapAt]
  split_ifs <;> first | rfl | (congr 1; omega) | omega

theorem face_adjacent {p : ℕ} {τ : ℕ → W} (h : τ p = τ (p + 1)) : face p τ = face (p + 1) τ := by
  funext m
  simp only [face]
  split_ifs with h₁ h₂ h₂
  · rfl
  · omega
  · have e : m = p := by omega
    subst e
    exact h.symm
  · rfl

/-- Moving the repeated entry across `d` others: `φ(∂_p τ) = (−1)^d φ(∂_{p+d+1} τ)`. -/
theorem face_repeat (φ : (ℕ → W) → M) (K : ℕ)
    (halt : ∀ (τ : ℕ → W) (a : ℕ), a + 1 < K → φ (swapAt a τ) = -φ τ) :
    ∀ (d p : ℕ) (τ : ℕ → W), p + d + 1 < K + 1 → τ p = τ (p + d + 1) →
      φ (face p τ) = ((-1 : ℤ) ^ d) • φ (face (p + d + 1) τ)
  | 0, p, τ, _, h => by
    rw [face_adjacent h, pow_zero, one_smul]
  | d + 1, p, τ, hK, h => by
    have e₁ : swapAt (p + d + 1) τ p = τ p := by
      simp only [swapAt]
      rw [if_neg (show ¬ (p = p + d + 1) by omega), if_neg (show ¬ (p = p + d + 1 + 1) by omega)]
    have e₂ : swapAt (p + d + 1) τ (p + d + 1) = τ (p + d + 1 + 1) := by
      simp [swapAt]
    have h' : swapAt (p + d + 1) τ p = swapAt (p + d + 1) τ (p + d + 1) := by
      rw [e₁, e₂]
      exact h
    have ih := face_repeat φ K halt d p (swapAt (p + d + 1) τ) (by omega) h'
    rw [face_swap_last, face_swap_lt (show p ≤ p + d by omega),
      halt (face p τ) (p + d) (by omega)] at ih
    rw [show p + (d + 1) + 1 = p + d + 1 + 1 by omega, pow_succ, mul_comm, mul_smul, ← ih]
    simp

/-- The boundary of a tuple with a repeated entry vanishes under `φ`. -/
theorem degenerate_boundary (φ : (ℕ → W) → M) (K : ℕ)
    (halt : ∀ (τ : ℕ → W) (a : ℕ), a + 1 < K → φ (swapAt a τ) = -φ τ)
    (hrep : ∀ (τ : ℕ → W) (a b : ℕ), a < b → b < K → τ a = τ b → φ τ = 0)
    (τ : ℕ → W) {p q : ℕ} (hpq : p < q) (hq : q < K + 1) (h : τ p = τ q) :
    ∑ j ∈ range (K + 1), ((-1 : ℤ) ^ j) • φ (face j τ) = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, q = p + d + 1 := ⟨q - p - 1, by omega⟩
  have hz : ∀ j ∈ range (K + 1), j ≠ p ∧ j ≠ p + d + 1 → ((-1 : ℤ) ^ j) • φ (face j τ) = 0 := by
    intro j hj hne
    rw [mem_range] at hj
    have hφ0 : φ (face j τ) = 0 := by
      rcases Nat.lt_or_ge j p with hjp | hjp
      · refine hrep _ (p - 1) (p + d) (by omega) (by omega) ?_
        simp only [face]
        rw [if_neg (show ¬ (p - 1 < j) by omega), if_neg (show ¬ (p + d < j) by omega),
          show p - 1 + 1 = p by omega]
        exact h
      · rcases Nat.lt_or_ge j (p + d + 1) with hjq | hjq
        · refine hrep _ p (p + d) (by omega) (by omega) ?_
          simp only [face]
          rw [if_pos (show p < j by omega), if_neg (show ¬ (p + d < j) by omega)]
          exact h
        · refine hrep _ p (p + d + 1) (by omega) (by omega) ?_
          simp only [face]
          rw [if_pos (show p < j by omega), if_pos (show p + d + 1 < j by omega)]
          exact h
    rw [hφ0, smul_zero]
  rw [sum_eq_add p (p + d + 1) (by omega) hz (fun hp => absurd (mem_range.mpr (by omega)) hp)
    (fun hp => absurd (mem_range.mpr (by omega)) hp)]
  rw [face_repeat φ K halt d p τ hq h, ← mul_smul, pow_add, pow_add, pow_one, ← add_smul]
  have e : (-1 : ℤ) ^ p * (-1) ^ d + (-1) ^ p * (-1) ^ d * -1 = 0 := by ring
  rw [e, zero_smul]

end LeanProofs.IPRA.Topology.DegenerateBoundary
