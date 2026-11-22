import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite replacements: bounded integral chains, deformation certificates, local support bounds

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/08_limits.tex`, for integer coefficient vectors
and finite tables:

* L01 (`thm:finite-currents`, "bounded integral chains on a fixed mesh"): for positive natural weights `a_i` and
  `M₂(T) = ∑ a_i |t_i| ≤ M`, every coefficient satisfies `|t_i| ≤ ⌊M / a_i⌋` (`coef_bound`), so the admissible
  chains lie in the coefficient box of size `∏ (2 ⌊M / a_i⌋ + 1)` (`mem_box`, `card_box`), and `N_M + 1` of them
  contain a repeated chain (`repeat_chain`, "by the finite pigeonhole argument, applied to their positions in the
  unfiltered coefficient box");
* L02 ("finite-scale compactness from deformation certificates"): certificates `T_i − P = A_i + ∂B_i` to the
  same chain `P` subtract to `T_i − T_j = (A_i − A_j) + ∂(B_i − B_j)` (`cert_sub`), with cost at most the sum of
  the two costs (`cost_sub`, "The weighted `ℓ¹` triangle inequality bounds the new cost by the sum of the old
  costs"), and among `N + 1` chains certified to at most `N` chains two share their target (`shared_target`);
* L05 ("local support bounds become a global finite support"): local bounds `b(x)` with
  `j > b(x) → N_x ∩ A_j = ∅` give the global bound `B = max_x b(x)` (`global_support`), and a global bound gives
  all local ones (`local_support`).
-/

namespace LeanProofs.IPRA.Topology.FiniteLimits

/-! ## L01 -/

variable {s : ℕ}

/-- The weighted mass `∑ a_i |t_i|`. -/
def mass (a : Fin s → ℕ) (t : Fin s → ℤ) : ℤ := ∑ i, (a i : ℤ) * |t i|

/-- Every coefficient of a chain of mass at most `M` satisfies `|t_i| ≤ ⌊M / a_i⌋`. -/
theorem coef_bound {a : Fin s → ℕ} (ha : ∀ i, 0 < a i) {t : Fin s → ℤ} {M : ℕ} (h : mass a t ≤ M) (i : Fin s) :
    |t i| ≤ ((M / a i : ℕ) : ℤ) := by
  have hle : (a i : ℤ) * |t i| ≤ M := by
    refine le_trans ?_ h
    exact Finset.single_le_sum (f := fun j => (a j : ℤ) * |t j|)
      (fun j _ => mul_nonneg (by positivity) (abs_nonneg _)) (Finset.mem_univ i)
  have hai : (0 : ℤ) < a i := by exact_mod_cast ha i
  have h1 : |t i| ≤ (M : ℤ) / a i := by
    rw [Int.le_ediv_iff_mul_le hai]
    linarith [_root_.mul_comm (a i : ℤ) |t i|]
  simpa [Int.natCast_div] using h1

/-- The coefficient box `∏_i [−b_i, b_i]`. -/
def box (b : Fin s → ℕ) : Finset (Fin s → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (-(b i : ℤ)) (b i)

theorem mem_box {a : Fin s → ℕ} (ha : ∀ i, 0 < a i) {t : Fin s → ℤ} {M : ℕ} (h : mass a t ≤ M) :
    t ∈ box fun i => M / a i := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  exact abs_le.mp (coef_bound ha h i)

theorem card_box (b : Fin s → ℕ) : (box b).card = ∏ i, (2 * b i + 1) := by
  simp only [box, Fintype.card_piFinset, Int.card_Icc]
  refine Finset.prod_congr rfl fun i _ => ?_
  omega

/-- L01: `N_M + 1` admissible chains contain a repeated chain. -/
theorem repeat_chain {a : Fin s → ℕ} (ha : ∀ i, 0 < a i) {M : ℕ}
    (T : Fin ((box fun i => M / a i).card + 1) → Fin s → ℤ) (hT : ∀ k, mass a (T k) ≤ M) :
    ∃ k l, k ≠ l ∧ T k = T l := by
  obtain ⟨k, -, l, -, hkl, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.univ) (t := box fun i => M / a i) (f := T) (by simp)
    (fun k _ => mem_box ha (hT k))
  exact ⟨k, l, hkl, h⟩

/-! ## L02 -/

variable {q : ℕ}

/-- `T_i − P = A_i + ∂B_i` and `T_j − P = A_j + ∂B_j` give `T_i − T_j = (A_i − A_j) + ∂(B_i − B_j)`. -/
theorem cert_sub (d : (Fin q → ℤ) →+ (Fin s → ℤ)) {Ti Tj P Ai Aj : Fin s → ℤ} {Bi Bj : Fin q → ℤ}
    (hi : Ti - P = Ai + d Bi) (hj : Tj - P = Aj + d Bj) : Ti - Tj = (Ai - Aj) + d (Bi - Bj) := by
  rw [map_sub]
  have : Ti - Tj = (Ti - P) - (Tj - P) := by abel
  rw [this, hi, hj]
  abel

/-- The cost of the difference certificate is at most the sum of the two costs. -/
theorem cost_sub (w : Fin s → ℕ) (v : Fin q → ℕ) (Ai Aj : Fin s → ℤ) (Bi Bj : Fin q → ℤ) :
    mass w (Ai - Aj) + mass v (Bi - Bj) ≤ (mass w Ai + mass v Bi) + (mass w Aj + mass v Bj) := by
  have hA : mass w (Ai - Aj) ≤ mass w Ai + mass w Aj := by
    unfold mass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← _root_.mul_add]
    exact mul_le_mul_of_nonneg_left (abs_sub (Ai i) (Aj i)) (by positivity)
  have hB : mass v (Bi - Bj) ≤ mass v Bi + mass v Bj := by
    unfold mass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← _root_.mul_add]
    exact mul_le_mul_of_nonneg_left (abs_sub (Bi i) (Bj i)) (by positivity)
  linarith

/-- Among `N + 1` chains certified to targets in a set of at most `N` chains, two share their target. -/
theorem shared_target {α : Type*} [DecidableEq α] (S : Finset α) (P : Fin (S.card + 1) → α)
    (hP : ∀ k, P k ∈ S) : ∃ k l, k ≠ l ∧ P k = P l := by
  obtain ⟨k, -, l, -, hkl, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.univ) (t := S) (f := P) (by simp) (fun k _ => hP k)
  exact ⟨k, l, hkl, h⟩

/-! ## L05 -/

variable {k : ℕ}

/-- L05: local support bounds give the global bound `max_x b(x)`. -/
theorem global_support {rel : Fin k → Fin k → Prop} (hrefl : ∀ x, rel x x) (A : ℕ → Fin k → Prop)
    (b : Fin k → ℕ) (hloc : ∀ x j, b x < j → ∀ y, rel x y → ¬ A j y) {j : ℕ}
    (hj : Finset.univ.sup b < j) : ∀ y, ¬ A j y :=
  fun y => hloc y j (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ y)) hj) y (hrefl y)

/-- Conversely, a global support bound gives every local bound. -/
theorem local_support {rel : Fin k → Fin k → Prop} (A : ℕ → Fin k → Prop) {B : ℕ}
    (hglob : ∀ j, B < j → ∀ y, ¬ A j y) : ∀ x j, B < j → ∀ y, rel x y → ¬ A j y :=
  fun _ j hj y _ => hglob j hj y

end LeanProofs.IPRA.Topology.FiniteLimits
