import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The finite prism identity of contiguous simplicial maps

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Proposition A19
(`prop:simplicial-prism`): for vertex maps `f, g`,
`P[v_0, …, v_k] = ∑_{i=0}^{k} (−1)^i [f(v_0), …, f(v_i), g(v_i), …, g(v_k)]` satisfies
`∂P + P∂ = g_# − f_#`.

Ordered tuples are sequences `σ : ℕ → V` (only the first `k + 1` entries matter), the `j`-th face deletes entry
`j` (`face`), and `prism f g i σ` is the `i`-th prism tuple `[f σ_0, …, f σ_i, g σ_i, g σ_{i+1}, …]`. Chains are
evaluated by an arbitrary additive `φ` (into any abelian group) depending only on the first `k + 1` entries:

* `face_prism_lt`, `face_prism_gt`: "Deleting an `f(v_j)` with `j < i`, or a `g(v_j)` with `j > i`, pairs with the
  prism summand for the face omitting `v_j`";
* `face_prism_diag`: "deleting the last `f`-vertex in one summand cancels deleting the first `g`-vertex in the
  preceding summand";
* `face_zero_prism`, `face_last_prism`: "The first and last unpaired terms are respectively
  `[g(v_0), …, g(v_k)]` and `−[f(v_0), …, f(v_k)]`";
* `prism_identity`: `∂P(σ) + P(∂σ) = g_#σ − f_#σ`, as an identity of finite signed sums.
-/

namespace LeanProofs.IPRA.Topology.PrismIdentity

open Finset

variable {α V W M : Type*} [AddCommGroup M]

/-- Deleting entry `j`. -/
def face (j : ℕ) (σ : ℕ → α) : ℕ → α := fun m => if m < j then σ m else σ (m + 1)

/-- The `i`-th prism tuple `[f σ_0, …, f σ_i, g σ_i, …]`. -/
def prism (f g : V → W) (i : ℕ) (σ : ℕ → V) : ℕ → W := fun m => if m ≤ i then f (σ m) else g (σ (m - 1))

variable (f g : V → W)

theorem face_prism_lt {i j : ℕ} (h : j < i + 1) (σ : ℕ → V) :
    face j (prism f g (i + 1) σ) = prism f g i (face j σ) := by
  funext m
  simp only [face, prism]
  split_ifs <;> first | rfl | omega | (congr 2; omega)

theorem face_prism_gt {i l : ℕ} (h : i < l) (σ : ℕ → V) :
    face (l + 1) (prism f g i σ) = prism f g i (face l σ) := by
  funext m
  simp only [face, prism]
  split_ifs <;> first | rfl | omega | (congr 2; omega)

theorem face_prism_diag (i : ℕ) (σ : ℕ → V) :
    face (i + 1) (prism f g (i + 1) σ) = face (i + 1) (prism f g i σ) := by
  funext m
  simp only [face, prism]
  split_ifs <;> first | rfl | omega | (congr 2; omega)

theorem face_zero_prism (σ : ℕ → V) : face 0 (prism f g 0 σ) = g ∘ σ := by
  funext m
  simp [face, prism]

theorem face_last_prism (k : ℕ) (σ : ℕ → V) {m : ℕ} (hm : m < k + 1) :
    face (k + 1) (prism f g (k + 1) σ) m = f (σ m) := by
  simp [face, prism, hm, show m ≤ k + 1 by omega]

/-- A19: `∂P + P∂ = g_# − f_#` on a `k`-simplex. -/
theorem prism_identity (k : ℕ) (φ : (ℕ → W) → M)
    (hφ : ∀ σ τ : ℕ → W, (∀ m < k + 1, σ m = τ m) → φ σ = φ τ) (σ : ℕ → V) :
    (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2), ((-1 : ℤ) ^ (i + j)) • φ (face j (prism f g i σ))) +
      ∑ l ∈ range (k + 1), ∑ i ∈ range k, ((-1 : ℤ) ^ (l + i)) • φ (prism f g i (face l σ)) =
    φ (g ∘ σ) - φ (f ∘ σ) := by
  have hsplit : ∀ i ∈ range (k + 1),
      ∑ j ∈ range (k + 2), ((-1 : ℤ) ^ (i + j)) • φ (face j (prism f g i σ)) =
        (∑ j ∈ range i, ((-1 : ℤ) ^ (i + j)) • φ (face j (prism f g i σ))) +
          (φ (face i (prism f g i σ)) - φ (face (i + 1) (prism f g (i + 1) σ))) -
          ∑ l ∈ Ico (i + 1) (k + 1), ((-1 : ℤ) ^ (l + i)) • φ (prism f g i (face l σ)) := by
    intro i hi
    rw [mem_range] at hi
    rw [← sum_range_add_sum_Ico _ (show i ≤ k + 2 by omega), sum_eq_sum_Ico_succ_bot (show i < k + 2 by omega),
      sum_eq_sum_Ico_succ_bot (show i + 1 < k + 2 by omega)]
    have e₁ : ((-1 : ℤ) ^ (i + i)) = 1 := by rw [← two_mul, pow_mul]; norm_num
    have e₂ : ((-1 : ℤ) ^ (i + (i + 1))) = -1 := by
      rw [show i + (i + 1) = 2 * i + 1 by ring, pow_succ, pow_mul]; norm_num
    have e₃ : ∑ j ∈ Ico (i + 1 + 1) (k + 2), ((-1 : ℤ) ^ (i + j)) • φ (face j (prism f g i σ)) =
        -∑ l ∈ Ico (i + 1) (k + 1), ((-1 : ℤ) ^ (l + i)) • φ (prism f g i (face l σ)) := by
      rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, show k + 2 - (i + 1 + 1) = k + 1 - (i + 1) by omega,
        ← sum_neg_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [show i + 1 + 1 + x = (i + 1 + x) + 1 by ring, face_prism_gt f g (show i < i + 1 + x by omega)]
      have hs : ((-1 : ℤ) ^ (i + (i + 1 + x + 1))) = -((-1 : ℤ) ^ (i + 1 + x + i)) := by ring
      rw [hs, neg_zsmul]
    rw [e₃, e₁, e₂, one_zsmul, neg_zsmul, one_zsmul, face_prism_diag]
    abel
  have htel : ∑ i ∈ range (k + 1),
      (φ (face i (prism f g i σ)) - φ (face (i + 1) (prism f g (i + 1) σ))) =
      φ (face 0 (prism f g 0 σ)) - φ (face (k + 1) (prism f g (k + 1) σ)) :=
    sum_range_sub' (fun i => φ (face i (prism f g i σ))) (k + 1)
  have h₁ : ∑ i ∈ range (k + 1), ∑ j ∈ range i, ((-1 : ℤ) ^ (i + j)) • φ (face j (prism f g i σ)) =
      -∑ i ∈ range k, ∑ j ∈ range (i + 1), ((-1 : ℤ) ^ (j + i)) • φ (prism f g i (face j σ)) := by
    rw [sum_range_succ', sum_range_zero, add_zero, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [face_prism_lt f g hj]
    have hs : ((-1 : ℤ) ^ (i + 1 + j)) = -((-1 : ℤ) ^ (j + i)) := by ring
    rw [hs, neg_zsmul]
  have h₃ : ∑ i ∈ range (k + 1), ∑ l ∈ Ico (i + 1) (k + 1), ((-1 : ℤ) ^ (l + i)) • φ (prism f g i (face l σ)) =
      ∑ i ∈ range k, ∑ l ∈ Ico (i + 1) (k + 1), ((-1 : ℤ) ^ (l + i)) • φ (prism f g i (face l σ)) := by
    rw [sum_range_succ, Ico_self, sum_empty, add_zero]
  have h₁₃ : (∑ i ∈ range k, ∑ j ∈ range (i + 1), ((-1 : ℤ) ^ (j + i)) • φ (prism f g i (face j σ))) +
      ∑ i ∈ range k, ∑ l ∈ Ico (i + 1) (k + 1), ((-1 : ℤ) ^ (l + i)) • φ (prism f g i (face l σ)) =
      ∑ l ∈ range (k + 1), ∑ i ∈ range k, ((-1 : ℤ) ^ (l + i)) • φ (prism f g i (face l σ)) := by
    rw [← sum_add_distrib, sum_comm (s := range (k + 1))]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    exact sum_range_add_sum_Ico _ (by omega)
  have hlast : φ (face (k + 1) (prism f g (k + 1) σ)) = φ (f ∘ σ) :=
    hφ _ _ fun m hm => face_last_prism f g k σ hm
  rw [sum_congr rfl hsplit, sum_sub_distrib, sum_add_distrib, htel, h₁, h₃, face_zero_prism, hlast, ← h₁₃]
  abel

end LeanProofs.IPRA.Topology.PrismIdentity
