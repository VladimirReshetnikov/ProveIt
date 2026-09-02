import FabiusFunction.GeometricSimplexSum

/-!
# The geometric simplex sum over strictly increasing sequences

`GeometricSimplexSum` evaluates `∑ q^{∑_h j_h r_h}` over the increment parametrization
`j_h = ∑_{k ≤ h} (i_k + 1)`.  Here we show that this parametrization is a bijection from
`Fin ℓ → ℕ` onto the strictly increasing sequences `1 ≤ j_1 < ⋯ < j_ℓ`
(`prefixSum_injective`, `prefixSum_surjective`), and transport the sum:

`∑_{1 ≤ j_1 < ⋯ < j_ℓ} q^{j_1 r_1 + ⋯ + j_ℓ r_ℓ} = ∏_h q^{t_h}/(1 - q^{t_h})`.

## Main declarations

* `prefixSum`, `prefixSum_strictMono`, `prefixSum_pos`, `prefixSum_injective`,
  `prefixSum_surjective`.
* `hasSum_geometric_simplex`: the geometric simplex sum over strictly increasing sequences.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The prefix sums `j_h = ∑_{k ≤ h} (i_k + 1)` of a sequence of increments. -/
def prefixSum {ℓ : ℕ} (i : Fin ℓ → ℕ) (h : Fin ℓ) : ℕ := ∑ k, if k ≤ h then i k + 1 else 0

theorem prefixSum_zero {ℓ : ℕ} (i : Fin (ℓ + 1) → ℕ) : prefixSum i 0 = i 0 + 1 := by
  unfold prefixSum
  rw [Fin.sum_univ_succ, if_pos le_rfl,
    sum_eq_zero fun k _ => if_neg (not_le.mpr (Fin.succ_pos k)), add_zero]

theorem prefixSum_succ {ℓ : ℕ} (i : Fin (ℓ + 1) → ℕ) (h : Fin ℓ) :
    prefixSum i h.succ = prefixSum i h.castSucc + (i h.succ + 1) := by
  unfold prefixSum
  have hsplit : ∀ k : Fin (ℓ + 1), (if k ≤ h.succ then i k + 1 else 0) =
      (if k ≤ h.castSucc then i k + 1 else 0) + (if k = h.succ then i k + 1 else 0) := by
    intro k
    by_cases hk : k = h.succ
    · subst hk
      rw [if_pos le_rfl, if_neg (not_le.mpr (Fin.castSucc_lt_succ (i := h))), if_pos rfl, zero_add]
    · rw [if_neg hk, add_zero]
      have : k ≤ h.succ ↔ k ≤ h.castSucc := by
        rw [Fin.le_castSucc_iff]
        exact ⟨fun h1 => lt_of_le_of_ne h1 hk, le_of_lt⟩
      by_cases hk2 : k ≤ h.castSucc
      · rw [if_pos (this.mpr hk2), if_pos hk2]
      · rw [if_neg (fun h1 => hk2 (this.mp h1)), if_neg hk2]
  simp_rw [hsplit]
  rw [sum_add_distrib, sum_ite_eq' univ h.succ]
  simp

theorem prefixSum_pos {ℓ : ℕ} (i : Fin ℓ → ℕ) (h : Fin ℓ) : 0 < prefixSum i h := by
  unfold prefixSum
  refine lt_of_lt_of_le (Nat.succ_pos (i h)) ?_
  have := single_le_sum (s := univ) (f := fun k => if k ≤ h then i k + 1 else 0)
    (fun _ _ => by positivity) (mem_univ h)
  simpa using this

theorem prefixSum_castSucc_lt_succ {ℓ : ℕ} (i : Fin (ℓ + 1) → ℕ) (h : Fin ℓ) :
    prefixSum i h.castSucc < prefixSum i h.succ := by
  rw [prefixSum_succ]
  omega

theorem prefixSum_strictMono {ℓ : ℕ} (i : Fin ℓ → ℕ) : StrictMono (prefixSum i) := by
  rcases ℓ with _ | ℓ
  · exact fun a => a.elim0
  · exact Fin.strictMono_iff_lt_succ.mpr fun h => prefixSum_castSucc_lt_succ i h

theorem prefixSum_injective {ℓ : ℕ} : Function.Injective (prefixSum (ℓ := ℓ)) := by
  rcases ℓ with _ | ℓ
  · intro i i' _
    funext h
    exact h.elim0
  · intro i i' hii'
    funext h
    induction h using Fin.induction with
    | zero =>
      have := congrFun hii' 0
      rw [prefixSum_zero, prefixSum_zero] at this
      omega
    | succ h ih =>
      have h1 := congrFun hii' h.succ
      have h2 := congrFun hii' h.castSucc
      rw [prefixSum_succ, prefixSum_succ] at h1
      rw [h2] at h1
      omega

theorem prefixSum_surjective {ℓ : ℕ} (j : Fin ℓ → ℕ) (hj : StrictMono j) (hpos : ∀ h, 0 < j h) :
    ∃ i, prefixSum i = j := by
  rcases ℓ with _ | ℓ
  · exact ⟨fun h => h.elim0, funext fun h => h.elim0⟩
  · refine ⟨Fin.cons (j 0 - 1) (fun h => j h.succ - j h.castSucc - 1), funext fun h => ?_⟩
    induction h using Fin.induction with
    | zero =>
      rw [prefixSum_zero, Fin.cons_zero]
      have := hpos 0
      omega
    | succ h ih =>
      rw [prefixSum_succ, ih, Fin.cons_succ]
      have := hj (Fin.castSucc_lt_succ (i := h))
      omega

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The geometric simplex sum**: for `‖q‖ < 1` and positive `r_1, …, r_ℓ` with tail sums
`t_h = r_h + ⋯ + r_ℓ`, `∑_{1 ≤ j_1 < ⋯ < j_ℓ} q^{j_1 r_1 + ⋯ + j_ℓ r_ℓ} = ∏_h q^{t_h}/(1 - q^{t_h})`,
the sum running over the strictly increasing positive sequences `j : Fin ℓ → ℕ`. -/
theorem hasSum_geometric_simplex {q : 𝕜} (hq : ‖q‖ < 1) {ℓ : ℕ} (r : Fin ℓ → ℕ)
    (hr : ∀ h, 0 < r h) :
    HasSum (fun j : {j : Fin ℓ → ℕ // StrictMono j ∧ ∀ h, 0 < j h} => q ^ (∑ h, j.1 h * r h))
      (∏ h, q ^ tailSum r h / (1 - q ^ tailSum r h)) := by
  set S : Set (Fin ℓ → ℕ) := {j | StrictMono j ∧ ∀ h, 0 < j h} with hS
  set f : (Fin ℓ → ℕ) → 𝕜 := fun j => q ^ (∑ h, j h * r h) with hf
  have hrange : Set.range (prefixSum (ℓ := ℓ)) = S := by
    ext j
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨prefixSum_strictMono i, prefixSum_pos i⟩
    · rintro ⟨hj, hpos⟩
      exact prefixSum_surjective j hj hpos
  have h1 := hasSum_geometric_simplex_increments hq r hr
  have h2 : HasSum (S.indicator f ∘ prefixSum) (∏ h, q ^ tailSum r h / (1 - q ^ tailSum r h)) := by
    refine h1.congr_fun fun i => ?_
    rw [Function.comp_apply, Set.indicator_of_mem (hrange ▸ Set.mem_range_self i)]
    rfl
  rw [prefixSum_injective.hasSum_iff (fun j hj => Set.indicator_of_notMem (hrange ▸ hj) f)] at h2
  rw [← hasSum_subtype_iff_indicator] at h2
  exact h2

end Fabius
