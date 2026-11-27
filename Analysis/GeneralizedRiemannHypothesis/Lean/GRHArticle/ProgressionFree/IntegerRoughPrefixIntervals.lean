import GRHArticle.ProgressionFree.IntegerPrefixTransfer
import GRHArticle.ProgressionFree.Density

/-!
# Rough intervals of one smooth budget

The rough parts that leave exactly budget `k` in the prefix at `N` are those
in `(N/(k+1), N/k]`. Their normalized count tends to the rough density times
`1/(k*(k+1))`.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- The rough parts from `Q` that leave quotient exactly `k` at cutoff `N`. -/
noncomputable def integerRoughBudgetSlice (Q : Set ℕ) (N k : ℕ) : Finset ℕ :=
  integerPrefixSlice Q (N/k) \ integerPrefixSlice Q (N/(k+1))

theorem mem_integerRoughBudgetSlice {Q : Set ℕ} {N k g : ℕ} :
    g ∈ integerRoughBudgetSlice Q N k ↔
      g ∈ Q ∧ N/(k+1) < g ∧ g ≤ N/k := by
  simp only [integerRoughBudgetSlice, Finset.mem_sdiff, integerPrefixSlice, Finset.mem_filter,
    integerPrefix, mem_Icc]
  constructor
  · rintro ⟨⟨⟨hg₀, hg⟩, hQ⟩, hnot⟩
    exact ⟨hQ, Nat.lt_of_not_ge (fun hl ↦ hnot ⟨⟨hg₀,hl⟩,hQ⟩), hg⟩
  · rintro ⟨hQ, hl, hu⟩
    exact ⟨⟨⟨Nat.succ_le_of_lt (Nat.zero_lt_of_lt hl), hu⟩, hQ⟩, fun hs ↦ hl.not_ge hs.1.2⟩

theorem div_eq_of_mem_integerRoughBudgetSlice {Q : Set ℕ} {N k g : ℕ}
    (hk : 0 < k) (hg : g ∈ integerRoughBudgetSlice Q N k) : N/g = k := by
  obtain ⟨_, hl, hu⟩ := mem_integerRoughBudgetSlice.mp hg
  have hg₀ : 0 < g := Nat.zero_lt_of_lt hl
  have h₁ := (Nat.le_div_iff_mul_le hk).mp hu
  have h₂ := (Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).mp hl
  have h₁' := (Nat.le_div_iff_mul_le hg₀).mpr (by simpa only [mul_comm] using h₁ : k*g ≤ N)
  have h₂' := (Nat.div_lt_iff_lt_mul hg₀).mpr (by simpa only [mul_comm] using h₂ : N < (k+1)*g)
  omega

private theorem integerPrefixSlice_mono (Q : Set ℕ) {m n : ℕ} (h : m ≤ n) :
    integerPrefixSlice Q m ⊆ integerPrefixSlice Q n := by
  intro g hg
  simp only [integerPrefixSlice, Finset.mem_filter, integerPrefix, mem_Icc] at hg ⊢
  exact ⟨⟨hg.1.1, hg.1.2.trans h⟩, hg.2⟩

private theorem integerRoughBudgetSlice_card_real (Q : Set ℕ) (N k : ℕ) (hk : 0 < k) :
    ((integerRoughBudgetSlice Q N k).card : ℝ) =
      (countUpTo Q (N/k) : ℝ) - (countUpTo Q (N/(k+1)) : ℝ) := by
  have hdiv : N/(k+1) ≤ N/k := Nat.div_le_div_left (Nat.le_succ k) hk
  have h := integerPrefixSlice_mono Q hdiv
  rw [integerRoughBudgetSlice, Finset.card_sdiff_of_subset h,
    Nat.cast_sub (Finset.card_le_card h)]
  rfl

/-- The density contribution of one fixed positive dilation. -/
theorem tendsto_countUpTo_div_cutoff {Q : Set ℕ} {d : ℝ} (hQ : HasNaturalDensity Q d)
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ ↦ (countUpTo Q (N/k) : ℝ) / (N : ℝ)) atTop (𝓝 (d / (k : ℝ))) := by
  have hratio : Tendsto (fun N : ℕ ↦ ((N/k : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := by
    have h := hasNaturalDensity_dvd k hk
    change Tendsto (fun N : ℕ ↦ (countUpTo {n | k ∣ n} N : ℝ) / (N : ℝ)) atTop _ at h
    simpa only [countUpTo_dvd k _ hk] using h
  have h := (hQ.comp (Nat.tendsto_div_const_atTop hk.ne')).mul hratio
  rw [mul_one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hNk
  have hquot : 0 < N/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa only [one_mul] using hNk : 1*k ≤ N)
  have hquot₀ : (((N/k : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hquot.ne'
  change ((countUpTo Q (N/k) : ℝ) / ((N/k : ℕ) : ℝ)) * (((N/k : ℕ) : ℝ) / (N : ℝ)) = _
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hquot₀ (by exact_mod_cast (hk.trans_le hNk).ne'))
    (by exact_mod_cast (hk.trans_le hNk).ne')]
  ring

/-- The normalized size of the rough kernel interval converges to its
contribution to the discrete smooth sum. -/
theorem tendsto_integerRoughBudgetSlice_card_div {Q : Set ℕ} {d : ℝ} (hQ : HasNaturalDensity Q d)
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ ↦ ((integerRoughBudgetSlice Q N k).card : ℝ) / (N : ℝ))
      atTop (𝓝 (d * integerPrefixStepWeight k)) := by
  have h := (tendsto_countUpTo_div_cutoff hQ hk).sub (tendsto_countUpTo_div_cutoff hQ (Nat.succ_pos k))
  have hcasting : d / (k : ℝ) - d / ((k+1 : ℕ) : ℝ) = d * integerPrefixStepWeight k := by
    have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    unfold integerPrefixStepWeight
    push_cast
    field_simp [hk₀]
    ring
  rw [hcasting] at h
  refine h.congr (fun N ↦ ?_)
  rw [integerRoughBudgetSlice_card_real Q N k hk, sub_div]

end GRHArticle.ProgressionFree
