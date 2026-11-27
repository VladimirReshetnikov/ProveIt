import GRHArticle.ProgressionFree.IntegerBlockGluing
import GRHArticle.ProgressionFree.IntegerPrimeSquareTail
import GRHArticle.ProgressionFree.IntegerRoughOptimalPrefix
import GRHArticle.ProgressionFree.IntegerRoughPrefixIntervals

/-!
# A lower bound for extremal integer upper density from smooth optimizers

At each cutoff the interval of rough parts with budget `k` contributes a
copy of the optimizer for `k` for every retained rough factor. After imposing
squarefreeness, the finite prefixes are admissible and can be glued.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- Squarefree positive integers with every prime factor larger than `Y`. -/
def integerSquarefreeRoughNumbers (Y : ℕ) : Set ℕ :=
  {r | r ∈ integerRoughNumbers Y ∧ Squarefree r}

private theorem count_integerRoughOptimalPrefix_ge (integral : Bool) (Y N M : ℕ)
    {Q : Set ℕ} (hQ : Q ⊆ integerRoughNumbers Y) :
    (∑ k ∈ integerPrefix M,
      (integerRoughBudgetSlice Q N k).card * integerSmoothPrefixMaximum integral Y k) ≤
      countUpTo (integerRoughOptimalPrefix integral Y Q N) N := by
  let D := (integerPrefix M).sigma fun k ↦
    integerRoughBudgetSlice Q N k ×ˢ integerSmoothPrefixOptimizer integral Y k
  let product (z : Σ _ : ℕ, ℕ × ℕ) := z.2.1 * z.2.2
  have hcard : D.card ≤ countUpTo (integerRoughOptimalPrefix integral Y Q N) N := by
    unfold countUpTo
    apply Finset.card_le_card_of_injOn product
    · rintro ⟨k,g,s⟩ hz
      obtain ⟨hk, hz⟩ := Finset.mem_sigma.mp hz
      obtain ⟨hg, hs⟩ := Finset.mem_product.mp hz
      have hkp : 0 < k := (mem_Icc.mp hk).1
      obtain ⟨hgQ, _, hgN⟩ := mem_integerRoughBudgetSlice.mp hg
      have hprodN := (Nat.mul_le_mul_left g (mem_smooth_of_mem_integerSmoothPrefixOptimizer hs).1.2).trans
        ((Nat.le_div_iff_mul_le hkp).mp hgN)
      have hp := Nat.mul_pos (Nat.pos_of_ne_zero (hQ hgQ).1)
        (mem_smooth_of_mem_integerSmoothPrefixOptimizer hs).1.1
      refine Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨hp,hprodN⟩, g,s,hgQ,?_ ,rfl⟩
      rwa [div_eq_of_mem_integerRoughBudgetSlice hkp hg]
    · rintro ⟨k,g,s⟩ hz ⟨k',g',s'⟩ hz' he
      obtain ⟨hk, hz⟩ := Finset.mem_sigma.mp hz
      obtain ⟨hk', hz'⟩ := Finset.mem_sigma.mp hz'
      obtain ⟨hg, hs⟩ := Finset.mem_product.mp hz
      obtain ⟨hg', hs'⟩ := Finset.mem_product.mp hz'
      have hleft := hQ (mem_integerRoughBudgetSlice.mp hg).1
      have hright := hQ (mem_integerRoughBudgetSlice.mp hg').1
      have he' : g*s = g'*s' := he
      have hgg := congrArg (integerRoughPart Y) he'
      rw [integerRoughPart_mul_of_parts hleft (mem_smooth_of_mem_integerSmoothPrefixOptimizer hs).2,
        integerRoughPart_mul_of_parts hright (mem_smooth_of_mem_integerSmoothPrefixOptimizer hs').2] at hgg
      change g = g' at hgg
      subst g'
      have hss := Nat.mul_left_cancel (Nat.pos_of_ne_zero hleft.1) he'
      subst s'
      have hkk := (div_eq_of_mem_integerRoughBudgetSlice (mem_Icc.mp hk).1 hg).symm.trans
        (div_eq_of_mem_integerRoughBudgetSlice (mem_Icc.mp hk').1 hg')
      change k = k' at hkk
      subst k'
      rfl
  simpa only [D, Finset.card_sigma, Finset.card_product,
    show ∀ k, (integerSmoothPrefixOptimizer integral Y k).card =
      integerSmoothPrefixMaximum integral Y k from fun k ↦ (integerSmoothPrefixOptimizer_spec integral Y k).2.2] using hcard

private theorem proportion_integerRoughOptimalPrefix_ge (integral : Bool) (Y N M : ℕ)
    {Q : Set ℕ} (hQ : Q ⊆ integerRoughNumbers Y) :
    (∑ k ∈ integerPrefix M,
      ((integerRoughBudgetSlice Q N k).card / (N : ℝ)) * integerSmoothPrefixMaximum integral Y k) ≤
      densityUpTo (integerRoughOptimalPrefix integral Y Q N) N := by
  have hcount := count_integerRoughOptimalPrefix_ge integral Y N M hQ
  unfold densityUpTo
  calc
    _ = ((↑(∑ k ∈ integerPrefix M,
        (integerRoughBudgetSlice Q N k).card * integerSmoothPrefixMaximum integral Y k) : ℝ) / (N : ℝ)) := by
      simp only [Nat.cast_sum, Nat.cast_mul, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg N)

private theorem summable_smooth_optimum_weights (integral : Bool) (Y : ℕ) :
    Summable (fun k ↦ (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k) := by
  have hs := (integerPrefix_hasSum_stepWeight (Nat.smoothNumbers (Y+1))
    (fun _ h ↦ Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers h))
    (summable_reciprocal_smoothNumbers Y)).summable
  apply Summable.of_nonneg_of_le (fun k ↦ by unfold integerPrefixStepWeight; positivity) _ hs
  intro k
  apply mul_le_mul_of_nonneg_right _ (by unfold integerPrefixStepWeight; positivity)
  have hc := Finset.card_le_card (integerSmoothPrefixOptimizer_spec integral Y k).1
  rw [(integerSmoothPrefixOptimizer_spec integral Y k).2.2] at hc
  exact_mod_cast hc

private theorem tendsto_rough_prefix_partial (integral : Bool) (Y M : ℕ)
    {Q : Set ℕ} {d : ℝ} (hQ : HasNaturalDensity Q d) :
    Tendsto (fun N : ℕ ↦ ∑ k ∈ integerPrefix M,
      ((integerRoughBudgetSlice Q N k).card / (N : ℝ)) * integerSmoothPrefixMaximum integral Y k)
      atTop (𝓝 (d * ∑ k ∈ integerPrefix M,
        (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k)) := by
  rw [Finset.mul_sum]
  apply tendsto_finsetSum
  intro k hk
  simpa only [mul_assoc, mul_comm (integerPrefixStepWeight k)] using
    (tendsto_integerRoughBudgetSlice_card_div hQ (mem_Icc.mp hk).1).mul_const
      (integerSmoothPrefixMaximum integral Y k : ℝ)

/-- Rough kernel prefixes with known density give a lower bound for the
extremal upper density. An error can be subtracted when the admissible
squarefree kernels omit some of the kernels whose density is known. -/
theorem smoothPrefixWeightedSum_sub_le_integerUpperDensitySupremum (integral : Bool) (Y : ℕ)
    {Q R : Set ℕ} {d err : ℝ} (hQ : Q ⊆ integerRoughNumbers Y) (hR : R ⊆ integerRoughNumbers Y)
    (hRsf : ∀ r ∈ R, Squarefree r) (hD : HasNaturalDensity Q d)
    (happrox : ∀ N, densityUpTo (integerRoughOptimalPrefix integral Y Q N) N ≤
      densityUpTo (integerRoughOptimalPrefix integral Y R N) N + err) :
    d * (∑' k, (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k) - err ≤
      integerUpperDensitySupremum integral := by
  let w (k : ℕ) := (integerSmoothPrefixMaximum integral Y k : ℝ) * integerPrefixStepWeight k
  have h₀ : w 0 = 0 := by simp [w, integerPrefixStepWeight]
  have hsum (M : ℕ) : ∑ k ∈ integerPrefix M, w k = ∑ k ∈ Finset.range (M+1), w k := by
    apply Finset.sum_subset
    · intro k hk
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
    · intro k hk hn
      have hK := mem_range.mp hk
      have hzero : k = 0 := by by_contra h; exact hn (mem_Icc.mpr ⟨Nat.pos_of_ne_zero h, by omega⟩)
      simpa only [hzero] using h₀
  have hlim : Tendsto (fun M ↦ d * ∑ k ∈ integerPrefix M, w k) atTop (𝓝 (d * ∑' k, w k)) := by
    simp_rw [hsum]
    exact tendsto_const_nhds.mul ((summable_smooth_optimum_weights integral Y).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1))
  apply le_of_tendsto (hlim.sub tendsto_const_nhds)
  apply Eventually.of_forall
  intro M
  apply le_integerUpperDensitySupremum_of_arbitrarily_large_prefix
  intro ε hε N₀
  have hNear := (tendsto_order.mp ((tendsto_rough_prefix_partial integral Y M hD).sub tendsto_const_nhds)).1
    (d * ∑ k ∈ integerPrefix M, w k - err - ε) (sub_lt_self _ hε)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hNear
  let N := max N₀ N₁
  refine ⟨N, le_max_left _ _, integerRoughOptimalPrefix integral Y R N,
    integerRoughOptimalPrefix_admissible integral Y N R hR hRsf, ?_⟩
  have hf := (proportion_integerRoughOptimalPrefix_ge integral Y N M hQ).trans (happrox N)
  exact (hN₁ N (le_max_right _ _)).le.trans (sub_le_iff_le_add.mpr hf)

private theorem densityUpTo_roughOptimalPrefix_le_squarefree_add_tail (integral : Bool) (Y N : ℕ) :
    densityUpTo (integerRoughOptimalPrefix integral Y (integerRoughNumbers Y) N) N ≤
      densityUpTo (integerRoughOptimalPrefix integral Y (integerSquarefreeRoughNumbers Y) N) N +
        integerPrimeSquareTail Y := by
  let raw := integerRoughOptimalPrefix integral Y (integerRoughNumbers Y) N
  let good := integerRoughOptimalPrefix integral Y (integerSquarefreeRoughNumbers Y) N
  let bad : Set ℕ := {n | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p^2 ∣ n}
  have hsub : raw ⊆ good ∪ bad := by
    rintro a ⟨r,s,hr,hs,rfl⟩
    by_cases hsf : Squarefree r
    · exact Or.inl ⟨r,s,⟨hr,hsf⟩,hs,rfl⟩
    · rw [Nat.squarefree_iff_prime_squarefree] at hsf
      push Not at hsf
      obtain ⟨p,hp,hpd⟩ := hsf
      have hpr := (dvd_mul_right p p).trans hpd
      have hpY := hr.2 p ((Nat.mem_primeFactorsList_iff_dvd hr.1 hp).mpr hpr)
      exact Or.inr ⟨p,hpY,hp,by rw [pow_two]; exact dvd_mul_of_dvd_left hpd s⟩
  exact (densityUpTo_mono hsub N).trans ((densityUpTo_union_le good bad N).trans
    (add_le_add (le_refl _) (densityUpTo_largePrimeSquare_le_tail Y N)))

/-- Discarding the large prime-square multiples gives an admissible global set
whose upper density loses at most the prime-square tail from `U_Y`. -/
theorem integerSmoothUpperOptimization_sub_integerPrimeSquareTail_le_integerUpperDensitySupremum
    (integral : Bool) (Y : ℕ) :
    integerSmoothUpperOptimization integral Y - integerPrimeSquareTail Y ≤
      integerUpperDensitySupremum integral := by
  unfold integerSmoothUpperOptimization
  exact smoothPrefixWeightedSum_sub_le_integerUpperDensitySupremum integral Y
    (Set.Subset.rfl) (fun _ h ↦ h.1) (fun _ h ↦ h.2) (hasNaturalDensity_integerRoughNumbers Y)
    (densityUpTo_roughOptimalPrefix_le_squarefree_add_tail integral Y)

end GRHArticle.ProgressionFree
