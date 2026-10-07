import OAI.Combinatorics.Progressions.Dynamics.ReferenceMeanBudget
import OAI.Combinatorics.Progressions.Estimates.RetainedShellComparison
import OAI.Combinatorics.Progressions.Lattices.ResidueCellNormLengths

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_re_nonneg {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re) :
    0 ≤ (residuePrimeCoordinateMean g lo N M a q K base).re := by
  rw [residuePrimeCoordinateMean_re, Fintype.expect_eq_sum_div_card]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro z _
  apply hg
  apply (mem_translatedIntegerBox lo N _).mpr
  intro j
  exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val j).property).1)

theorem ResiduePrimeCoordinateStable.self_upper {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] {g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ}
    {M : ℕ} {q : ι → ℕ} {r : ℕ} {δ : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base) :
    PrimeRefinementUpperBound g g lo N M a q r 1 0 δ K base := by
  intro J hKJ hJ y hy hne
  exact hstable.refinement_upper_bound zero_le_one J hKJ hJ y hy hne (by simp)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_reference_mean_bounds {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level ε δ η τ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1)
    (hlevel : 0 ≤ level) (hτ : 0 ≤ τ) (hδ : δ ≤ τ / 8) (hε : ε ≤ level * τ / 8)
    (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ r →
      2 * (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) ≤ η) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ∀ (S : Finset {i // i ∉ K}), S.card ≤ r → ∀ x,
      productConditionalMean μ S (density (fun z => (h z).re)) x ≤
        level * productConditionalMean μ S (density (fun z => (g z).re)) x + level * τ ∧
      v - τ ≤ productConditionalMean μ S (density (fun z => (g z).re)) x := by
  dsimp only
  intro S hS x
  have he := herror S hS
  have hs : (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) < 1 / 2 := by
    linarith
  have hgclose := hstable.reference_density_close hM hpair hcop u 1 zero_le_one hg S hS x hs
  have hhupper := hupper.reference_density_upper hM hpair hcop u 1 zero_le_one hh S hS x hs
  simp only [mul_one] at hgclose hhupper
  apply reference_mean_comparison_of_budget hlevel hτ hδ hε hητ hηlevel
  · exact hgclose.trans (add_le_add le_rfl he)
  · exact hhupper.trans (add_le_add le_rfl he)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_retained_atom {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level inc δ η τ ε ξ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1)
    (hlevel : 0 ≤ level) (hτ : 0 ≤ τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hε : 0 ≤ ε) (hsmall : ξ * (2 + ε) ≤ ε)
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ r →
      2 * (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) ≤ η) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ∀ (S : Finset {i // i ∉ K}), S.card ≤ r → ∀ x PH PG mass m EH EG UH UG,
      0 ≤ mass → 0 ≤ m →
      |PH - (mass * m) * productConditionalMean μ S (density (fun z => (h z).re)) x| ≤
        EH + mass * m * (4 * level * (v + τ)) * UH →
      |PG - (mass * m) * productConditionalMean μ S (density (fun z => (g z).re)) x| ≤
        EG + mass * m * (2 * (v + τ)) * UG →
      4 * UH ≤ ξ → 2 * UG ≤ ξ →
      PH - (1 + ε) * level * PG ≤
        (mass * m) * level * (1 + 2 * ε) * τ + EH + (1 + ε) * level * EG := by
  dsimp only
  intro S hS x PH PG mass m EH EG UH UG hmass hm hPH hPG hUH hUG
  have hga : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hg z hz).1]
    exact (hg z hz).2
  have hmeans := stable_site_reference_mean_bounds hstable hupper hM hpair hcop u hga hh
    hlevel hτ hδ hinc hη hητ hηlevel herror S hS x
  have hv := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  exact retained_atom_from_normalized_errors hmass hm hlevel hv hτ hε hPH hPG hUH hUG
    hmeans.1 hmeans.2 hsmall

end Erdos3

end

end OAI
