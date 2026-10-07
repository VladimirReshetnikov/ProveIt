import OAI.Combinatorics.Progressions.Estimates.StableRetainedAtom

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem PrimeRefinementUpperBound.normalized_reference_bounded {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level ε δ η scale : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1)
    (hscale : 0 < scale) (hη : η < 1)
    (hcap : level * (residuePrimeCoordinateMean g lo N M a q K base).re + ε + level * δ + η ≤ scale)
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ r →
      2 * (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) ≤ η) :
    ProductBoundedMarginals (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (normalizedResiduePrimeDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) scale) 1 r := by
  apply scaled_bounded_marginals _ _ hscale r
  intro S hS x _
  have he := herror S hS
  have hs : (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) < 1 / 2 := by
    linarith
  have hu := hupper.reference_density_upper hM hpair hcop u 1 zero_le_one hh S hS x hs
  linarith

theorem stable_site_normalized_marginals {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level ε δ η τ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ) (hε : ε ≤ level * τ)
    (hη : η < 1) (hητ : η ≤ τ) (hηlevel : η ≤ level * τ)
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ r →
      2 * (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) ≤ η) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f scale => normalizedResiduePrimeDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f scale
    let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ProductBoundedMarginals μ (density (fun z => (g z).re) (2 * (v + τ))) 1 r ∧
    ProductBoundedMarginals μ (density (fun z => (h z).re) (4 * level * (v + τ))) 1 r := by
  dsimp only
  have hv := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  have hga : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hg z hz).1]
    exact (hg z hz).2
  constructor
  · apply hstable.self_upper.normalized_reference_bounded hM hpair hcop u hga (by positivity) hη _ herror
    simp only [one_mul, add_zero]
    linarith
  · apply hupper.normalized_reference_bounded hM hpair hcop u hh (by positivity) hη _ herror
    nlinarith [mul_nonneg hlevel.le hv, mul_le_mul_of_nonneg_left hδ hlevel.le]

end Erdos3

end

end OAI
