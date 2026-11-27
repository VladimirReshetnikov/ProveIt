import GRHArticle.ProgressionFree.LightPrimeBlocks
import GRHArticle.ProgressionFree.IntegerPrimeBlockPartitions

/-!
# Finite independence of joint exponent rules

A finite family of disjoint prime blocks can be indexed by the dependent
sum of its valuation coordinates. Truncating the exponents gives a
finite exact density formula, and the omitted prime powers have small
density uniformly in the counting cutoff.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- The natural-density factor of a local rule on a finite prime block. -/
noncomputable def primeBlockProbability (P : Finset ℕ) (F : Set (↥P → ℕ)) : ℝ :=
  (∏ p : ↥P, (1-1/(p.val : ℝ))) *
    reciprocalExponentMass (fun p : ↥P ↦ 1/(p.val : ℝ)) F

/-- The positive integers passing only this finite collection of block rules. -/
def finitePrimeBlockRule (T : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ P ∈ T, (fun p : ↥P ↦ n.factorization p.val) ∈ rules P}

/-- Bounded exponent patterns in a given local rule. -/
noncomputable def blockPatternsBelow {ι : Type*} [Fintype ι]
    (F : Set (ι → ℕ)) (K : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι ↦ range K).filter (· ∈ F)

theorem mem_blockPatternsBelow {ι : Type*} [Fintype ι] {F : Set (ι → ℕ)}
    {K : ℕ} {v : ι → ℕ} : v ∈ blockPatternsBelow F K ↔ v ∈ F ∧ ∀ p, v p < K := by
  simp only [blockPatternsBelow, mem_filter, Fintype.mem_piFinset, mem_range, and_comm]

private theorem tendsto_box {ι : Type*} [Fintype ι] :
    Tendsto (fun K : ℕ ↦ Fintype.piFinset (fun _ : ι ↦ range K)) atTop atTop := by
  apply tendsto_atTop.2
  intro U
  let M := U.sup fun v : ι → ℕ ↦ (univ : Finset ι).sup v
  filter_upwards [eventually_gt_atTop M] with K hK
  intro v hv
  apply Fintype.mem_piFinset.mpr
  intro p
  have h₁ : (univ : Finset ι).sup v ≤ M := le_sup (f := fun v : ι → ℕ ↦ (univ : Finset ι).sup v) hv
  have h₂ : v p ≤ (univ : Finset ι).sup v := le_sup (f := v) (mem_univ _)
  exact mem_range.mpr (h₂.trans_lt (h₁.trans_lt hK))

/-- Bounded pattern masses converge to the complete reciprocal mass. -/
theorem tendsto_sum_blockPatternsBelow {ι : Type*} [Fintype ι] {u : ι → ℝ}
    (hu₀ : ∀ p, 0 ≤ u p) (hu₁ : ∀ p, u p < 1) (F : Set (ι → ℕ)) :
    Tendsto (fun K ↦ ∑ v ∈ blockPatternsBelow F K, reciprocalExponentWeight u v)
      atTop (𝓝 (reciprocalExponentMass u F)) := by
  have hs : Summable (F.indicator (reciprocalExponentWeight u)) :=
    summable_subtype_iff_indicator.mp ((summable_reciprocalExponentWeight hu₀ hu₁).subtype _)
  have ht := hs.hasSum.comp (tendsto_box (ι := ι))
  refine ht.congr fun K ↦ ?_
  simp only [Function.comp_apply, blockPatternsBelow, sum_filter, Set.indicator]

private theorem reciprocalPrime_lt_one {p : ℕ} (h : p.Prime) : 1/(p : ℝ) < 1 :=
  (div_lt_one (by exact_mod_cast h.pos)).mpr (by exact_mod_cast h.one_lt)

private def finiteTruncation (T : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (K : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ P ∈ T, (fun p : ↥P ↦ n.factorization p.val) ∈ blockPatternsBelow (rules P) K}

private noncomputable def finiteProbability (P : Finset ℕ)
    (F : Set (↥P → ℕ)) (K : ℕ) : ℝ :=
  (∏ p : ↥P, (1-1/(p.val : ℝ))) *
    ∑ v ∈ blockPatternsBelow F K, reciprocalExponentWeight (fun p : ↥P ↦ 1/(p.val : ℝ)) v

private theorem finiteTruncation_density (T : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (K : ℕ)
    (hpr : ∀ P ∈ T, ∀ p ∈ P, p.Prime)
    (hpair : (T : Set (Finset ℕ)).PairwiseDisjoint id) :
    HasNaturalDensity (finiteTruncation T rules K)
      (∏ P ∈ T, finiteProbability P (rules P) K) := by
  let ι := Σ P : ↥T, ↥P.val
  let prime (x : ι) := x.2.val
  have hinj : Function.Injective prime := by
    intro ⟨P,p⟩ ⟨Q,q⟩ h
    change p.val = q.val at h
    have he : P = Q := by
      apply Subtype.ext
      by_contra hn
      have hd := hpair P.property Q.property hn
      exact (disjoint_left.mp hd) p.property (h.symm ▸ q.property)
    subst Q
    exact congrArg (Sigma.mk P) (Subtype.ext h)
  have hp (x : ι) : (prime x).Prime :=
    hpr x.1.val x.1.property x.2.val x.2.property
  let E (P : ↥T) := blockPatternsBelow (rules P.val) K
  let enc : ((P : ↥T) → ↥P.val → ℕ) ↪ (ι → ℕ) :=
    ⟨fun w x ↦ w x.1 x.2, fun _ _ h ↦ funext fun P ↦ funext fun p ↦ congrFun h ⟨P,p⟩⟩
  let W := (Fintype.piFinset E).map enc
  have hset : {n | n ≠ 0 ∧ (fun x ↦ n.factorization (prime x)) ∈ W} =
      finiteTruncation T rules K := by
    ext n
    let v (P : ↥T) (p : ↥P.val) := n.factorization p.val
    change (n ≠ 0 ∧ enc v ∈ W) ↔ n ≠ 0 ∧ ∀ P ∈ T, _ ∈ blockPatternsBelow (rules P) K
    rw [show W = (Fintype.piFinset E).map enc from rfl, Finset.mem_map', Fintype.mem_piFinset]
    exact and_congr_right fun _ ↦ ⟨fun h P hP ↦ h ⟨P,hP⟩,fun h P ↦ h P.val P.property⟩
  have hweight (v : (P : ↥T) → ↥P.val → ℕ) :
      (∏ x : ι, (1-1/(prime x : ℝ))*(1/(prime x : ℝ))^enc v x) =
      ∏ P : ↥T, (∏ p : ↥P.val, (1-1/(p.val : ℝ))) *
        reciprocalExponentWeight (fun p : ↥P.val ↦ 1/(p.val : ℝ)) (v P) := by
    rw [Fintype.prod_sigma]
    apply prod_congr rfl
    intro P _
    exact prod_mul_distrib
  have hsum :
      (∑ w ∈ W, ∏ x : ι, (1-1/(prime x : ℝ))*(1/(prime x : ℝ))^w x) =
      ∏ P ∈ T, finiteProbability P (rules P) K := by
    unfold W
    rw [sum_map]
    simp_rw [hweight]
    rw [← Finset.prod_univ_sum E (fun (P : ↥T) (v : ↥P.val → ℕ) ↦
      (∏ p : ↥P.val, (1-1/(p.val : ℝ))) *
        reciprocalExponentWeight (fun p : ↥P.val ↦ 1/(p.val : ℝ)) v)]
    simp only [← mul_sum, E, finiteProbability]
    rw [univ_eq_attach]
    exact prod_attach T (fun P ↦ finiteProbability P (rules P) K)
  have hD := hasNaturalDensity_indexedValuationPatterns prime hinj hp W
  rwa [hset,hsum] at hD

private theorem finiteTruncation_error (T : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) (K N : ℕ)
    (hpr : ∀ P ∈ T, ∀ p ∈ P, p.Prime) :
    |densityUpTo (finitePrimeBlockRule T rules) N -
      densityUpTo (finiteTruncation T rules K) N| ≤ ∑ p ∈ T.biUnion id, 1/(p : ℝ)^K := by
  have hP (p : ℕ) (hp : p ∈ T.biUnion id) : p.Prime := by
    obtain ⟨P,hP,hpP⟩ := mem_biUnion.mp hp
    exact hpr P hP p hpP
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset
    (E := {n | ∃ p ∈ T.biUnion id, p^K ∣ n}) N ?_).trans ?_
  · intro n hn
    rcases hn with ⟨h,h'⟩ | ⟨h,h'⟩
    · by_contra H
      apply h'
      refine ⟨h.1, fun P hP ↦ mem_blockPatternsBelow.mpr ⟨h.2 P hP,fun p ↦ ?_⟩⟩
      by_contra! hp
      exact H ⟨p.val, mem_biUnion.mpr ⟨P,hP,p.property⟩,
        ((hpr P hP p.val p.property).pow_dvd_iff_le_factorization h.1).mpr hp⟩
    · exact (h' ⟨h.1,fun P hP ↦ (mem_blockPatternsBelow.mp (h.2 P hP)).1⟩).elim
  · simpa only [Nat.cast_pow] using
      densityUpTo_divisibleByOneOf_le (T.biUnion id) (fun p ↦ p^K) N
        (fun p hp ↦ pow_pos (hP p hp).pos _)

set_option maxHeartbeats 500000 in
/-- On a finite family of disjoint prime blocks, arbitrary local rules
have natural density equal to the product of their local probabilities. -/
theorem hasNaturalDensity_finitePrimeBlockRule (T : Finset (Finset ℕ))
    (rules : (P : Finset ℕ) → Set (↥P → ℕ))
    (hpr : ∀ P ∈ T, ∀ p ∈ P, p.Prime)
    (hpair : (T : Set (Finset ℕ)).PairwiseDisjoint id) :
    HasNaturalDensity (finitePrimeBlockRule T rules) (∏ P ∈ T, primeBlockProbability P (rules P)) := by
  let d := ∏ P ∈ T, primeBlockProbability P (rules P)
  let f (K : ℕ) := ∏ P ∈ T, finiteProbability P (rules P) K
  have hf : Tendsto f atTop (𝓝 d) :=
    tendsto_finsetProd T fun P hP ↦
      tendsto_const_nhds.mul (tendsto_sum_blockPatternsBelow
        (u := fun p : ↥P ↦ 1/(p.val : ℝ)) (fun _ ↦ by positivity)
        (fun p ↦ reciprocalPrime_lt_one (hpr P hP p.val p.property)) (rules P))
  have hErr : Tendsto (fun K : ℕ ↦ ∑ p ∈ T.biUnion id, 1/(p : ℝ)^K) atTop (𝓝 0) := by
    simp_rw [← one_div_pow]
    rw [show (0 : ℝ) = ∑ p ∈ T.biUnion id, 0 by simp]
    apply tendsto_finsetSum
    intro p hp
    obtain ⟨P,hP,hpP⟩ := mem_biUnion.mp hp
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (reciprocalPrime_lt_one (hpr P hP p hpP))
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε₃ : 0 < ε/3 := by positivity
  have hf' : ∀ᶠ K in atTop, |f K-d| < ε/3 :=
    (hf.eventually (Metric.ball_mem_nhds _ hε₃)).mono (fun K h ↦ by simpa [Metric.mem_ball,Real.dist_eq] using h)
  obtain ⟨K,hK,hfK⟩ := ((hErr.eventually_lt_const hε₃).and hf').exists
  have hD : HasNaturalDensity (finiteTruncation T rules K) (f K) := finiteTruncation_density T rules K hpr hpair
  obtain ⟨N₀,hN₀⟩ := Metric.tendsto_atTop.1 hD (ε/3) hε₃
  refine ⟨N₀,fun N hN ↦ ?_⟩
  rw [Real.dist_eq]
  have hA := finiteTruncation_error T rules K N hpr
  have hB : |densityUpTo (finiteTruncation T rules K) N-f K| < ε/3 :=
    by simpa only [Real.dist_eq] using hN₀ N hN
  have hx := abs_sub_le (densityUpTo (finitePrimeBlockRule T rules) N)
    (densityUpTo (finiteTruncation T rules K) N) d
  have hy := abs_sub_le (densityUpTo (finiteTruncation T rules K) N) (f K) d
  linarith

end GRHArticle.ProgressionFree
