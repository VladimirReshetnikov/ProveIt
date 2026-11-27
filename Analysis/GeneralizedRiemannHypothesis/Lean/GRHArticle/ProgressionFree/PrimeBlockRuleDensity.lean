import GRHArticle.ProgressionFree.ExactRuleApproximation
import GRHArticle.ProgressionFree.EulerLowerBound

/-!
# Densities of finite prime blocks with general exterior exponent rules

The exterior rule may be any set of exponents containing zero and one.
A common positive factor transfers quantitative finite mass gains to
strict increases in natural density.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- A joint rule on the affected primes, with an independent exponent rule
`G` at every other prime. -/
def primeBlockRuleSet (G : Set ℕ) (marker : ℕ) (S : Finset ℕ)
    (C : Set (ℕ × (↥S → ℕ))) : Set ℕ :=
  {n | n ≠ 0 ∧ (n.factorization marker, fun p : ↥S ↦ n.factorization p.val) ∈ C ∧
    ∀ p : ℕ, p.Prime → p ≠ marker → p ∉ S → n.factorization p ∈ G}

/-- The accepted exponents strictly below a finite cutoff. -/
noncomputable def exponentsBelow (G : Set ℕ) (K : ℕ) : Finset ℕ :=
  (range K).filter (· ∈ G)

theorem mem_exponentsBelow {G : Set ℕ} {K j : ℕ} :
    j ∈ exponentsBelow G K ↔ j ∈ G ∧ j < K := by
  simp only [exponentsBelow, mem_filter, mem_range, and_comm]

private def finiteRule {ι ρ : Type*} [Fintype ι]
    (G : Set ℕ) (a : Option ι → ℕ) (r : ρ → ℕ) (C : Set (ℕ × (ι → ℕ))) (K : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ (n.factorization (a none), fun i ↦ n.factorization (a (some i))) ∈
    boundedExactPatterns C K ∧ ∀ q, n.factorization (r q) ∈ exponentsBelow G K}

private noncomputable def commonWeight {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (G : Set ℕ) (a : Option ι → ℕ) (r : ρ → ℕ) (K : ℕ) : ℝ :=
  (∏ o, (1 - 1 / (a o : ℝ))) *
    ∏ q, (1 - 1 / (r q : ℝ)) * ∑ e ∈ exponentsBelow G K, (1 / (r q : ℝ))^e

private theorem finite_rule_density {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (G : Set ℕ) (a : Option ι → ℕ) (r : ρ → ℕ) (C : Set (ℕ × (ι → ℕ))) (K : ℕ)
    (hinj : Function.Injective (Sum.elim a r))
    (ha : ∀ o, (a o).Prime) (hr : ∀ q, (r q).Prime) :
    HasNaturalDensity (finiteRule G a r C K)
      (exactPatternMass (1 / (a none : ℝ)) (fun i ↦ 1 / (a (some i) : ℝ)) C K *
        commonWeight G a r K) := by
  let U := boundedExactPatterns C K
  let V := Fintype.piFinset fun _ : ρ ↦ exponentsBelow G K
  let enc : ((ℕ × (ι → ℕ)) × (ρ → ℕ)) ↪ ((Option ι ⊕ ρ) → ℕ) :=
    ⟨fun v ↦ Sum.elim (fun o ↦ o.elim v.1.1 v.1.2) v.2, by
      intro v w h
      exact Prod.ext (Prod.ext (congrFun h (.inl none))
        (funext fun i ↦ congrFun h (.inl (some i)))) (funext fun q ↦ congrFun h (.inr q))⟩
  let P := (U ×ˢ V).map enc
  let p := Sum.elim a r
  have hp : ∀ j, (p j).Prime := fun j ↦ Sum.rec ha hr j
  have hset : {n | n ≠ 0 ∧ (fun j ↦ n.factorization (p j)) ∈ P} = finiteRule G a r C K := by
    ext n
    let u := (n.factorization (a none), fun i ↦ n.factorization (a (some i)))
    let v (q : ρ) := n.factorization (r q)
    have he : enc (u,v) = fun j ↦ n.factorization (p j) := by
      funext j
      rcases j with o | q
      · cases o <;> rfl
      · rfl
    change (n ≠ 0 ∧ (fun j ↦ n.factorization (p j)) ∈ P) ↔ n ≠ 0 ∧ u ∈ U ∧ _
    rw [← he, show P = (U ×ˢ V).map enc from rfl, Finset.mem_map', Finset.mem_product]
    simp only [V, v, Fintype.mem_piFinset]
  let W := exactPatternWeight (ι := ι) (1/(a none : ℝ)) (fun i ↦ 1/(a (some i) : ℝ))
  let A := ∏ o, (1 - 1/(a o : ℝ))
  let R (v : ρ → ℕ) := ∏ q, (1 - 1/(r q : ℝ)) * (1/(r q : ℝ))^v q
  have hweight (v : (ℕ × (ι → ℕ)) × (ρ → ℕ)) :
      (∏ j, (1 - 1/(p j : ℝ)) * (1/(p j : ℝ))^enc v j) = W v.1 * (A * R v.2) := by
    rw [Fintype.prod_sum_type]
    change (∏ o : Option ι, (1 - 1/(a o : ℝ)) *
      (1/(a o : ℝ))^o.elim v.1.1 v.1.2) * R v.2 = _
    rw [prod_mul_distrib]
    have hW : (∏ o : Option ι, (1/(a o : ℝ))^o.elim v.1.1 v.1.2) = W v.1 := by
      rw [Fintype.prod_option]
      rfl
    rw [hW]
    change (A * W v.1) * R v.2 = _
    ring
  have hrSum : (∑ v ∈ V, R v) = ∏ q, (1 - 1/(r q : ℝ)) *
      ∑ e ∈ exponentsBelow G K, (1/(r q : ℝ))^e := by
    dsimp only [V, R]
    rw [← Finset.prod_univ_sum (fun _ : ρ ↦ exponentsBelow G K)
      (fun q e ↦ (1 - 1/(r q : ℝ)) * (1/(r q : ℝ))^e)]
    simp only [mul_sum]
  have he :
      (∑ e ∈ P, ∏ j, (1 - 1/(p j : ℝ)) * (1/(p j : ℝ))^e j) =
        (∑ v ∈ U, W v) * (A * ∑ v ∈ V, R v) := by
    unfold P
    rw [sum_map]
    simp_rw [sum_product, hweight, ← mul_sum, ← sum_mul]
  have h := hasNaturalDensity_indexedValuationPatterns p hinj hp P
  rw [hset, he, hrSum] at h
  exact h

private theorem abs_densityUpTo_rule_sub_finite_le {marker Y : ℕ} {S : Finset ℕ}
    {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G) (C : Set (ℕ × (↥S → ℕ))) (N K : ℕ)
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime)
    (hmY : marker ≤ Y) (hSY : ∀ p ∈ S, p ≤ Y) (hY : 0 < Y) :
    |densityUpTo (primeBlockRuleSet G marker S C) N -
      densityUpTo (finiteRule G (exchangeAffected marker S)
        (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) C K) N| ≤
      1/(Y : ℝ) + ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ)^K := by
  let E := {n : ℕ | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p^2 ∣ n}
  let F := {n : ℕ | ∃ p ∈ Nat.primesLE Y, p^K ∣ n}
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset (E := E ∪ F) N ?_).trans
    ((densityUpTo_union_le E F N).trans (add_le_add (densityUpTo_largePrimeSquare_le Y N hY) ?_))
  · intro n hn
    rcases hn with ⟨hn,ht⟩ | ⟨ht,hn⟩
    · apply Or.inr
      by_contra hlarge
      have hsmall (p : ℕ) (hp : p ∈ Nat.primesLE Y) : n.factorization p < K := by
        by_contra hp'
        exact hlarge ⟨p, hp, ((Nat.prime_of_mem_primesLE hp).pow_dvd_iff_le_factorization hn.1).mpr
          (Nat.le_of_not_gt hp')⟩
      apply ht
      refine ⟨hn.1, mem_boundedExactPatterns.mpr ⟨hn.2.1, ?_, ?_⟩, ?_⟩
      · exact hsmall marker (Nat.mem_primesLE.mpr ⟨hmY,hm⟩)
      · intro p
        exact hsmall p.val (Nat.mem_primesLE.mpr ⟨hSY _ p.property,hS _ p.property⟩)
      · intro q
        have hq := mem_sdiff.mp q.property
        have hm' : q.val ≠ marker := fun h ↦ hq.2 (mem_insert.mpr (Or.inl h))
        have hs' : q.val ∉ S := fun h ↦ hq.2 (mem_insert.mpr (Or.inr h))
        exact mem_exponentsBelow.mpr ⟨hn.2.2 _ (exchangeRough_prime q) hm' hs', hsmall _ hq.1⟩
    · apply Or.inl
      by_contra hlarge
      apply hn
      refine ⟨ht.1, (mem_boundedExactPatterns.mp ht.2.1).1, fun p hp hpm hpS ↦ ?_⟩
      by_cases hle : p ≤ Y
      · have hmem : p ∈ exchangeRough marker S Y := mem_sdiff.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hle,hp⟩, fun h ↦ (mem_insert.mp h).elim hpm hpS⟩
        exact (mem_exponentsBelow.mp (ht.2.2 ⟨p,hmem⟩)).1
      · have hfac : n.factorization p < 2 := by
          by_contra! h
          exact hlarge ⟨p, lt_of_not_ge hle, hp, (hp.pow_dvd_iff_le_factorization ht.1).mpr h⟩
        rcases (show n.factorization p = 0 ∨ n.factorization p = 1 by omega) with h | h
        · exact h.symm ▸ h0
        · exact h.symm ▸ h1
  · simpa only [F, Nat.cast_pow] using
      densityUpTo_divisibleByOneOf_le (Nat.primesLE Y) (fun p ↦ p^K) N
        (fun p hp ↦ pow_pos (Nat.prime_of_mem_primesLE hp).pos _)

private theorem exists_cutoffs (marker : ℕ) (S : Finset ℕ) (K₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y K : ℕ, 0 < Y ∧ K₀ ≤ K ∧ marker ≤ Y ∧ (∀ p ∈ S, p ≤ Y) ∧
      1/(Y : ℝ) + ∑ p ∈ Nat.primesLE Y, 1/(p : ℝ)^K ≤ ε := by
  obtain ⟨Y,L,hY,_,hM,hS,hB⟩ := exists_digitRule_cutoffs marker S hε
  refine ⟨Y,max K₀ (3*L),hY,le_max_left _ _,hM,hS,?_⟩
  refine (add_le_add le_rfl (sum_le_sum fun p hp ↦ ?_)).trans hB
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
  exact one_div_le_one_div_of_le (pow_pos hp0 _) (pow_le_pow_right₀ hp1 (le_max_right _ _))

/-- Any prime-block rule with a valid squarefree exterior pattern has a
natural density. -/
theorem exists_hasNaturalDensity_primeBlockRuleSet {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    {marker : ℕ} {S : Finset ℕ} (C : Set (ℕ × (↥S → ℕ)))
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (hdisj : marker ∉ S) :
    ∃ d, HasNaturalDensity (primeBlockRuleSet G marker S C) d := by
  apply exists_hasNaturalDensity_of_uniform_approximation
  intro ε hε
  obtain ⟨Y,K,hY,_,hmY,hSY,hB⟩ := exists_cutoffs marker S 0 hε
  refine ⟨_, _, finite_rule_density G (exchangeAffected marker S)
    (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) C K
    (exchangePrimeCoordinates_injective hdisj) (exchangeAffected_prime hm hS) exchangeRough_prime, ?_⟩
  intro N
  exact (abs_densityUpTo_rule_sub_finite_le h0 h1 C N K hm hS hmY hSY hY).trans hB

private theorem prime_recips {p : ℕ} (hp : p.Prime) : (1 : ℝ) / p < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact (div_lt_one (by linarith)).mpr hp1

private theorem commonWeight_lower {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    {marker Y K : ℕ} {S : Finset ℕ} (hm : marker.Prime)
    (hS : ∀ p ∈ S, p.Prime) (hK : 2 ≤ K) :
    (∏ o, (1 - 1 / (exchangeAffected marker S o : ℝ))) * (1/2) ≤
      commonWeight G (exchangeAffected marker S) (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) K := by
  let R := exchangeRough marker S Y
  have hR : (1/2 : ℝ) ≤ ∏ q : ↥R, (1 - 1 / (q.val : ℝ)^2) := by
    rw [univ_eq_attach, prod_attach R (fun q : ℕ ↦ 1 - 1 / (q : ℝ)^2)]
    exact one_half_le_prod_one_sub_inv_sq R
      (fun q hq ↦ (exchangeRough_prime (marker := marker) ⟨q,hq⟩).two_le)
  unfold commonWeight
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun p _ ↦
    sub_nonneg.mpr (prime_recips (exchangeAffected_prime hm hS p)).le)
  refine hR.trans (prod_le_prod (fun q _ ↦ ?_) (fun q _ ↦ ?_))
  · have hq := prime_recips (exchangeRough_prime q)
    rw [← one_div_pow]
    nlinarith [sq_nonneg ((1:ℝ)/q.val),
      mul_nonneg (by positivity : (0:ℝ) ≤ 1/q.val) (sub_nonneg.mpr hq.le)]
  · have hq := prime_recips (exchangeRough_prime q)
    have hs : ({0,1} : Finset ℕ) ⊆ exponentsBelow G K := by
      intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact mem_exponentsBelow.mpr ⟨h0, by omega⟩
      · exact mem_exponentsBelow.mpr ⟨h1, by omega⟩
    have hsum : 1 + 1/(q.val : ℝ) ≤ ∑ e ∈ exponentsBelow G K, (1/(q.val : ℝ))^e := by
      simpa using sum_le_sum_of_subset_of_nonneg
        (f := fun e : ℕ ↦ (1/(q.val : ℝ))^e) hs (fun _ _ _ ↦ by positivity)
    calc
      _ = (1 - 1/(q.val : ℝ)) * (1 + 1/(q.val : ℝ)) := by rw [← one_div_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hq.le)

/-- A positive mass gain uniform over sufficiently large bounded exponent
cutoffs gives a strict natural-density gain for the full prime-block rules. -/
theorem naturalDensity_primeBlockRuleSet_lt_of_mass_gain {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    {marker : ℕ} {S : Finset ℕ} (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (hdisj : marker ∉ S)
    {C D : Set (ℕ × (↥S → ℕ))} {c d : ℝ}
    (hC : HasNaturalDensity (primeBlockRuleSet G marker S C) c)
    (hD : HasNaturalDensity (primeBlockRuleSet G marker S D) d)
    {δ : ℝ} (hδ : 0 < δ) (K₀ : ℕ)
    (hgain : ∀ K, K₀ ≤ K →
      δ ≤ exactPatternMass (1/(marker : ℝ)) (fun q : ↥S ↦ 1/(q.val : ℝ)) D K -
        exactPatternMass (1/(marker : ℝ)) (fun q : ↥S ↦ 1/(q.val : ℝ)) C K) : c < d := by
  let a := exchangeAffected marker S
  let L := (∏ o, (1 - 1/(a o : ℝ))) * (1/2)
  have hL : 0 < L := mul_pos (prod_pos fun p _ ↦
    sub_pos.mpr (prime_recips (exchangeAffected_prime hm hS p))) (by norm_num)
  let ε := δ*L/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Y,K,hY,hK,hmY,hSY,hB⟩ := exists_cutoffs marker S (max K₀ 2) hε
  let r := (Subtype.val : ↥(exchangeRough marker S Y) → ℕ)
  let W := commonWeight G a r K
  let m (U : Set (ℕ × (↥S → ℕ))) := exactPatternMass (1/(marker : ℝ))
    (fun q : ↥S ↦ 1/(q.val : ℝ)) U K
  have hW : L ≤ W := commonWeight_lower h0 h1 hm hS ((le_max_right _ _).trans hK)
  have hclose (U : Set (ℕ × (↥S → ℕ))) {u : ℝ}
      (hu : HasNaturalDensity (primeBlockRuleSet G marker S U) u) : |u - m U * W| ≤ ε := by
    have hfinite : HasNaturalDensity (finiteRule G a r U K) (m U * W) :=
      finite_rule_density G a r U K (exchangePrimeCoordinates_injective hdisj)
        (exchangeAffected_prime hm hS) exchangeRough_prime
    exact le_of_tendsto' (hu.sub hfinite).abs fun N ↦
      (abs_densityUpTo_rule_sub_finite_le h0 h1 U N K hm hS hmY hSY hY).trans hB
  have hdiff : δ*L ≤ m D * W - m C * W := by
    rw [← sub_mul]
    exact mul_le_mul (hgain K ((le_max_left _ _).trans hK)) hW hL.le (hδ.le.trans (hgain K ((le_max_left _ _).trans hK)))
  have hb := mul_pos hδ hL
  have hce := (abs_le.mp (hclose C hC)).2
  have hde := (abs_le.mp (hclose D hD)).1
  dsimp [ε] at hce hde
  linarith

end GRHArticle.ProgressionFree
