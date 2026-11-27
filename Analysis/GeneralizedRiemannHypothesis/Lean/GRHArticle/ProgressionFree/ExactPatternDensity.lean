import GRHArticle.ProgressionFree.IndexedDensity
import GRHArticle.ProgressionFree.RankinTruncation
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Densities of bounded exact-valuation rules

A correlated rule on the affected primes can be any set of exact exponent
tuples. Truncating all tracked exponents gives a finite pattern family whose
density factors into affected reciprocal mass and a common factor.
-/

open scoped BigOperators

namespace GRHArticle.ProgressionFree

/-- The exact tuples in the rule with every coordinate below the cutoff. -/
noncomputable def boundedExactPatterns {ι : Type*} [Fintype ι]
    (C : Set (ℕ × (ι → ℕ))) (K : ℕ) : Finset (ℕ × (ι → ℕ)) := by
  classical
  exact ((Finset.range K) ×ˢ (Fintype.piFinset fun _ : ι => Finset.range K)).filter (· ∈ C)

theorem mem_boundedExactPatterns {ι : Type*} [Fintype ι]
    {C : Set (ℕ × (ι → ℕ))} {K : ℕ} {v : ℕ × (ι → ℕ)} :
    v ∈ boundedExactPatterns C K ↔ v ∈ C ∧ v.1 < K ∧ ∀ i, v.2 i < K := by
  classical
  simp only [boundedExactPatterns, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Fintype.mem_piFinset, and_comm]

/-- Reciprocal weight of an exact affected-prime exponent tuple. -/
noncomputable def exactPatternWeight {ι : Type*} [Fintype ι]
    (w : ℝ) (u : ι → ℝ) (v : ℕ × (ι → ℕ)) : ℝ :=
  w ^ v.1 * ∏ i, u i ^ v.2 i

/-- Reciprocal mass of bounded exact exponent patterns. -/
noncomputable def exactPatternMass {ι : Type*} [Fintype ι]
    (w : ℝ) (u : ι → ℝ) (C : Set (ℕ × (ι → ℕ))) (K : ℕ) : ℝ :=
  ∑ v ∈ boundedExactPatterns C K, exactPatternWeight w u v

/-- Finite-prime, bounded-exponent approximation to the exact exponent rule. -/
def finiteExactRuleSet {ι ρ : Type*} [Fintype ι]
    (affected : Option ι → ℕ) (rough : ρ → ℕ) (C : Set (ℕ × (ι → ℕ))) (K : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧
    (n.factorization (affected none), fun i => n.factorization (affected (some i))) ∈
      boundedExactPatterns C K ∧ ∀ q, n.factorization (rough q) ∈ greedyExponentsBelow K}

/-- Factors of the finite density independent of the selected exact patterns. -/
noncomputable def exactRuleCommonWeight {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (affected : Option ι → ℕ) (rough : ρ → ℕ) (K : ℕ) : ℝ :=
  (∏ o, (1 - 1 / (affected o : ℝ))) *
    (∏ q, (1 - 1 / (rough q : ℝ)) *
      ∑ h ∈ greedyExponentsBelow K, (1 / (rough q : ℝ)) ^ h)

private def encodeExactPattern {ι ρ : Type*} (v : (ℕ × (ι → ℕ)) × (ρ → ℕ)) :
    Option ι ⊕ ρ → ℕ :=
  Sum.elim (fun o => o.elim v.1.1 v.1.2) v.2

private theorem encodeExactPattern_injective {ι ρ : Type*} :
    Function.Injective (encodeExactPattern (ι := ι) (ρ := ρ)) := by
  intro a b h
  exact Prod.ext (Prod.ext (congrFun h (.inl none)) (funext fun i => congrFun h (.inl (some i))))
    (funext fun q => congrFun h (.inr q))

/-- Exact factorization of a bounded valuation density. -/
theorem hasNaturalDensity_finiteExactRuleSet {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (affected : Option ι → ℕ) (rough : ρ → ℕ) (C : Set (ℕ × (ι → ℕ))) (K : ℕ)
    (hinj : Function.Injective (Sum.elim affected rough))
    (hpa : ∀ o, (affected o).Prime) (hpr : ∀ q, (rough q).Prime) :
    HasNaturalDensity (finiteExactRuleSet affected rough C K)
      (exactPatternMass (1 / (affected none : ℝ)) (fun i => 1 / (affected (some i) : ℝ)) C K *
        exactRuleCommonWeight affected rough K) := by
  classical
  let p : Option ι ⊕ ρ → ℕ := Sum.elim affected rough
  let U := boundedExactPatterns C K
  let G := Fintype.piFinset fun _ : ρ => greedyExponentsBelow K
  let enc : ((ℕ × (ι → ℕ)) × (ρ → ℕ)) ↪ ((Option ι ⊕ ρ) → ℕ) :=
    ⟨encodeExactPattern, encodeExactPattern_injective⟩
  let P := (U ×ˢ G).map enc
  have hset : {n | n ≠ 0 ∧ (fun j => n.factorization (p j)) ∈ P} =
      finiteExactRuleSet affected rough C K := by
    ext n
    let a := (n.factorization (affected none), fun i => n.factorization (affected (some i)))
    let g (q : ρ) := n.factorization (rough q)
    have he : enc (a, g) = fun j => n.factorization (p j) := by
      funext j
      rcases j with o | q
      · cases o <;> rfl
      · rfl
    change (n ≠ 0 ∧ (fun j => n.factorization (p j)) ∈ P) ↔
      n ≠ 0 ∧ a ∈ U ∧ _
    rw [← he, show P = (U ×ˢ G).map enc from rfl, Finset.mem_map', Finset.mem_product]
    simp only [G, g, Fintype.mem_piFinset]
  have hprime (j : Option ι ⊕ ρ) : (p j).Prime := by
    rcases j with o | q
    · exact hpa o
    · exact hpr q
  let A := ∏ o, (1 - 1 / (affected o : ℝ))
  let W (v : ℕ × (ι → ℕ)) :=
    exactPatternWeight (1 / (affected none : ℝ)) (fun i => 1 / (affected (some i) : ℝ)) v
  let R (g : ρ → ℕ) := ∏ q, (1 - 1 / (rough q : ℝ)) * (1 / (rough q : ℝ)) ^ g q
  have hweight (v : (ℕ × (ι → ℕ)) × (ρ → ℕ)) :
      (∏ j, (1 - 1 / (p j : ℝ)) * (1 / (p j : ℝ)) ^ enc v j) = W v.1 * (A * R v.2) := by
    rw [Fintype.prod_sum_type]
    change (∏ o : Option ι, (1 - 1 / (affected o : ℝ)) *
      (1 / (affected o : ℝ)) ^ o.elim v.1.1 v.1.2) * R v.2 = _
    rw [Finset.prod_mul_distrib]
    have hW : (∏ o : Option ι, (1 / (affected o : ℝ)) ^ o.elim v.1.1 v.1.2) = W v.1 := by
      rw [Fintype.prod_option]
      rfl
    rw [hW]
    change (A * W v.1) * R v.2 = _
    ring
  have hR : (∑ g ∈ G, R g) = ∏ q, (1 - 1 / (rough q : ℝ)) *
      ∑ k ∈ greedyExponentsBelow K, (1 / (rough q : ℝ)) ^ k := by
    dsimp only [G, R]
    rw [← Finset.prod_univ_sum (fun _ : ρ => greedyExponentsBelow K)
      (fun q k => (1 - 1 / (rough q : ℝ)) * (1 / (rough q : ℝ)) ^ k)]
    simp only [Finset.mul_sum]
  have hmass :
      (∑ e ∈ P, ∏ j, (1 - 1 / (p j : ℝ)) * (1 / (p j : ℝ)) ^ e j) =
        (∑ v ∈ U, W v) * (A * ∑ g ∈ G, R g) := by
    unfold P
    rw [Finset.sum_map]
    simp_rw [Finset.sum_product, hweight, ← Finset.mul_sum, ← Finset.sum_mul]
  have hD := hasNaturalDensity_indexedValuationPatterns p hinj hprime P
  rw [hset, hmass, hR] at hD
  exact hD

end GRHArticle.ProgressionFree
