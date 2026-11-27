import GRHArticle.ProgressionFree.IntegerPrimeBlockPartitions

/-!
# Progression-freeness of individual prime blocks

A admitted positive integer provides fixed exponents outside any block.
Replacing the block's exponents along an affine progression would produce
a rational-ratio geometric progression in the complete integer set.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- If every prime exponent varies affinely, the positive integers form a
rational-ratio progression. A unit ratio forces every prime step to vanish. -/
theorem rationalGP_of_primeExponentAffine {k : ℕ} (hk : 2 ≤ k) {a : Fin k → ℕ}
    (ha : ∀ i, a i ≠ 0) {u d : ℕ → ℤ}
    (hf : ∀ i p, p.Prime → ((a i).factorization p : ℤ) = u p + (i.val : ℤ)*d p) :
    ∃ (b r : ℚ), 0 < b ∧ 0 < r ∧ (∀ i, (a i : ℚ) = b*r^i.val) ∧
      (r = 1 → ∀ p, p.Prime → d p = 0) := by
  let i₀ : Fin k := ⟨0,by omega⟩
  let i₁ : Fin k := ⟨1,by omega⟩
  have hq₀ : (0 : ℚ) < a i₀ := by exact_mod_cast Nat.pos_of_ne_zero (ha i₀)
  have hq₁ : (0 : ℚ) < a i₁ := by exact_mod_cast Nat.pos_of_ne_zero (ha i₁)
  have hN (i : Fin k) : a i * (a i₀)^i.val = a i₀ * (a i₁)^i.val := by
    apply Nat.factorization_inj (mul_ne_zero (ha i) (pow_ne_zero _ (ha i₀)))
      (mul_ne_zero (ha i₀) (pow_ne_zero _ (ha i₁)))
    rw [Nat.factorization_mul (ha i) (pow_ne_zero _ (ha i₀)),
      Nat.factorization_mul (ha i₀) (pow_ne_zero _ (ha i₁)), Nat.factorization_pow,
      Nat.factorization_pow]
    ext p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
    by_cases hp : p.Prime
    · have h₀ : ((a i₀).factorization p : ℤ) = u p := by simpa [i₀] using hf i₀ p hp
      have h₁ : ((a i₁).factorization p : ℤ) = u p + d p := by simpa [i₁] using hf i₁ p hp
      exact_mod_cast (show ((a i).factorization p : ℤ) + (i.val : ℤ)*(a i₀).factorization p =
        ((a i₀).factorization p : ℤ) + (i.val : ℤ)*(a i₁).factorization p by
        rw [hf i p hp,h₀,h₁]
        ring)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  let r : ℚ := (a i₁ : ℚ) / (a i₀ : ℚ)
  have hr : 0 < r := div_pos hq₁ hq₀
  have hA (i : Fin k) : (a i : ℚ) = (a i₀ : ℚ)*r^i.val := by
    dsimp [r]
    rw [div_pow, ← mul_div_assoc]
    exact (eq_div_iff (pow_ne_zero _ hq₀.ne')).2 (by exact_mod_cast hN i)
  refine ⟨a i₀,r,hq₀,hr,hA,fun hr1 p hp ↦ ?_⟩
  have he : a i₁ = a i₀ := by
    exact_mod_cast (show (a i₁ : ℚ) = (a i₀ : ℚ) by simpa [hr1] using hA i₁)
  have h₀ : ((a i₀).factorization p : ℤ) = u p := by simpa [i₀] using hf i₀ p hp
  have h₁ : ((a i₁).factorization p : ℤ) = u p + d p := by simpa [i₁] using hf i₁ p hp
  rw [he,h₀] at h₁
  omega

private def blockExponent (P : Finset ℕ) (v : ↥P → ℕ) (p : ℕ) : ℕ :=
  if hp : p ∈ P then v ⟨p,hp⟩ else 0

private def blockProduct (P : Finset ℕ) (v : ↥P → ℕ) : ℕ :=
  ∏ p ∈ P, p ^ blockExponent P v p

private theorem blockProduct_ne_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (v : ↥P → ℕ) : blockProduct P v ≠ 0 :=
  prod_ne_zero_iff.mpr fun p hp ↦ pow_ne_zero _ (hP p hp).ne_zero

private theorem factorization_blockProduct {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (v : ↥P → ℕ) (q : ℕ) : (blockProduct P v).factorization q = blockExponent P v q := by
  unfold blockProduct
  rw [Nat.factorization_prod_apply (fun p hp ↦ pow_ne_zero _ (hP p hp).ne_zero)]
  calc
    _ = ∑ p ∈ P, if p = q then blockExponent P v p else 0 := by
      apply sum_congr rfl
      intro p hp
      rw [(hP p hp).factorization_pow,Finsupp.single_apply]
    _ = _ := by
      rw [Finset.sum_ite_eq']
      by_cases hq : q ∈ P <;> simp [blockExponent,hq]

private theorem exists_replace_block_exponents {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : n ≠ 0) (v : ↥P → ℕ) :
    ∃ m : ℕ, m ≠ 0 ∧
      ∀ p : ℕ, m.factorization p = if hp : p ∈ P then v ⟨p,hp⟩ else n.factorization p := by
  let w (p : ↥P) := n.factorization p.val
  let t := blockProduct P w
  have ht := blockProduct_ne_zero hP w
  have hfac : t.factorization ≤ n.factorization := by
    intro p
    rw [factorization_blockProduct hP]
    by_cases hp : p ∈ P <;> simp [blockExponent,hp,w]
  have hdvd : t ∣ n := (Nat.factorization_le_iff_dvd ht hn).mp hfac
  let s := n/t
  have hs : s ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)
    (Nat.pos_of_ne_zero ht)).ne'
  refine ⟨s*blockProduct P v, mul_ne_zero hs (blockProduct_ne_zero hP v), fun p ↦ ?_⟩
  rw [Nat.factorization_mul hs (blockProduct_ne_zero hP v), Finsupp.add_apply,
    factorization_blockProduct hP]
  simp only [s,Nat.factorization_div hdvd,Finsupp.tsub_apply]
  by_cases hp : p ∈ P <;> simp [blockExponent,hp,t,w,factorization_blockProduct hP]

/-- Every block rule of a nonempty progression-free integer product is itself
free of nonconstant signed progressions of exponent vectors. -/
theorem kTermVectorAPFree_of_integerPrimePartitionRule {k : ℕ} (hk : 2 ≤ k)
    {π : PrimeBlockPartition} {rules : (P : Finset ℕ) → Set (↥P → ℕ)}
    (hnon : (integerPrimePartitionRule π rules).Nonempty)
    (hfree : KTermGPFree k (integerPrimePartitionRule π rules)) :
    ∀ P ∈ π.blocks, KTermVectorAPFree k (rules P) := by
  classical
  obtain ⟨n,hnn,hnRules⟩ := hnon
  intro P hP x u d hx hAffine
  choose a ha hfa using fun i ↦ exists_replace_block_exponents (π.primes P hP) hnn (x i)
  have hm (i : Fin k) : a i ∈ integerPrimePartitionRule π rules := by
    refine ⟨ha i, fun Q hQ ↦ ?_⟩
    by_cases hQP : Q = P
    · subst Q
      have he : (fun q : ↥P ↦ (a i).factorization q.val) = x i := by
        funext q
        rw [hfa i, dif_pos q.property]
      rw [he]
      exact hx i
    · have hd := π.pairwiseDisjoint hQ hP hQP
      have he : (fun q : ↥Q ↦ (a i).factorization q.val) =
          (fun q : ↥Q ↦ n.factorization q.val) := by
        funext q
        have hq : q.val ∉ P := fun hp ↦ (disjoint_left.mp hd) q.property hp
        rw [hfa i, dif_neg hq]
      exact he.symm ▸ hnRules Q hQ
  let u' (p : ℕ) : ℤ := if hp : p ∈ P then u ⟨p,hp⟩ else n.factorization p
  let d' (p : ℕ) : ℤ := if hp : p ∈ P then d ⟨p,hp⟩ else 0
  have hF (i : Fin k) (p : ℕ) (_ : p.Prime) :
      ((a i).factorization p : ℤ) = u' p + (i.val : ℤ)*d' p := by
    rw [hfa i]
    by_cases hp : p ∈ P
    · simpa only [u',d',dif_pos hp] using hAffine i ⟨p,hp⟩
    · simp [u',d',hp]
  obtain ⟨b,r,hb,hr,hR,hconst⟩ := rationalGP_of_primeExponentAffine hk ha hF
  have hd (p : ℕ) (hp : p.Prime) := hconst (hfree a b r hb hr hm hR) p hp
  intro q
  simpa only [d',dif_pos q.property] using hd q.val (π.primes P hP q.val q.property)

/-- Every individual rule of a nonempty, progression-free independent
prime product excludes signed exponent progressions. -/
theorem kTermAPFree_of_integerIndependentPrimeRules {k : ℕ} (hk : 2 ≤ k)
    {R : ℕ → Set ℕ} (hn : (integerIndependentPrimeRules R).Nonempty)
    (hA : KTermGPFree k (integerIndependentPrimeRules R)) {p : ℕ} (hp : p.Prime) :
    KTermAPFree k (R p) := by
  rw [← integerPrimePartitionRule_singleton] at hn hA
  have h := kTermVectorAPFree_of_integerPrimePartitionRule hk hn hA {p} ⟨p,hp,rfl⟩
  intro x a d hx ha
  refine h (fun i _ ↦ x i) (fun _ ↦ a) (fun _ ↦ d) ?_ (fun i _ ↦ ha i) ⟨p, mem_singleton_self _⟩
  intro i q
  change x i ∈ R q.val
  rw [mem_singleton.mp q.property]
  exact hx i

end GRHArticle.ProgressionFree
