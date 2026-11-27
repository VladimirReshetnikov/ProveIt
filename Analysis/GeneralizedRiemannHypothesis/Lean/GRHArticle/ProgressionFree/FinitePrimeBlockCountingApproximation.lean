import GRHArticle.ProgressionFree.ExteriorPrimeBlockDensity

/-!
# Finite counting approximations for reduced block rules

Bound the tested exponents and retain the independent exterior tests only
at the primes up to a second cutoff. The resulting density is a finite
product and has a uniform error bound from divisibility by prime powers.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- The probability of a singleton block is its ordinary exponent mass
multiplied by the geometric normalization. -/
theorem primeBlockProbability_singleton_eq_exponentRuleMass (p : ℕ) (G : Set ℕ) :
    primeBlockProbability {p} (blockwiseIndependentRules (fun _ ↦ G) {p}) =
      (1-1/(p : ℝ))*exponentRuleMass (1/(p : ℝ)) G := by
  let P : Finset ℕ := {p}
  let q₀ : ↥P := ⟨p,mem_singleton_self _⟩
  letI : Unique ↥P :=
    { default := q₀
      uniq := fun q ↦ Subtype.ext (mem_singleton.mp q.property) }
  let A := blockwiseIndependentRules (fun _ ↦ G) P
  let e : G ≃ A :=
    { toFun := fun n ↦ ⟨fun _ ↦ n.val,fun _ ↦ n.property⟩
      invFun := fun v ↦ ⟨v.val q₀,v.property q₀⟩
      left_inv := fun _ ↦ rfl
      right_inv := by intro v; apply Subtype.ext; funext q; rw [Unique.eq_default q]; rfl }
  change primeBlockProbability P A = _
  unfold primeBlockProbability
  rw [Fintype.prod_unique,reciprocalExponentMass_eq_tsum_subtype,← e.tsum_eq]
  congr 1
  unfold exponentRuleMass
  apply tsum_congr
  intro n
  rw [reciprocalExponentWeight,Fintype.prod_unique]
  rfl

/-- The tested exterior primes below the finite counting cutoff. -/
def finiteBlockExteriorPrimes (S : Finset (Finset ℕ)) (U : ℕ) : Finset ℕ :=
  Nat.primesLE U \ S.biUnion id

/-- The doubly truncated counting set of an exceptional prime-block rule. -/
noncomputable def finiteExceptionPrimeRuleApproximation (S : Finset (Finset ℕ))
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ) (U L : ℕ) : Set ℕ :=
  finitePrimeBlockRule S (fun P ↦ (blockPatternsBelow (R P) L : Set (↥P → ℕ))) ∩
    integerFiniteIndependentPrimeRules (finiteBlockExteriorPrimes S U)
      (fun _ ↦ (exponentsBelow G L : Set ℕ))

/-- The finite product density of a truncated counting set. -/
noncomputable def finiteExceptionPrimeRuleApproximationDensity (S : Finset (Finset ℕ))
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ) (U L : ℕ) : ℝ :=
  (∏ P ∈ S, primeBlockProbability P (blockPatternsBelow (R P) L : Set (↥P → ℕ))) *
    ∏ p ∈ finiteBlockExteriorPrimes S U, (1-1/(p : ℝ)) *
      ∑ e ∈ exponentsBelow G L, (1/(p : ℝ))^e

theorem hasNaturalDensity_finiteExceptionPrimeRuleApproximation (S : Finset (Finset ℕ))
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) (G : Set ℕ) (U L : ℕ)
    (hpr : ∀ P ∈ S, ∀ p ∈ P, p.Prime) (hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id) :
    HasNaturalDensity (finiteExceptionPrimeRuleApproximation S R G U L)
      (finiteExceptionPrimeRuleApproximationDensity S R G U L) := by
  let T := finiteBlockExteriorPrimes S U
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime := Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1
  have hDis : Disjoint T (S.biUnion id) :=
    disjoint_left.mpr fun _ hp hS ↦ (mem_sdiff.mp hp).2 hS
  have h := hasNaturalDensity_mixedBlockRule S
    (fun P ↦ (blockPatternsBelow (R P) L : Set (↥P → ℕ))) (exponentsBelow G L : Set ℕ) T hpr hPair hT hDis
  have hsum (p : ℕ) :
      exponentRuleMass (1/(p : ℝ)) (exponentsBelow G L : Set ℕ) =
        ∑ e ∈ exponentsBelow G L, (1/(p : ℝ))^e :=
    Finset.tsum_subtype (exponentsBelow G L) (fun e : ℕ ↦ (1/(p : ℝ))^e)
  simpa only [finiteExceptionPrimeRuleApproximation,finiteExceptionPrimeRuleApproximationDensity,T,
    primeBlockProbability_singleton_eq_exponentRuleMass,hsum] using h

/-- Uniform density error from untested primes and truncated exponents. -/
theorem densityUpTo_finiteExceptionPrimeRuleApproximation_error {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    (S : Finset (Finset ℕ)) (R : (P : Finset ℕ) → Set (↥P → ℕ)) (U L N : ℕ) (hU : 0 < U)
    (hCover : ∀ P ∈ S, P ⊆ Nat.primesLE U) :
    |densityUpTo (finiteExceptionPrimeRule S R G) N -
      densityUpTo (finiteExceptionPrimeRuleApproximation S R G U L) N| ≤
      1/(U : ℝ) + ∑ p ∈ Nat.primesLE U, 1/(p : ℝ)^L := by
  let E : Set ℕ := {n | ∃ p, U < p ∧ p.Prime ∧ p^2 ∣ n}
  let F : Set ℕ := {n | ∃ p ∈ Nat.primesLE U, p^L ∣ n}
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset (E := E∪F) N ?_).trans
    ((densityUpTo_union_le E F N).trans (add_le_add (densityUpTo_largePrimeSquare_le U N hU) ?_))
  · intro n hn
    rcases hn with ⟨h,h'⟩ | ⟨h,h'⟩
    · right
      by_contra hBig
      apply h'
      have hsmall (p : ℕ) (hp : p ∈ Nat.primesLE U) : n.factorization p < L := by
        by_contra! hle
        exact hBig ⟨p,hp,((Nat.prime_of_mem_primesLE hp).pow_dvd_iff_le_factorization h.1.1).mpr hle⟩
      refine ⟨⟨h.1.1,fun P hP ↦ mem_blockPatternsBelow.mpr ⟨h.1.2 P hP,fun p ↦ hsmall _ (hCover P hP p.property)⟩⟩,
        ⟨h.1.1,fun p ↦ mem_exponentsBelow.mpr ?_⟩⟩
      have hp := mem_sdiff.mp p.property
      exact ⟨h.2 _ (Nat.prime_of_mem_primesLE hp.1) hp.2,hsmall _ hp.1⟩
    · left
      by_contra hBig
      apply h'
      refine ⟨⟨h.1.1,fun P hP ↦ (mem_blockPatternsBelow.mp (h.1.2 P hP)).1⟩,
        fun p hp hpOut ↦ ?_⟩
      by_cases hle : p ≤ U
      · exact (mem_exponentsBelow.mp
          (h.2.2 ⟨p,mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hle,hp⟩,hpOut⟩⟩)).1
      · have hsmall : n.factorization p < 2 := by
          by_contra! hle'
          exact hBig ⟨p,lt_of_not_ge hle,hp,(hp.pow_dvd_iff_le_factorization h.1.1).mpr hle'⟩
        rcases (show n.factorization p = 0 ∨ n.factorization p = 1 by omega) with he | he
        · exact he.symm ▸ h0
        · exact he.symm ▸ h1
  · simpa only [F,Nat.cast_pow] using
      densityUpTo_divisibleByOneOf_le (Nat.primesLE U) (fun p ↦ p^L) N
        (fun p hp ↦ pow_pos (Nat.prime_of_mem_primesLE hp).pos _)

/-- The same error bounds the finite approximation to the true density. -/
theorem finiteExceptionPrimeRuleApproximationDensity_error {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G)
    (S : Finset (Finset ℕ)) (R : (P : Finset ℕ) → Set (↥P → ℕ)) (U L : ℕ) (hU : 0 < U)
    (hCover : ∀ P ∈ S, P ⊆ Nat.primesLE U)
    (hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    {e : ℝ} (he : HasNaturalDensity (finiteExceptionPrimeRule S R G) e) :
    |e-finiteExceptionPrimeRuleApproximationDensity S R G U L| ≤
      1/(U : ℝ) + ∑ p ∈ Nat.primesLE U, 1/(p : ℝ)^L := by
  have h := hasNaturalDensity_finiteExceptionPrimeRuleApproximation S R G U L
    (fun P hP p hp ↦ Nat.prime_of_mem_primesLE (hCover P hP hp)) hPair
  exact le_of_tendsto' (he.sub h).abs (fun N ↦
    densityUpTo_finiteExceptionPrimeRuleApproximation_error h0 h1 S R U L N hU hCover)

end GRHArticle.ProgressionFree
