import GRHArticle.ProgressionFree.HeavyPrimeBlocks
import GRHArticle.ProgressionFree.ExteriorPrimeBlockDensity
import GRHArticle.ProgressionFree.IntegerPrimeBlockFreeness

/-!
# Reduction to finitely many exceptional prime blocks

For a finite selection of blocks, replace the light rules by their greedy
optimizers. Taking selections that cover every prime below a growing
cutoff bounds the original upper density by the natural density of the
reduced rule.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- Progression-freeness is preserved when finitely many disjoint blocks
are combined with an independent exterior rule. -/
theorem kTermGPFree_finiteExceptionPrimeRule {k : ℕ} (hk : 2 ≤ k)
    (H : Finset (Finset ℕ)) (rules : (P : Finset ℕ) → Set (↥P → ℕ))
    (hRule : ∀ P ∈ H, KTermVectorAPFree k (rules P))
    {G : Set ℕ} (hG : KTermAPFree k G) :
    KTermGPFree k (finiteExceptionPrimeRule H rules G) := by
  intro a u r hu _ ha hf
  obtain ⟨v,d,hAffine,hOne⟩ := exists_primeExponentAffine hk (fun i ↦ (ha i).1.1) hu hf
  apply hOne
  intro p hp
  by_cases hH : p ∈ H.biUnion id
  · obtain ⟨P,hP,hpP⟩ := mem_biUnion.mp hH
    exact hRule P hP (fun i q ↦ (a i).factorization q.val) (fun q ↦ v q.val)
      (fun q ↦ d q.val) (fun i ↦ (ha i).1.2 P hP) (fun i q ↦ hAffine i q.val) ⟨p,hpP⟩
  · exact hG (fun i ↦ (a i).factorization p) (v p) (d p) (fun i ↦ (ha i).2 p hp hH)
      (fun i ↦ hAffine i p)

private theorem integerUpperDensity_le_of_subset {A B : Set ℕ} (h : A ⊆ B)
    {d : ℝ} (hd : HasNaturalDensity B d) : integerUpperDensity A ≤ d := by
  unfold integerUpperDensity
  rw [← hd.limsup_eq]
  exact limsup_le_limsup (Eventually.of_forall (densityUpTo_mono h))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (densityUpTo_nonneg A))).isCoboundedUnder_le
    hd.isBoundedUnder_le

/-- The upper density of a nonempty width-`d` product is dominated by the
natural density of a rule with at most `d * π(2d)` exceptional primes. -/
theorem exists_dominating_finiteExceptionPrimeRule {k d : ℕ} (hk : 3 ≤ k) (hd : 0 < d)
    (π : PrimeBlockPartition) (rules : (P : Finset ℕ) → Set (↥P → ℕ))
    (hwidth : ∀ P ∈ π.blocks, P.card ≤ d)
    (hN : (integerPrimePartitionRule π rules).Nonempty)
    (hfree : KTermGPFree k (integerPrimePartitionRule π rules)) :
    ∃ (H : Finset (Finset ℕ)) (e : ℝ),
      (∀ P ∈ H, P ∈ π.blocks) ∧
      (∀ P ∈ H, KTermVectorAPFree k (rules P)) ∧
      (H.biUnion id).card ≤ d*(Nat.primesLE (2*d)).card ∧
      HasNaturalDensity (finiteExceptionPrimeRule H rules (greedyLengthExponents k)) e ∧
      integerUpperDensity (integerPrimePartitionRule π rules) ≤ e := by
  classical
  let G := greedyLengthExponents k
  have hG₀ : 0 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hG₁ : 1 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hRules := kTermVectorAPFree_of_integerPrimePartitionRule (by omega : 2 ≤ k) hN hfree
  obtain ⟨H,hH,_,hcard⟩ := exists_heavyPrimeBlocks π hd hwidth
  have hπ (P : Finset ℕ) (hP : P ∈ H) := ((hH P).mp hP).1
  have hpr (P : Finset ℕ) (hP : P ∈ H) := π.primes P (hπ P hP)
  have hPair : (H : Set (Finset ℕ)).PairwiseDisjoint id :=
    fun P hP Q hQ hne ↦ π.pairwiseDisjoint (hπ P hP) (hπ Q hQ) hne
  obtain ⟨e,he⟩ := exists_hasNaturalDensity_finiteExceptionPrimeRule H rules hG₀ hG₁ hpr hPair
  refine ⟨H,e,hπ,fun P hP ↦ hRules P (hπ P hP),hcard,he,?_⟩
  let replacement (P : Finset ℕ) : Set (↥P → ℕ) :=
    if P ∈ H then rules P else greedyExponentPatterns ↥P k
  choose block hb using π.covers
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N,hεN⟩ := exists_nat_one_div_lt hε
  let Y := N+1
  let P₀ := Nat.primesLE Y
  let T := H ∪ P₀.attach.image (fun p ↦ block p.val (Nat.prime_of_mem_primesLE p.property))
  have hT (P : Finset ℕ) (hP : P ∈ T) : P ∈ π.blocks := by
    rcases mem_union.mp hP with hP | hP
    · exact hπ P hP
    · obtain ⟨p,_,rfl⟩ := mem_image.mp hP
      exact (hb p.val (Nat.prime_of_mem_primesLE p.property)).1
  have hCov (p : ℕ) (hp : p ∈ P₀) : ∃ P ∈ T, p ∈ P :=
    ⟨block p (Nat.prime_of_mem_primesLE hp), mem_union_right _ (mem_image.mpr
      ⟨⟨p,hp⟩,mem_attach _ _,rfl⟩), (hb p (Nat.prime_of_mem_primesLE hp)).2⟩
  have htPr (P : Finset ℕ) (hP : P ∈ T) := π.primes P (hT P hP)
  have htPair : (T : Set (Finset ℕ)).PairwiseDisjoint id :=
    fun P hP Q hQ hne ↦ π.pairwiseDisjoint (hT P hP) (hT Q hQ) hne
  let dT (R : (P : Finset ℕ) → Set (↥P → ℕ)) := ∏ P ∈ T, primeBlockProbability P (R P)
  have hDensityT (R : (P : Finset ℕ) → Set (↥P → ℕ)) :
      HasNaturalDensity (finitePrimeBlockRule T R) (dT R) :=
    hasNaturalDensity_finitePrimeBlockRule T R htPr htPair
  have hUpper : integerUpperDensity (integerPrimePartitionRule π rules) ≤ dT rules :=
    integerUpperDensity_le_of_subset (by rintro n ⟨hn,h⟩; exact ⟨hn,fun P hP ↦ h P (hT P hP)⟩)
      (hDensityT rules)
  have hMass : dT rules ≤ dT replacement := by
    apply Finset.prod_le_prod (fun P hP ↦ primeBlockProbability_nonneg (htPr P hP) _)
    intro P hP
    by_cases hh : P ∈ H
    · rw [show replacement P = rules P from if_pos hh]
    · rw [show replacement P = greedyExponentPatterns ↥P k from if_neg hh]
      have hl : (∏ p : ↥P, (1-1/(p.val:ℝ))⁻¹) ≤ 2 := le_of_not_gt fun h ↦
        hh ((hH P).mpr ⟨hT P hP,h⟩)
      have hU (p : ↥P) : 1/(p.val:ℝ) < 1 :=
        (div_lt_one (by exact_mod_cast (htPr P hP _ p.property).pos)).mpr
          (by exact_mod_cast (htPr P hP _ p.property).one_lt)
      unfold primeBlockProbability
      exact mul_le_mul_of_nonneg_left
        (reciprocalExponentMass_le_greedy_of_light (by omega) (fun p ↦ by positivity)
          hU hl (hRules P (hT P hP)))
        (prod_nonneg fun p _ ↦ sub_nonneg.mpr (hU p).le)
  have hSubset : finiteExceptionPrimeRule H rules G ⊆ finitePrimeBlockRule T replacement := by
    rintro n ⟨⟨hn,hE⟩,hOut⟩
    refine ⟨hn,fun P hP ↦ ?_⟩
    by_cases hh : P ∈ H
    · rw [show replacement P = rules P from if_pos hh]
      exact hE P hh
    · rw [show replacement P = greedyExponentPatterns ↥P k from if_neg hh]
      intro p
      apply hOut p.val (htPr P hP p.val p.property)
      intro hp
      obtain ⟨Q,hQ,hpQ⟩ := mem_biUnion.mp hp
      have hne : P ≠ Q := fun heq ↦ hh (heq.symm ▸ hQ)
      exact (disjoint_left.mp (π.pairwiseDisjoint (hT P hP) (hπ Q hQ) hne)) p.property hpQ
  have hError (Z : ℕ) : |densityUpTo (finitePrimeBlockRule T replacement) Z -
      densityUpTo (finiteExceptionPrimeRule H rules G) Z| ≤ 1/(Y : ℝ) := by
    refine (densityUpTo_abs_sub_le_of_symmDiff_subset
      (E := {n | ∃ p, Y < p ∧ p.Prime ∧ p^2 ∣ n}) Z ?_).trans
      (densityUpTo_largePrimeSquare_le Y Z (Nat.succ_pos _))
    intro n hn
    rcases hn with ⟨hn,hBad⟩ | ⟨hn,hBad⟩
    · by_contra hSquare
      apply hBad
      refine ⟨⟨hn.1,fun P hP ↦ ?_⟩,fun p hp hOut ↦ ?_⟩
      · have h := hn.2 P (mem_union_left _ hP)
        rw [show replacement P = rules P from if_pos hP] at h
        exact h
      · by_cases hpY : p ≤ Y
        · obtain ⟨P,hP,hpP⟩ := hCov p (Nat.mem_primesLE.mpr ⟨hpY,hp⟩)
          have hPH : P ∉ H := fun hh ↦ hOut (mem_biUnion.mpr ⟨P,hh,hpP⟩)
          have hf := hn.2 P hP
          rw [show replacement P = greedyExponentPatterns ↥P k from if_neg hPH] at hf
          exact hf ⟨p,hpP⟩
        · have hSmall : n.factorization p < 2 := by
            by_contra! h
            exact hSquare ⟨p,lt_of_not_ge hpY,hp,(hp.pow_dvd_iff_le_factorization hn.1).mpr h⟩
          rcases (show n.factorization p = 0 ∨ n.factorization p = 1 by omega) with h | h
          · exact h.symm ▸ hG₀
          · exact h.symm ▸ hG₁
    · exact (hBad (hSubset hn)).elim
  have hdist : |dT replacement-e| ≤ 1/(Y : ℝ) :=
    le_of_tendsto' ((hDensityT replacement).sub he).abs hError
  have hε' : 1/(Y : ℝ) < ε := by exact_mod_cast hεN
  exact hUpper.trans (hMass.trans (by linarith only [(abs_le.mp hdist).2,hε']))

end GRHArticle.ProgressionFree
