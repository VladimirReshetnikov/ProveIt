import GRHArticle.ProgressionFree.GreedyBlockWitnesses
import GRHArticle.ProgressionFree.IntegerDensityExtrema

/-!
# Prime partitions and their integer rule sets

A prime partition covers every prime exactly once by a nonempty finite
block. A rule on each block tests the vector of valuations of a positive
integer on that block.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter

/-- A partition of all rational primes into nonempty finite sets. -/
structure PrimeBlockPartition where
  blocks : Set (Finset ℕ)
  nonempty : ∀ P ∈ blocks, P.Nonempty
  primes : ∀ P ∈ blocks, ∀ p ∈ P, p.Prime
  covers : ∀ p : ℕ, p.Prime → ∃ P ∈ blocks, p ∈ P
  pairwiseDisjoint : blocks.PairwiseDisjoint id

/-- The actual set of integers satisfying one rule per block. -/
def integerPrimePartitionRule (π : PrimeBlockPartition)
    (rules : (P : Finset ℕ) → Set (↥P → ℕ)) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ P ∈ π.blocks, (fun p : ↥P ↦ n.factorization p.val) ∈ rules P}

/-- A prime partition in which every block has at most `d` coordinates. -/
def IntegerBoundedPrimeBlockSet (d : ℕ) (A : Set ℕ) : Prop :=
  ∃ π : PrimeBlockPartition, ∃ rules : (P : Finset ℕ) → Set (↥P → ℕ),
    (∀ P ∈ π.blocks, P.card ≤ d) ∧ A = integerPrimePartitionRule π rules

/-- The bounded-block upper-density extremum of the article. -/
noncomputable def integerBoundedPrimeBlockDensitySupremum (k d : ℕ) : ℝ :=
  sSup {a | ∃ A, IntegerBoundedPrimeBlockSet d A ∧ KTermGPFree k A ∧ a = integerUpperDensity A}

/-- The unrestricted natural-density extremum at length `k`. -/
noncomputable def integerLengthNaturalDensitySupremum (k : ℕ) : ℝ :=
  sSup {a | ∃ A : Set ℕ, 0 ∉ A ∧ KTermGPFree k A ∧ HasNaturalDensity A a}

/-- The positive integers satisfying one rule at each prime separately. -/
def integerIndependentPrimeRules (rules : ℕ → Set ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p : ℕ, p.Prime → n.factorization p ∈ rules p}

/-- The partition with one prime in each block. -/
def singletonPrimeBlockPartition : PrimeBlockPartition where
  blocks := {P | ∃ p : ℕ, p.Prime ∧ P = {p}}
  nonempty := by rintro P ⟨p,_,rfl⟩; exact singleton_nonempty _
  primes := by
    rintro P ⟨p,hp,rfl⟩ q hq
    exact (mem_singleton.mp hq).symm ▸ hp
  covers := fun p hp ↦ ⟨{p},⟨p,hp,rfl⟩,mem_singleton_self _⟩
  pairwiseDisjoint := by
    rintro P ⟨p,_,rfl⟩ Q ⟨q,_,rfl⟩ h
    exact disjoint_singleton.mpr (fun e ↦ h (congrArg singleton e))

/-- Lift separate exponent rules to rules on finite blocks. At the singleton
partition this imposes each rule on precisely its own prime. -/
def blockwiseIndependentRules (R : ℕ → Set ℕ) (P : Finset ℕ) : Set (↥P → ℕ) :=
  {v | ∀ p, v p ∈ R p.val}

theorem integerPrimePartitionRule_singleton (R : ℕ → Set ℕ) :
    integerPrimePartitionRule singletonPrimeBlockPartition (blockwiseIndependentRules R) =
      integerIndependentPrimeRules R := by
  ext n
  constructor
  · rintro ⟨hn,h⟩
    exact ⟨hn, fun p hp ↦ h {p} ⟨p,hp,rfl⟩ ⟨p,mem_singleton_self _⟩⟩
  · rintro ⟨hn,h⟩
    refine ⟨hn,?_⟩
    rintro P ⟨p,hp,rfl⟩ q
    have hq := mem_singleton.mp q.property
    change n.factorization q.val ∈ R q.val
    rw [hq]
    exact h p hp

/-- Independent prime rules are precisely the rules of width one. -/
theorem integerBoundedPrimeBlockSet_one_iff {A : Set ℕ} :
    IntegerBoundedPrimeBlockSet 1 A ↔ ∃ rules : ℕ → Set ℕ, A = integerIndependentPrimeRules rules := by
  classical
  constructor
  · rintro ⟨π,rules,hwidth,rfl⟩
    let R (p : ℕ) : Set ℕ := {a | (fun _ : ↥({p} : Finset ℕ) ↦ a) ∈ rules {p}}
    have hs (P : Finset ℕ) (hP : P ∈ π.blocks) (p : ℕ) (hp : p ∈ P) : P = {p} := by
      ext q
      simp only [mem_singleton]
      constructor
      · intro hq
        exact card_le_one.mp (hwidth P hP) q hq p hp
      · rintro rfl
        exact hp
    refine ⟨R, ?_⟩
    ext n
    constructor
    · rintro ⟨hn,hπ⟩
      refine ⟨hn, fun p hp ↦ ?_⟩
      obtain ⟨P,hP,hpP⟩ := π.covers p hp
      have hP' : ({p} : Finset ℕ) ∈ π.blocks := hs P hP p hpP ▸ hP
      have he : (fun q : ↥({p} : Finset ℕ) ↦ n.factorization q.val) =
          (fun _ : ↥({p} : Finset ℕ) ↦ n.factorization p) := by
        funext q
        rw [mem_singleton.mp q.property]
      change (fun _ : ↥({p} : Finset ℕ) ↦ n.factorization p) ∈ rules {p}
      rw [← he]
      exact hπ _ hP'
    · rintro ⟨hn,hR⟩
      refine ⟨hn, fun P hP ↦ ?_⟩
      obtain ⟨p,hpP⟩ := π.nonempty P hP
      have hp := π.primes P hP p hpP
      have h := hR p hp
      have he := hs P hP p hpP
      subst P
      have heq : (fun q : ↥({p} : Finset ℕ) ↦ n.factorization q.val) =
          (fun _ : ↥({p} : Finset ℕ) ↦ n.factorization p) := by
        funext q
        rw [mem_singleton.mp q.property]
      exact heq.symm ▸ h
  · rintro ⟨R,rfl⟩
    refine ⟨singletonPrimeBlockPartition, blockwiseIndependentRules R, ?_,
      (integerPrimePartitionRule_singleton R).symm⟩
    rintro P ⟨p,_,rfl⟩
    simp

/-- Independent greedy conditions give a width-one rule. -/
theorem integerBoundedPrimeBlockSet_greedyLength (k : ℕ) :
    IntegerBoundedPrimeBlockSet 1 (integerGreedyLengthSet k) :=
  integerBoundedPrimeBlockSet_one_iff.mpr ⟨fun _ ↦ greedyLengthExponents k,rfl⟩

/-- If every block has a progression-free rule, the resulting positive
integers are progression-free for positive rational ratios. -/
theorem kTermGPFree_integerPrimePartitionRule {k : ℕ} (hk : 2 ≤ k)
    (π : PrimeBlockPartition) (rules : (P : Finset ℕ) → Set (↥P → ℕ))
    (hrules : ∀ P ∈ π.blocks, KTermVectorAPFree k (rules P)) :
    KTermGPFree k (integerPrimePartitionRule π rules) := by
  intro a u r hu _ ha hf
  obtain ⟨v,d,hAffine,hOne⟩ := exists_primeExponentAffine hk (fun i ↦ (ha i).1) hu hf
  apply hOne
  intro p hp
  obtain ⟨P,hP,hpP⟩ := π.covers p hp
  exact hrules P hP (fun i q ↦ (a i).factorization q.val) (fun q ↦ v q.val)
    (fun q ↦ d q.val) (fun i ↦ (ha i).2 P hP) (fun i q ↦ hAffine i q.val) ⟨p,hpP⟩

end GRHArticle.ProgressionFree
