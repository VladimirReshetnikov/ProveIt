import GRHArticle.ProgressionFree.PrimeBlockDensityUpgrade
import GRHArticle.ProgressionFree.GreedyLengthDensityGain

/-!
# Mutually disjoint improving prime blocks

The shared-deletion exchange supplies an improving local block outside
any finite set of primes. A finite family of mutually disjoint such blocks
therefore gives a positive uniform gain whenever only a bounded number of
primes are unavailable.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- One local block rule with greater probability than the greedy rule. -/
structure ImprovingPrimeBlock (k : ℕ) where
  primes : Finset ℕ
  nonempty : primes.Nonempty
  primeOfMem : ∀ p ∈ primes, p.Prime
  rule : Set (↥primes → ℕ)
  free : KTermVectorAPFree k rule
  gain : primeBlockProbability primes (greedyExponentPatterns ↥primes k) <
    primeBlockProbability primes rule

private def sharedBlockSlot (marker : ℕ) (B : Finset ℕ) : Option ↥B → ↥(insert marker B)
  | none => ⟨marker,mem_insert_self _ _⟩
  | some q => ⟨q.val,mem_insert_of_mem q.property⟩

private theorem sharedBlockSlot_surjective (marker : ℕ) (B : Finset ℕ) :
    Function.Surjective (sharedBlockSlot marker B) := by
  intro q
  rcases mem_insert.mp q.property with he | hq
  · exact ⟨none,Subtype.ext he.symm⟩
  · exact ⟨some ⟨q.val,hq⟩,Subtype.ext rfl⟩

/-- There is a probability-improving local block outside any finite set of
primes. The greedy density is positive. -/
theorem exists_improvingPrimeBlock_avoiding {k : ℕ} (hk : 3 ≤ k) {dG : ℝ}
    (hG : HasNaturalDensity (integerGreedyLengthSet k) dG) (F : Finset ℕ) :
    0 < dG ∧ ∃ E : ImprovingPrimeBlock k, Disjoint E.primes F := by
  obtain ⟨marker,B,dG',dE,hm,_,hDis,hB,_,hG',hE,hlt⟩ :=
    exists_integerGreedyLengthExchange_strictNaturalDensityGain hk F
  have hDg : dG' = dG := tendsto_nhds_unique hG' hG
  subst dG'
  let P := insert marker B
  let slot := sharedBlockSlot marker B
  let G := greedyLengthExponents k
  let C : Set (↥P → ℕ) := {v | (fun q ↦ v (slot q)) ∈ sharedDeletionRule (k-2) G}
  let base (Q : Finset ℕ) : Set (↥Q → ℕ) := Set.univ
  let R := Function.update base P C
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (mem_insert.mp hp).elim
    (fun h ↦ h.symm ▸ hm) (fun h ↦ hB p h)
  have hS (Q : Finset ℕ) (hQ : Q ∈ ({P} : Finset (Finset ℕ))) :
      ∀ p ∈ Q, p.Prime := by
    have he := mem_singleton.mp hQ
    rw [he]
    exact hP
  have hpair : (({P} : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro Q hQ Q' hQ' hn
    exact (hn ((mem_singleton.mp hQ).trans (mem_singleton.mp hQ').symm)).elim
  have hFree : KTermVectorAPFree k C := by
    have hb : k-2 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
    have hb' : k-2+1 ∉ G := by
      change k-2+1 ∉ greedyLengthExponents k
      rw [show k-2+1 = k-1 by omega]
      exact not_mem_greedyLengthExponents_pred (by omega)
    intro x u d hx ha q
    obtain ⟨o,ho⟩ := sharedBlockSlot_surjective marker B q
    exact ho ▸ sharedDeletionRule_step_zero hk (kTermAPFree_greedyLengthExponents (by omega))
      hb hb' (fun i ↦ hx i) (fun i t ↦ ha i (slot t)) o
  have hUnion : ({P} : Finset (Finset ℕ)).biUnion id = P := by
    ext p
    simp only [mem_biUnion,mem_singleton,id_eq,exists_eq_left]
  have hLocal (n : ℕ) : (fun p : ↥P ↦ n.factorization p.val) ∈ C ↔
      (fun o ↦ n.factorization (sharedDeletionPrime marker B o)) ∈ sharedDeletionRule (k-2) G := by
    have he : (fun o ↦ n.factorization (slot o).val) =
        fun o ↦ n.factorization (sharedDeletionPrime marker B o) := by
      funext o
      cases o <;> rfl
    change (fun o ↦ n.factorization (slot o).val) ∈ sharedDeletionRule (k-2) G ↔
      (fun o ↦ n.factorization (sharedDeletionPrime marker B o)) ∈ sharedDeletionRule (k-2) G
    rw [he]
  have hEq : finiteExceptionPrimeRule {P} R G = integerGreedyLengthExchange k marker B := by
    ext n
    constructor
    · rintro ⟨⟨hn,hLocalR⟩,hOut⟩
      have hL := hLocalR P (mem_singleton_self P)
      rw [show R P = C from Function.update_self _ _ _] at hL
      refine ⟨hn,(hLocal n).mp hL,fun p hp hpm hpB ↦ hOut p hp ?_⟩
      rw [hUnion]
      exact fun h ↦ (mem_insert.mp h).elim hpm hpB
    · rintro ⟨hn,hLocalR,hOut⟩
      refine ⟨⟨hn,fun Q hQ ↦ ?_⟩,fun p hp hOut' ↦ ?_⟩
      · have he := mem_singleton.mp hQ
        subst Q
        rw [show R P = C from Function.update_self _ _ _]
        exact (hLocal n).mpr hLocalR
      · rw [hUnion] at hOut'
        exact hOut p hp (fun h ↦ hOut' (mem_insert.mpr (Or.inl h)))
          (fun h ↦ hOut' (mem_insert_of_mem h))
  have hD : HasNaturalDensity (finiteExceptionPrimeRule {P} R G) dE := hEq.symm ▸ hE
  have hmul := finiteExceptionPrimeRule_density_relative_greedy hk R hS hpair hD hG
  rw [prod_singleton,prod_singleton,show R P = C from Function.update_self _ _ _] at hmul
  have h0 : 0 ≤ dG := ge_of_tendsto' hG (densityUpTo_nonneg _)
  have hPG := primeBlockProbability_greedy_pos (k := k) (by omega) hP
  have hdG : 0 < dG := by
    by_contra! hn
    have hzero : dG = 0 := le_antisymm hn h0
    rw [hzero,zero_mul] at hmul
    have hdE : 0 < dE := hzero ▸ hlt
    exact (mul_pos hdE hPG).ne' hmul
  have hProb : primeBlockProbability P (greedyExponentPatterns ↥P k) < primeBlockProbability P C := by
    by_contra! h
    have h₁ := mul_le_mul_of_nonneg_left h h0
    have h₂ := mul_lt_mul_of_pos_right hlt hPG
    linarith only [h₁,h₂,hmul]
  exact ⟨hdG,⟨⟨P,⟨marker,mem_insert_self _ _⟩,hP,C,hFree,hProb⟩,hDis⟩⟩

/-- Replicate the improving-block construction on any finite number of
mutually disjoint blocks. -/
theorem exists_disjoint_improvingPrimeBlocks {k : ℕ} (hk : 3 ≤ k) {dG : ℝ}
    (hG : HasNaturalDensity (integerGreedyLengthSet k) dG) (n : ℕ) :
    ∃ E : Fin n → ImprovingPrimeBlock k, Pairwise (fun i j ↦ Disjoint (E i).primes (E j).primes) := by
  induction n with
  | zero =>
    let E : Fin 0 → ImprovingPrimeBlock k := Fin.elim0
    exact ⟨E,fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨E,hPair⟩ := ih
    let U : Finset ℕ := (univ : Finset (Fin n)).biUnion fun i ↦ (E i).primes
    obtain ⟨_,P,hP⟩ := exists_improvingPrimeBlock_avoiding hk hG U
    have hOld (i : Fin n) : Disjoint P.primes (E i).primes := disjoint_left.mpr fun p hp hi ↦
      (disjoint_left.mp hP) hp (mem_biUnion.mpr ⟨i,mem_univ _,hi⟩)
    refine ⟨Fin.cons P E,fun i j hij ↦ ?_⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i',rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j',rfl⟩
    · exact (hij rfl).elim
    · simpa only [Fin.cons_zero,Fin.cons_succ] using hOld j'
    · simpa only [Fin.cons_zero,Fin.cons_succ] using (hOld i').symm
    · simpa only [Fin.cons_succ] using hPair (show i' ≠ j' from fun h ↦ hij (congrArg Fin.succ h))

/-- A set containing at most `h` primes misses at least one of `h+1`
pairwise disjoint candidate blocks. -/
theorem exists_improvingPrimeBlock_disjoint_of_card_le {k h : ℕ}
    {E : Fin (h+1) → ImprovingPrimeBlock k}
    (hPair : Pairwise (fun i j ↦ Disjoint (E i).primes (E j).primes))
    {S : Finset ℕ} (hS : S.card ≤ h) : ∃ i, Disjoint (E i).primes S := by
  by_contra! hAll
  have hchoose (i : Fin (h+1)) : ∃ p : ↥S, p.val ∈ (E i).primes := by
    obtain ⟨p,hp,hpS⟩ := Finset.not_disjoint_iff.mp (hAll i)
    exact ⟨⟨p,hpS⟩,hp⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hij
    have hp : (f i).val ∈ (E j).primes := by rw [he]; exact hf j
    exact (disjoint_left.mp (hPair hij)) (hf i) hp
  have hi := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fin,Fintype.card_coe] at hi
  omega

end GRHArticle.ProgressionFree
