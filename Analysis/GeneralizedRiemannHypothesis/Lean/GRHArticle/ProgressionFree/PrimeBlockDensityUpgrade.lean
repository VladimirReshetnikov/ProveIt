import GRHArticle.ProgressionFree.PrimeBlockReduction

/-!
# Replacing one greedy block amidst arbitrary fixed exceptions

The density law for finite exceptions cancels the exterior and all
unchanged local factors. It quantifies the gain from adding a disjoint
improving block to any reduced rule.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

theorem primeBlockProbability_greedy_pos {k : ℕ} (hk : 2 ≤ k) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) :
    0 < primeBlockProbability P (greedyExponentPatterns ↥P k) := by
  let u (p : ↥P) : ℝ := 1/(p.val : ℝ)
  let G := greedyExponentPatterns ↥P k
  have hu₀ (p : ↥P) : 0 ≤ u p := by dsimp [u]; positivity
  have hu₁ (p : ↥P) : u p < 1 :=
    (div_lt_one (by exact_mod_cast (hP _ p.property).pos)).mpr
      (by exact_mod_cast (hP _ p.property).one_lt)
  have h0 : (0 : ↥P → ℕ) ∈ G := by
    intro p
    change 0 ∈ greedyLengthExponents k
    exact mem_greedyLengthExponents_of_lt hk (by omega)
  have hs : Summable (G.indicator (reciprocalExponentWeight u)) :=
    summable_subtype_iff_indicator.mp ((summable_reciprocalExponentWeight hu₀ hu₁).subtype _)
  have hmass : 1 ≤ reciprocalExponentMass u G := by
    have hm := hs.sum_le_tsum ({0} : Finset (↥P → ℕ))
      (fun v _ ↦ Set.indicator_nonneg (fun v _ ↦ reciprocalExponentWeight_nonneg hu₀ v) _)
    simpa [reciprocalExponentMass, Set.indicator_of_mem h0, reciprocalExponentWeight] using hm
  exact mul_pos (prod_pos fun p _ ↦ sub_pos.mpr (hu₁ p)) (lt_of_lt_of_le zero_lt_one hmass)

private theorem finiteExceptionPrimeRule_greedy_eq (k : ℕ) {S : Finset (Finset ℕ)}
    (pr : ∀ P ∈ S, ∀ p ∈ P, p.Prime) :
    finiteExceptionPrimeRule S (fun P ↦ greedyExponentPatterns ↥P k) (greedyLengthExponents k) =
      integerGreedyLengthSet k := by
  ext n
  constructor
  · rintro ⟨⟨hn,h⟩,hOut⟩
    refine ⟨hn,fun p hp ↦ ?_⟩
    by_cases hm : p ∈ S.biUnion id
    · obtain ⟨P,hP,hpP⟩ := mem_biUnion.mp hm
      exact h P hP ⟨p,hpP⟩
    · exact hOut p hp hm
  · rintro ⟨hn,h⟩
    exact ⟨⟨hn,fun P hP p ↦ h p.val (pr P hP p.val p.property)⟩, fun p hp _ ↦ h p hp⟩

/-- Express the density of a reduced rule relative to the full greedy
density and the local probabilities of the exceptional blocks. -/
theorem finiteExceptionPrimeRule_density_relative_greedy {k : ℕ} (hk : 3 ≤ k)
    {S : Finset (Finset ℕ)} (rules : (P : Finset ℕ) → Set (↥P → ℕ))
    (hpr : ∀ P ∈ S, ∀ p ∈ P, p.Prime)
    (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    {d dG : ℝ}
    (hd : HasNaturalDensity (finiteExceptionPrimeRule S rules (greedyLengthExponents k)) d)
    (hG : HasNaturalDensity (integerGreedyLengthSet k) dG) :
    d * (∏ P ∈ S, primeBlockProbability P (greedyExponentPatterns ↥P k)) =
      dG * (∏ P ∈ S, primeBlockProbability P (rules P)) := by
  have h₀ : 0 ∈ greedyLengthExponents k := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have h₁ : 1 ∈ greedyLengthExponents k := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  rw [← finiteExceptionPrimeRule_greedy_eq k hpr] at hG
  exact finiteExceptionPrimeRule_density_cross_mul S rules _ h₀ h₁ hpr hpair hd hG

private theorem pairwise_insert_block {P : Finset ℕ} {S : Finset (Finset ℕ)}
    (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    (hdis : Disjoint P (S.biUnion id)) :
    ((insert P S : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id := by
  intro Q hQ R hR hne
  rcases mem_insert.mp hQ with rfl | hQ'
  · rcases mem_insert.mp hR with rfl | hR'
    · exact (hne rfl).elim
    · exact disjoint_left.mpr fun p hpP hpR ↦
        (disjoint_left.mp hdis) hpP (mem_biUnion.mpr ⟨R,hR',hpR⟩)
  · rcases mem_insert.mp hR with rfl | hR'
    · exact disjoint_left.mpr fun p hpQ hpP ↦
        (disjoint_left.mp hdis) hpP (mem_biUnion.mpr ⟨Q,hQ',hpQ⟩)
    · exact hpair hQ' hR' hne

/-- Add a disjoint improving block to a reduced rule. The natural density
is multiplied by the ratio of its new and old local probabilities. -/
theorem exists_density_of_disjoint_primeBlock_upgrade {k : ℕ} (hk : 3 ≤ k)
    {S : Finset (Finset ℕ)} (rules : (P : Finset ℕ) → Set (↥P → ℕ))
    (hS : ∀ P ∈ S, ∀ p ∈ P, p.Prime)
    (hpair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    (hfree : ∀ P ∈ S, KTermVectorAPFree k (rules P))
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hP₀ : P.Nonempty)
    (hDis : Disjoint P (S.biUnion id)) (F : Set (↥P → ℕ)) (hF : KTermVectorAPFree k F)
    {d dG : ℝ} (hd : HasNaturalDensity (finiteExceptionPrimeRule S rules (greedyLengthExponents k)) d)
    (hG : HasNaturalDensity (integerGreedyLengthSet k) dG) :
    ∃ E : Set ℕ, ∃ e : ℝ, 0 ∉ E ∧ KTermGPFree k E ∧ HasNaturalDensity E e ∧
      e * primeBlockProbability P (greedyExponentPatterns ↥P k) = d * primeBlockProbability P F := by
  let T := insert P S
  let R := Function.update rules P F
  let G := greedyLengthExponents k
  have h₀ : 0 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have h₁ : 1 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hnot : P ∉ S := by
    intro h
    obtain ⟨p,hp⟩ := hP₀
    exact (disjoint_left.mp hDis) hp (mem_biUnion.mpr ⟨P,h,hp⟩)
  have hPr (Q : Finset ℕ) (hQ : Q ∈ T) : ∀ p ∈ Q, p.Prime := by
    rcases mem_insert.mp hQ with rfl | hQ
    · exact hP
    · exact hS Q hQ
  have hR (Q : Finset ℕ) (hQ : Q ∈ T) : KTermVectorAPFree k (R Q) := by
    rcases mem_insert.mp hQ with rfl | hQ
    · simpa only [R,Function.update_self] using hF
    · rw [show R Q = rules Q from Function.update_of_ne (show Q ≠ P from fun he ↦ hnot (he ▸ hQ)) F rules]
      exact hfree Q hQ
  obtain ⟨e,he⟩ := exists_hasNaturalDensity_finiteExceptionPrimeRule T R h₀ h₁ hPr
    (pairwise_insert_block hpair hDis)
  refine ⟨finiteExceptionPrimeRule T R G,e,fun h ↦ h.1.1 rfl,
    kTermGPFree_finiteExceptionPrimeRule (by omega) T R hR (kTermAPFree_greedyLengthExponents (by omega)),he,?_⟩
  have hOld := finiteExceptionPrimeRule_density_relative_greedy hk rules hS hpair hd hG
  have hNew := finiteExceptionPrimeRule_density_relative_greedy hk R hPr
    (pairwise_insert_block hpair hDis) he hG
  let A := ∏ Q ∈ S, primeBlockProbability Q (greedyExponentPatterns ↥Q k)
  let B := ∏ Q ∈ S, primeBlockProbability Q (rules Q)
  have hA : 0 < A := prod_pos fun Q hQ ↦ primeBlockProbability_greedy_pos (by omega) (hS Q hQ)
  have hB : (∏ Q ∈ S, primeBlockProbability Q (R Q)) = B := by
    refine prod_congr rfl fun Q hQ ↦ ?_
    rw [show R Q = rules Q from Function.update_of_ne (show Q ≠ P from fun he ↦ hnot (he ▸ hQ)) F rules]
  rw [prod_insert hnot, prod_insert hnot, hB, show R P = F from Function.update_self _ _ _] at hNew
  apply mul_right_cancel₀ hA.ne'
  calc
    _ = e * (primeBlockProbability P (greedyExponentPatterns ↥P k)*A) := by ring
    _ = dG * (primeBlockProbability P F*B) := hNew
    _ = (dG*B)*primeBlockProbability P F := by ring
    _ = _ := by rw [← hOld]; ring

end GRHArticle.ProgressionFree
