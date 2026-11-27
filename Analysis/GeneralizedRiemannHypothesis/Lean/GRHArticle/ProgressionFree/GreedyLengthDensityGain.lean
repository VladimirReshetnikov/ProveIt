import GRHArticle.ProgressionFree.GreedyLengthExponents
import GRHArticle.ProgressionFree.SharedDeletionMass

/-!
# A denser progression-free set for every length

Reciprocal-prime divergence supplies enough satellites outside any finite
exception set. The quantitative finite mass gain persists in the natural
density of the full integer set.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- A finite set of primes with arbitrarily large reciprocal mass can avoid
any fixed finite set of integers. -/
theorem exists_prime_reciprocalSum_gt_disjoint (F : Finset ℕ) (M : ℝ) :
    ∃ S : Finset ℕ, Disjoint S F ∧ (∀ p ∈ S, p.Prime) ∧
      M < ∑ p ∈ S, 1/(p : ℝ) := by
  obtain ⟨P,_,hP,hM⟩ := exists_odd_primes_reciprocalSum_gt (M + ∑ p ∈ F, 1/(p : ℝ))
  let q (p : ℕ) : ℝ := 1/(p : ℝ)
  have hpart := sum_sdiff (f := q) (s₂ := P) (s₁ := P ∩ F) inter_subset_left
  have he : P \ (P ∩ F) = P \ F := by
    ext p
    simp only [mem_sdiff, mem_inter]
    tauto
  rw [he] at hpart
  have hrem : (∑ p ∈ P ∩ F, q p) ≤ ∑ p ∈ F, q p :=
    sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ ↦ by dsimp [q]; positivity)
  refine ⟨P \ F, disjoint_left.mpr (fun _ hp hF ↦ (mem_sdiff.mp hp).2 hF), fun p hp ↦ hP p (mem_sdiff.mp hp).1, ?_⟩
  change M < ∑ p ∈ P \ F, q p
  change M + (∑ p ∈ F, q p) < ∑ p ∈ P, q p at hM
  linarith

private theorem primeBlockRuleSet_base_eq {G : Set ℕ} {marker : ℕ} {B : Finset ℕ}
    (hm : marker.Prime) (hB : ∀ p ∈ B, p.Prime) :
    primeBlockRuleSet G marker B (sharedDeletionBasePatterns G) = integerIndependentExponentSet G := by
  ext n
  constructor
  · rintro ⟨hn,hCap,hOut⟩
    refine ⟨hn,fun p hp ↦ ?_⟩
    by_cases hpm : p = marker
    · subst p
      exact hCap.1
    by_cases hpB : p ∈ B
    · exact hCap.2 ⟨p,hpB⟩
    · exact hOut p hp hpm hpB
  · rintro ⟨hn,h⟩
    exact ⟨hn, ⟨h marker hm, fun p ↦ h p.val (hB _ p.property)⟩, fun p hp _ _ ↦ h p hp⟩

private theorem primeBlockRuleSet_edit_eq (k : ℕ) (G : Set ℕ) (marker : ℕ) (B : Finset ℕ) :
    primeBlockRuleSet G marker B (sharedDeletionEditedPatterns (k-2) G) =
      integerSharedDeletionSet k G marker B := by
  ext n
  have he :
      (fun j : Option ↥B ↦ j.elim (n.factorization marker) (fun p ↦ n.factorization p.val)) =
      (fun j ↦ n.factorization (sharedDeletionPrime marker B j)) := by
    funext j
    cases j <;> rfl
  simp only [primeBlockRuleSet, integerSharedDeletionSet, sharedDeletionEditedPatterns,
    Set.mem_setOf_eq, he]

private theorem sum_satellite_inv_sq_le_one (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    (∑ p : ↥B, (1/(p.val : ℝ))^2) ≤ 1 := by
  rw [univ_eq_attach, sum_attach B (fun p : ℕ ↦ (1/(p : ℝ))^2)]
  have hs : B ⊆ Ioc 1 (B.sup id) :=
    fun p hp ↦ mem_Ioc.mpr ⟨(hB p hp).one_lt, le_sup (f := id) hp⟩
  simp_rw [one_div_pow]
  exact (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ by positivity)).trans
    (by simpa only [Nat.cast_one, div_one] using sum_Ioc_one_div_sq_le 1 (B.sup id) (by decide))

/-- The article's `gpi:thm:klength`. For every length at least three, an
actual positive-integer set avoiding rational-ratio progressions improves
the greedy natural density, by changing only a single finite prime block
outside the prescribed exceptional primes. -/
theorem exists_integerGreedyLengthExchange_strictNaturalDensityGain {k : ℕ} (hk : 3 ≤ k)
    (F : Finset ℕ) :
    ∃ (marker : ℕ) (B : Finset ℕ) (dG dE : ℝ),
      marker.Prime ∧ marker ∉ B ∧ Disjoint (insert marker B) F ∧
      (∀ p ∈ B, p.Prime) ∧
      KTermGPFree k (integerGreedyLengthExchange k marker B) ∧
      HasNaturalDensity (integerGreedyLengthSet k) dG ∧
      HasNaturalDensity (integerGreedyLengthExchange k marker B) dE ∧ dG < dE := by
  obtain ⟨marker,hmF,hm⟩ := Nat.exists_infinite_primes (F.sup id+1)
  have hmF' : marker ∉ F := fun h ↦ (not_le_of_gt (Nat.lt_of_succ_le hmF)) (le_sup (f := id) h)
  let w : ℝ := 1/(marker : ℝ)
  let b := k-2
  have hw0 : 0 < w := by dsimp [w]; exact one_div_pos.mpr (by exact_mod_cast hm.pos)
  have hw1 : w ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm.two_le)
  have hpw : 0 < w^(b+1) := pow_pos hw0 _
  obtain ⟨B,hdis,hB,hBlarge⟩ := exists_prime_reciprocalSum_gt_disjoint (insert marker F) (7/w^(b+1))
  have hnot : marker ∉ B := fun h ↦ (disjoint_left.mp hdis) h (mem_insert_self _ _)
  have hFin : Disjoint (insert marker B) F := by
    refine disjoint_left.mpr fun q hq hqF ↦ ?_
    rcases mem_insert.mp hq with rfl | hq
    · exact hmF' hqF
    · exact (disjoint_left.mp hdis) hq (mem_insert_of_mem hqF)
  let G := greedyLengthExponents k
  have hG0 : 0 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hG1 : 1 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hb : b ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by dsimp [b]; omega)
  have hnext : b+1 ∉ G := by
    change k-2+1 ∉ greedyLengthExponents k
    rw [show k-2+1 = k-1 by omega]
    exact not_mem_greedyLengthExponents_pred (by omega)
  let C := sharedDeletionBasePatterns (ι := ↥B) G
  let E := sharedDeletionEditedPatterns (ι := ↥B) b G
  let u (q : ↥B) : ℝ := 1/(q.val : ℝ)
  let δ := ∏ q, u q^b
  have hu0 (q : ↥B) : 0 < u q := one_div_pos.mpr (by exact_mod_cast (hB _ q.property).pos)
  have hu1 (q : ↥B) : u q ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (hB _ q.property).two_le)
  have hδ : 0 < δ := prod_pos fun q _ ↦ pow_pos (hu0 q) _
  have hLarge : 7 ≤ w^(b+1) * ∑ q, u q := by
    dsimp only [u]
    rw [univ_eq_attach, sum_attach B (fun p : ℕ ↦ 1/(p : ℝ))]
    exact (by simpa only [mul_comm] using (div_lt_iff₀ hpw).mp hBlarge :
      7 < w^(b+1) * ∑ p ∈ B, 1/(p : ℝ)).le
  obtain ⟨dG,hDg⟩ := exists_hasNaturalDensity_primeBlockRuleSet hG0 hG1 C hm hB hnot
  obtain ⟨dE,hDe⟩ := exists_hasNaturalDensity_primeBlockRuleSet hG0 hG1 E hm hB hnot
  have hGain : dG < dE := naturalDensity_primeBlockRuleSet_lt_of_mass_gain hG0 hG1 hm hB hnot
    hDg hDe hδ (b+2) (fun K hK ↦ sharedDeletionPatternMass_gain hb hnext (by omega)
      hw0.le hw1 (fun q ↦ (hu0 q).le) hu1 (sum_satellite_inv_sq_le_one B hB) hLarge)
  rw [primeBlockRuleSet_base_eq hm hB] at hDg
  rw [primeBlockRuleSet_edit_eq k G marker B] at hDe
  exact ⟨marker,B,dG,dE,hm,hnot,hFin,hB,kTermGPFree_integerGreedyLengthExchange hk marker B,hDg,hDe,hGain⟩

end GRHArticle.ProgressionFree
