import GRHArticle.ProgressionFree.IndependentPrimeRuleDensity
import GRHArticle.ProgressionFree.IntegerPrimeBlockFreeness
import GRHArticle.ProgressionFree.LightPrimeBlocks
import GRHArticle.ProgressionFree.GreedyLengthDensityGain

/-!
# The bounded-block extremum at width one

The local mass comparison applies to every individual prime of a
nonempty width-one rule. Taking larger finite collections of primes
then bounds its upper density by the greedy natural density.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

private def scalarPatterns (R : Set ℕ) : Set (Unit → ℕ) :=
  {v | v () ∈ R}

private theorem scalarPatternMass (w : ℝ) (R : Set ℕ) :
    reciprocalExponentMass (fun _ : Unit ↦ w) (scalarPatterns R) = exponentRuleMass w R := by
  let e : R ≃ scalarPatterns R :=
    { toFun := fun n ↦ ⟨fun _ ↦ n.val,n.property⟩
      invFun := fun v ↦ ⟨v.val (),v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := by intro v; apply Subtype.ext; funext i; cases i; rfl }
  rw [reciprocalExponentMass_eq_tsum_subtype, ← e.tsum_eq]
  unfold exponentRuleMass
  apply tsum_congr
  intro n
  simp [e,reciprocalExponentWeight]

/-- Any one-dimensional greedy rule maximizes the geometric-weight
sum at weights at most one half. -/
theorem exponentRuleMass_le_greedy {k : ℕ} (hk : 2 ≤ k) {R : Set ℕ}
    (hR : KTermAPFree k R) {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1/2) :
    exponentRuleMass w R ≤ exponentRuleMass w (greedyLengthExponents k) := by
  have hA : KTermVectorAPFree k (scalarPatterns R) := by
    intro x a d hx ha i
    cases i
    exact hR (fun j ↦ x j ()) (a ()) (d ()) (fun j ↦ hx j) (fun j ↦ ha j ())
  have hB : greedyExponentPatterns Unit k = scalarPatterns (greedyLengthExponents k) := by
    ext x
    exact ⟨fun h ↦ h (), fun h i ↦ by cases i; exact h⟩
  have hL : (∏ _ : Unit, (1-w)⁻¹) ≤ 2 := by
    simp only [Fintype.prod_unique]
    rw [← one_div, div_le_iff₀ (show 0 < 1-w by linarith)]
    linarith
  have h := reciprocalExponentMass_le_greedy_of_light hk
    (fun _ : Unit ↦ hw) (fun _ : Unit ↦ show w < 1 by linarith) hL hA
  simpa only [hB,scalarPatternMass] using h

private theorem greedy_subset_finite (k Y : ℕ) :
    integerGreedyLengthSet k ⊆ integerFiniteIndependentPrimeRules (Nat.primesLE Y)
      (fun _ ↦ greedyLengthExponents k) := by
  rintro n ⟨hn,hG⟩
  exact ⟨hn,fun p ↦ hG p.val (Nat.prime_of_mem_primesLE p.property)⟩

/-- Imposing the greedy exponent rule at finitely many primes approximates
the full greedy set uniformly on positive prefixes. -/
theorem densityUpTo_greedyLength_truncation_error {k : ℕ} (hk : 3 ≤ k) (Y N : ℕ) (hY : 0 < Y) :
    |densityUpTo (integerFiniteIndependentPrimeRules (Nat.primesLE Y) (fun _ ↦ greedyLengthExponents k)) N -
      densityUpTo (integerGreedyLengthSet k) N| ≤ 1/(Y : ℝ) := by
  have h0 : 0 ∈ greedyLengthExponents k := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have h1 : 1 ∈ greedyLengthExponents k := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset
    (E := {n | ∃ p, Y < p ∧ p.Prime ∧ p^2 ∣ n}) N ?_).trans
    (densityUpTo_largePrimeSquare_le Y N hY)
  intro n hn
  rcases hn with ⟨hF,hG⟩ | ⟨hG,hF⟩
  · by_contra h
    apply hG
    refine ⟨hF.1, fun p hp ↦ ?_⟩
    by_cases hpY : p ≤ Y
    · exact hF.2 ⟨p,Nat.mem_primesLE.mpr ⟨hpY,hp⟩⟩
    · have hsmall : n.factorization p < 2 := by
        by_contra! hn
        exact h ⟨p,lt_of_not_ge hpY,hp,(hp.pow_dvd_iff_le_factorization hF.1).mpr hn⟩
      rcases (show n.factorization p = 0 ∨ n.factorization p = 1 by omega) with he | he
      · exact he.symm ▸ h0
      · exact he.symm ▸ h1
  · exact (hF (greedy_subset_finite k Y hG)).elim

/-- The independent greedy product has a true natural density at every
length at least three. -/
theorem exists_hasNaturalDensity_integerGreedyLengthSet {k : ℕ} (hk : 3 ≤ k) :
    ∃ d, HasNaturalDensity (integerGreedyLengthSet k) d := by
  apply exists_hasNaturalDensity_of_uniform_approximation
  intro ε hε
  obtain ⟨Y,hY⟩ := exists_nat_one_div_lt hε
  let P := Nat.primesLE (Y+1)
  have h := hasNaturalDensity_integerFiniteIndependentPrimeRules P (fun _ ↦ greedyLengthExponents k)
    (fun _ hp ↦ Nat.prime_of_mem_primesLE hp)
  refine ⟨_,_,h,fun N ↦ ?_⟩
  rw [abs_sub_comm]
  exact (densityUpTo_greedyLength_truncation_error hk (Y+1) N (Nat.succ_pos _)).trans
    (by exact_mod_cast hY.le)

private theorem integerUpperDensity_le_of_subset_density {A B : Set ℕ} (hAB : A ⊆ B)
    {d : ℝ} (hB : HasNaturalDensity B d) : integerUpperDensity A ≤ d := by
  unfold integerUpperDensity
  rw [← hB.limsup_eq]
  exact limsup_le_limsup (Eventually.of_forall (densityUpTo_mono hAB))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (densityUpTo_nonneg A))).isCoboundedUnder_le
    hB.isBoundedUnder_le

/-- A progression-free independent prime rule has upper density at most
the true natural density of the greedy set. -/
theorem integerUpperDensity_singletonPrimeRule_le_greedy {k : ℕ} (hk : 3 ≤ k)
    {R : ℕ → Set ℕ} (hA : KTermGPFree k (integerIndependentPrimeRules R))
    {d : ℝ} (hd : HasNaturalDensity (integerGreedyLengthSet k) d) :
    integerUpperDensity (integerIndependentPrimeRules R) ≤ d := by
  by_cases hn : (integerIndependentPrimeRules R).Nonempty
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨Y,hY⟩ := exists_nat_one_div_lt hε
    let P := Nat.primesLE (Y+1)
    have hP : ∀ p ∈ P, p.Prime := fun p hp ↦ Nat.prime_of_mem_primesLE hp
    have hFin (p : ↥P) : KTermAPFree k (R p.val) :=
      kTermAPFree_of_integerIndependentPrimeRules (by omega) hn hA (hP _ p.property)
    let t (S : ℕ → Set ℕ) := ∏ p : ↥P, (1-1/(p.val : ℝ))*exponentRuleMass (1/(p.val : ℝ)) (S p.val)
    let G (_ : ℕ) := greedyLengthExponents k
    have hR : HasNaturalDensity (integerFiniteIndependentPrimeRules P R) (t R) :=
      hasNaturalDensity_integerFiniteIndependentPrimeRules P R hP
    have hG : HasNaturalDensity (integerFiniteIndependentPrimeRules P G) (t G) :=
      hasNaturalDensity_integerFiniteIndependentPrimeRules P G hP
    have hsub : integerIndependentPrimeRules R ⊆ integerFiniteIndependentPrimeRules P R := by
      rintro n ⟨hn,h⟩
      exact ⟨hn,fun p ↦ h p.val (hP _ p.property)⟩
    have hupper := integerUpperDensity_le_of_subset_density hsub hR
    have he (p : ↥P) : 0 ≤ 1-1/(p.val : ℝ) := by
      apply sub_nonneg.mpr
      exact (div_le_one (by exact_mod_cast (hP _ p.property).pos)).mpr
        (by exact_mod_cast (hP _ p.property).one_lt.le)
    have hcomp : t R ≤ t G := by
      apply Finset.prod_le_prod
      · intro p _
        exact mul_nonneg (he p) (tsum_nonneg fun _ ↦ by positivity)
      · intro p _
        apply mul_le_mul_of_nonneg_left _ (he p)
        exact exponentRuleMass_le_greedy (by omega) (hFin p) (by positivity)
          (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (hP _ p.property).two_le))
    have hDist : |t G-d| ≤ 1/((Y+1 : ℕ) : ℝ) := by
      apply le_of_tendsto' ((hG.sub hd).abs)
      exact fun N ↦ densityUpTo_greedyLength_truncation_error hk (Y+1) N (Nat.succ_pos _)
    have hL := (abs_le.mp hDist).2
    have hY' : 1/((Y+1 : ℕ) : ℝ) < ε := by exact_mod_cast hY
    exact hupper.trans (hcomp.trans (by linarith only [hL,hY']))
  · rw [Set.not_nonempty_iff_eq_empty.mp hn, integerUpperDensity_eq_of_hasNaturalDensity hasNaturalDensity_empty]
    exact ge_of_tendsto' hd (densityUpTo_nonneg _)

/-- The width-one bounded-block supremum is the greedy natural density.
This is the first equality in the article's `gpi:thm:blocksk`. -/
theorem integerBoundedPrimeBlockDensitySupremum_one_eq_greedy {k : ℕ} (hk : 3 ≤ k)
    {d : ℝ} (hd : HasNaturalDensity (integerGreedyLengthSet k) d) :
    integerBoundedPrimeBlockDensitySupremum k 1 = d := by
  let S := {a | ∃ A, IntegerBoundedPrimeBlockSet 1 A ∧ KTermGPFree k A ∧ a = integerUpperDensity A}
  have hmem : d ∈ S := ⟨integerGreedyLengthSet k, integerBoundedPrimeBlockSet_greedyLength k,
    kTermGPFree_integerGreedyLengthSet (by omega), (integerUpperDensity_eq_of_hasNaturalDensity hd).symm⟩
  have hS : BddAbove S := ⟨1, by
    rintro a ⟨A,_,_,rfl⟩
    exact integerUpperDensity_le_one A⟩
  change sSup S = d
  apply le_antisymm (csSup_le ⟨d,hmem⟩ ?_) (le_csSup hS hmem)
  rintro a ⟨A,hBlock,hF,rfl⟩
  obtain ⟨R,rfl⟩ := integerBoundedPrimeBlockSet_one_iff.mp hBlock
  exact integerUpperDensity_singletonPrimeRule_le_greedy hk hF hd

/-- The width-one supremum is strictly below the unrestricted
natural-density supremum at every length at least three. -/
theorem integerBoundedPrimeBlockDensitySupremum_one_lt_lengthNaturalDensitySupremum
    {k : ℕ} (hk : 3 ≤ k) :
    integerBoundedPrimeBlockDensitySupremum k 1 < integerLengthNaturalDensitySupremum k := by
  obtain ⟨marker,B,dG,dE,_,_,_,_,hfree,hG,hE,hlt⟩ :=
    exists_integerGreedyLengthExchange_strictNaturalDensityGain hk ∅
  rw [integerBoundedPrimeBlockDensitySupremum_one_eq_greedy hk hG]
  refine hlt.trans_le (le_csSup ?_ ?_)
  · exact ⟨1, by rintro a ⟨A,_,_,ha⟩; exact naturalDensity_le_one ha⟩
  · refine ⟨integerGreedyLengthExchange k marker B, ?_, hfree, hE⟩
    intro h
    exact h.1 rfl

end GRHArticle.ProgressionFree
