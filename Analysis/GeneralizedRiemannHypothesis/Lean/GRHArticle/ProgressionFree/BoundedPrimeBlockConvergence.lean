import GRHArticle.ProgressionFree.BoundedPrimeBlockStrictGap
import GRHArticle.ProgressionFree.GreedyLengthSmoothBound
import GRHArticle.ProgressionFree.PrimeBlockPrefixTemplates
import GRHArticle.ProgressionFree.PrimePowerTailBounds
import GRHArticle.ProgressionFree.WidthPreservingFiniteExceptions
import Mathlib.Data.Nat.Prime.Nth

/-!
# Effective loss bound and convergence for bounded prime blocks

Keep the entire initial segment of primes in one block. Imposing the
greedy exterior discards only large prime powers of exponent at least
`k-1`. The uniform power-tail bound gives the article's explicit error.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- A prefix block followed by the greedy exterior retains almost all of
the density associated to any admissible smooth template. -/
private theorem exists_boundedPrimeBlockRule_near_smoothTemplate_of_tailBound {k Y d : ℕ}
    (hk : 3 ≤ k) (hY : 2 ≤ Y) (hd : 0 < d) (hwidth : (Nat.primesLE Y).card ≤ d)
    {τ : ℝ} (hτ : ∀ N, densityUpTo {n | ∃ p, Y < p ∧ p.Prime ∧ p^(k-1) ∣ n} N ≤ τ)
    {F : Set ℕ} (hF : F ⊆ Nat.smoothNumbers (Y+1)) (hFree : KTermGPFree k F) :
    ∃ (A : Set ℕ) (e : ℝ), IntegerBoundedPrimeBlockSet d A ∧ KTermGPFree k A ∧
      HasNaturalDensity A e ∧
      integerSmoothDensityFactor Y * (∑' s : F, (s.val : ℝ)⁻¹) -
        τ ≤ e := by
  let P := Nat.primesLE Y
  let S : Finset (Finset ℕ) := {P}
  let base (Q : Finset ℕ) : Set (↥Q → ℕ) := Set.univ
  let C := integerPrimeBlockPatterns P F
  let R := Function.update base P C
  let G := greedyLengthExponents k
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primesLE hp
  have hP₀ : P.Nonempty := ⟨2,Nat.mem_primesLE.mpr ⟨hY,Nat.prime_two⟩⟩
  have hNon (Q : Finset ℕ) (hQ : Q ∈ S) : Q.Nonempty :=
    (mem_singleton.mp hQ).symm ▸ hP₀
  have hPr (Q : Finset ℕ) (hQ : Q ∈ S) : ∀ p ∈ Q, p.Prime :=
    (mem_singleton.mp hQ).symm ▸ hP
  have hWidth (Q : Finset ℕ) (hQ : Q ∈ S) : Q.card ≤ d :=
    (mem_singleton.mp hQ).symm ▸ hwidth
  have hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro Q hQ Q' hQ' hneq
    exact (hneq ((mem_singleton.mp hQ).trans (mem_singleton.mp hQ').symm)).elim
  have hRule : R P = C := Function.update_self _ _ _
  have hRF (Q : Finset ℕ) (hQ : Q ∈ S) : KTermVectorAPFree k (R Q) := by
    rw [mem_singleton.mp hQ,hRule]
    exact kTermVectorAPFree_integerPrimeBlockPatterns (by omega) hP hFree
  have hG₀ : 0 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hG₁ : 1 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  obtain ⟨e,he⟩ := exists_hasNaturalDensity_finiteExceptionPrimeRule S R hG₀ hG₁ hPr hPair
  refine ⟨finiteExceptionPrimeRule S R G,e,
    integerBoundedPrimeBlockSet_finiteExceptionPrimeRule hd S R G hNon hPr hPair hWidth,
    kTermGPFree_finiteExceptionPrimeRule (by omega) S R hRF (kTermAPFree_greedyLengthExponents (by omega)),he,?_⟩
  let M := integerSmoothDensityFactor Y * (∑' s : F, (s.val : ℝ)⁻¹)
  have hM : HasNaturalDensity (finitePrimeBlockRule S R) M := by
    change HasNaturalDensity (finitePrimeBlockRule {Nat.primesLE Y} R) M
    rw [finitePrimeBlockRule_primesLE_eq_roughTemplate Y hF R hRule]
    exact hasNaturalDensity_integerRoughTemplateProducts (fun _ h ↦ h) hF
      (hasNaturalDensity_integerRoughNumbers Y)
  have hUnion : S.biUnion id = P := by
    ext p
    simp only [S,mem_biUnion,mem_singleton,id_eq,exists_eq_left]
  have hErr (N : ℕ) :
      |densityUpTo (finitePrimeBlockRule S R) N - densityUpTo (finiteExceptionPrimeRule S R G) N| ≤
        τ := by
    refine (densityUpTo_abs_sub_le_of_symmDiff_subset
      (E := {n | ∃ p, Y < p ∧ p.Prime ∧ p^(k-1) ∣ n}) N ?_).trans (hτ N)
    intro n hn
    rcases hn with ⟨h,h'⟩ | ⟨h,h'⟩
    · by_contra hN
      apply h'
      refine ⟨h,fun p hp hOut ↦ ?_⟩
      have hpY : Y < p := lt_of_not_ge fun hp' ↦ hOut (hUnion.symm ▸ Nat.mem_primesLE.mpr ⟨hp',hp⟩)
      have hlt : n.factorization p < k-1 := by
        by_contra! he
        exact hN ⟨p,hpY,hp,(hp.pow_dvd_iff_le_factorization h.1).mpr (by omega)⟩
      exact mem_greedyLengthExponents_of_lt (by omega) hlt
    · exact (h' h.1).elim
  have h := le_of_tendsto' (hM.sub he).abs hErr
  exact sub_le_iff_le_add'.mpr (by linarith only [(abs_le.mp h).2])

/-- Quantitative approximation to any admissible smooth template by an
actual bounded-width set with a true natural density. -/
theorem exists_boundedPrimeBlockRule_near_smoothTemplate {k Y d : ℕ}
    (hk : 3 ≤ k) (hY : 2 ≤ Y) (hd : 0 < d) (hwidth : (Nat.primesLE Y).card ≤ d)
    {F : Set ℕ} (hF : F ⊆ Nat.smoothNumbers (Y+1)) (hFree : KTermGPFree k F) :
    ∃ (A : Set ℕ) (e : ℝ), IntegerBoundedPrimeBlockSet d A ∧ KTermGPFree k A ∧
      HasNaturalDensity A e ∧
      integerSmoothDensityFactor Y * (∑' s : F, (s.val : ℝ)⁻¹) -
        1 / (((k-2 : ℕ) : ℝ)*(Y : ℝ)^(k-2)) ≤ e := by
  apply exists_boundedPrimeBlockRule_near_smoothTemplate_of_tailBound hk hY hd hwidth _ hF hFree
  intro N
  simpa only [show (k-2)+1 = k-1 by omega] using
    densityUpTo_largePrimePower_le Y N (k-2) (by omega) (by omega)

/-- The whole template supremum fits below the bounded-block supremum,
up to the same effective prime-power tail. -/
private theorem integerLengthSmoothOptimization_sub_tail_le_boundedPrimeBlocks_of_tailBound {k Y d : ℕ}
    (hk : 3 ≤ k) (hY : 2 ≤ Y) (hd : 0 < d) (hwidth : (Nat.primesLE Y).card ≤ d)
    {τ : ℝ} (hτ : ∀ N, densityUpTo {n | ∃ p, Y < p ∧ p.Prime ∧ p^(k-1) ∣ n} N ≤ τ) :
    integerLengthSmoothOptimization k Y - τ ≤
      integerBoundedPrimeBlockDensitySupremum k d := by
  unfold integerLengthSmoothOptimization
  rw [sub_le_iff_le_add,mul_comm,← le_div_iff₀ (integerSmoothDensityFactor_pos Y)]
  apply csSup_le (integerLengthSmoothTemplateWeights_nonempty (by omega : 0 < k) Y)
  rintro w ⟨F,hF,hFree,rfl⟩
  obtain ⟨A,e,hA,hAF,hD,hL⟩ := exists_boundedPrimeBlockRule_near_smoothTemplate_of_tailBound hk hY hd hwidth hτ hF hFree
  have hE : e ≤ integerBoundedPrimeBlockDensitySupremum k d := by
    unfold integerBoundedPrimeBlockDensitySupremum
    exact le_csSup ⟨1,by rintro a ⟨B,_,_,rfl⟩; exact integerUpperDensity_le_one B⟩
      ⟨A,hA,hAF,(integerUpperDensity_eq_of_hasNaturalDensity hD).symm⟩
  apply (le_div_iff₀ (integerSmoothDensityFactor_pos Y)).mpr
  rw [mul_comm]
  exact sub_le_iff_le_add.mp (hL.trans hE)

theorem integerLengthSmoothOptimization_sub_tail_le_boundedPrimeBlocks {k Y d : ℕ}
    (hk : 3 ≤ k) (hY : 2 ≤ Y) (hd : 0 < d) (hwidth : (Nat.primesLE Y).card ≤ d) :
    integerLengthSmoothOptimization k Y - 1 / (((k-2 : ℕ) : ℝ)*(Y : ℝ)^(k-2)) ≤
      integerBoundedPrimeBlockDensitySupremum k d := by
  apply integerLengthSmoothOptimization_sub_tail_le_boundedPrimeBlocks_of_tailBound hk hY hd hwidth
  intro N
  simpa only [show (k-2)+1 = k-1 by omega] using
    densityUpTo_largePrimePower_le Y N (k-2) (by omega) (by omega)

/-- Quantitative loss bound for any initial prime segment small enough
to lie in a single block. -/
theorem integerLengthDensity_sub_boundedPrimeBlocks_le_tail {k Y d : ℕ}
    (hk : 3 ≤ k) (hY : 2 ≤ Y) (hd : 0 < d) (hwidth : (Nat.primesLE Y).card ≤ d) :
    integerLengthNaturalDensitySupremum k - integerBoundedPrimeBlockDensitySupremum k d ≤
      1 / (((k-2 : ℕ) : ℝ)*(Y : ℝ)^(k-2)) := by
  have h₁ := integerLengthNaturalDensitySupremum_le_smoothOptimization (by omega : 0 < k) Y
  have h₂ := integerLengthSmoothOptimization_sub_tail_le_boundedPrimeBlocks hk hY hd hwidth
  linarith only [h₁,h₂]

private theorem prefix_before_next_prime {d : ℕ} (hd : 0 < d) :
    2 ≤ Nat.nth Nat.Prime d - 1 ∧ (Nat.primesLE (Nat.nth Nat.Prime d - 1)).card = d := by
  let p := Nat.nth Nat.Prime d
  have hp : 2 < p := by
    simpa only [Nat.nth_prime_zero_eq_two] using (Nat.nth_strictMono Nat.infinite_setOf_prime) hd
  refine ⟨by omega,?_⟩
  have he : p-1+1 = p := by omega
  change ((p-1+1).primesBelow).card = d
  rw [he,Nat.primesBelow,← Nat.count_eq_card_filter_range]
  exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime d

/-- The exact loss bound in `gpi:thm:blocksk`. The zero-based index
`Nat.nth Nat.Prime d` is the article's `p_(d+1)`. -/
theorem integerLengthDensity_sub_boundedPrimeBlocks_le_next_prime {k d : ℕ}
    (hk : 3 ≤ k) (hd : 0 < d) :
    integerLengthNaturalDensitySupremum k - integerBoundedPrimeBlockDensitySupremum k d ≤
      1 / (((k-2 : ℕ) : ℝ)*((Nat.nth Nat.Prime d-1 : ℕ) : ℝ)^(k-2)) := by
  obtain ⟨hY,hP⟩ := prefix_before_next_prime hd
  exact integerLengthDensity_sub_boundedPrimeBlocks_le_tail hk hY hd hP.le

/-- For triples, the odd-prime square tail gives the sharper reciprocal
next-prime bound of `gpi:thm:blocks`. -/
theorem integerLengthDensity_three_sub_boundedPrimeBlocks_le_next_prime {d : ℕ} (hd : 0 < d) :
    integerLengthNaturalDensitySupremum 3 - integerBoundedPrimeBlockDensitySupremum 3 d ≤
      1 / (Nat.nth Nat.Prime d : ℝ) := by
  let p := Nat.nth Nat.Prime d
  let Y := p-1
  obtain ⟨hY,hprWidth⟩ := prefix_before_next_prime hd
  change 2 ≤ Y at hY
  change (Nat.primesLE Y).card = d at hprWidth
  have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime d
  have hp' : 2 < p := by dsimp [Y] at hY; omega
  obtain ⟨j,hj⟩ := hp.odd_of_ne_two hp'.ne'
  have hEq : p = 2*j+1 := by simpa only [two_mul] using hj
  have heY : Y = 2*j := by dsimp [Y]; omega
  have hTail (N : ℕ) :
      densityUpTo {n | ∃ q, Y < q ∧ q.Prime ∧ q^(3-1) ∣ n} N ≤ 1/(p : ℝ) := by
    rw [heY]
    have hj₀ : 0 < j := by omega
    refine (densityUpTo_largePrimeSquare_even_cutoff_le j N hj₀).trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have hj₁ : (1 : ℝ) ≤ j := by exact_mod_cast hj₀
    rw [hEq]
    push_cast
    linarith
  have h₁ := integerLengthNaturalDensitySupremum_le_smoothOptimization (by decide : 0 < (3 : ℕ)) Y
  have h₂ := integerLengthSmoothOptimization_sub_tail_le_boundedPrimeBlocks_of_tailBound
    (by decide : 3 ≤ (3 : ℕ)) hY hd hprWidth.le hTail
  linarith only [h₁,h₂]

/-- Increasing the maximum block width recovers the unrestricted
natural-density supremum. -/
theorem tendsto_integerBoundedPrimeBlockDensitySupremum {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (integerBoundedPrimeBlockDensitySupremum k) atTop (𝓝 (integerLengthNaturalDensitySupremum k)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨Y,hY⟩ := exists_nat_one_div_lt hε
  let Z := Y+2
  have hZ : 2 ≤ Z := by dsimp [Z]; omega
  have hZ₀ : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hZ' : 1/(Z : ℝ) < ε := (one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < (Y:ℝ)+1) (by dsimp [Z]; push_cast; linarith)).trans_lt hY
  have hTail : 1 / (((k-2 : ℕ) : ℝ)*(Z : ℝ)^(k-2)) ≤ 1/(Z : ℝ) := by
    apply one_div_le_one_div_of_le hZ₀
    have hm : (1 : ℝ) ≤ ((k-2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k-2 by omega)
    have hz : (Z : ℝ) ≤ (Z : ℝ)^(k-2) :=
      le_self_pow₀ (by exact_mod_cast (show 1 ≤ Z by omega)) (by omega)
    exact hz.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hm (pow_nonneg hZ₀.le _))
  refine ⟨max 1 (Nat.primesLE Z).card, fun d hd ↦ ?_⟩
  have hd₀ : 0 < d := (le_max_left _ _).trans hd
  have hP : (Nat.primesLE Z).card ≤ d := (le_max_right _ _).trans hd
  have hlt := integerBoundedPrimeBlockDensitySupremum_lt_lengthNaturalDensitySupremum hk hd₀
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hlt.le),neg_sub]
  exact ((integerLengthDensity_sub_boundedPrimeBlocks_le_tail hk hZ hd₀ hP).trans hTail).trans_lt hZ'

end GRHArticle.ProgressionFree
