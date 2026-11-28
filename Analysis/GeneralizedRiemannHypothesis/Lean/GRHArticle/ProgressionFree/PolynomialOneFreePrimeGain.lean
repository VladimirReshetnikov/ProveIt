import GRHArticle.ProgressionFree.PolynomialOneFreePrimeOptimum

/-!
# Improving the greedy valuation rule at one linear prime

The all-prime greedy set is the constant assignment in the one-free-prime
family. Its degree-eight exponent prefix has size four, whereas an
arithmetic-progression-free prefix of size five is available.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Polynomial
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The original greedy set defined by ternary valuation digits at all primes. -/
def polynomialValuationGreedySet (F : Type*) [Field F] : Set F[X] :=
  {f | f ≠ 0 ∧ ∀ p, polynomialPrimeExponent p f ∈ greedyExponents}

omit [Fintype F] in
theorem oneFreePrimeFamily_greedy_eq {P : F[X]} (hm : P.Monic) (hi : Irreducible P) :
    oneFreePrimeFamily P (fun _ ↦ greedyExponents) = polynomialValuationGreedySet F := by
  ext f
  change (f ≠ 0 ∧ OneFreePrimeAdmissibleCofactor P (oneFreePrimeCofactor P f) ∧
      polynomialPrimeExponent P f ∈ greedyExponents) ↔
    (f ≠ 0 ∧ ∀ p, polynomialPrimeExponent p f ∈ greedyExponents)
  constructor
  · rintro ⟨hf, hG, hE⟩
    refine ⟨hf, fun p ↦ ?_⟩
    by_cases hp : p = P
    · simpa [hp] using hE
    · simpa only [polynomialPrimeExponent_oneFreePrimeCofactor, if_neg hp] using hG.2.2 p
  · rintro ⟨hf, hG⟩
    refine ⟨hf, ⟨monic_oneFreePrimeCofactor P f, not_dvd_oneFreePrimeCofactor hm hi f, ?_⟩, hG P⟩
    intro p
    rw [polynomialPrimeExponent_oneFreePrimeCofactor]
    split
    · exact zero_mem_greedyExponents
    · exact hG p

/-- The size of the greedy exponent set in the prefix through `t`. -/
noncomputable def greedyExponentCount (t : ℕ) : ℕ :=
  ((Finset.range (t+1)).filter (· ∈ greedyExponents)).card

private theorem greedyExponentCount_le_roth (t : ℕ) :
    greedyExponentCount t ≤ rothNumberNat (t+1) := by
  let S := (Finset.range (t+1)).filter (· ∈ greedyExponents)
  have h : ThreeAPFree (S : Set ℕ) :=
    threeAPFree_greedyExponents.mono (fun _ hn ↦ (Finset.mem_filter.mp hn).2)
  exact h.le_rothNumberNat S (fun _ hn ↦ Finset.mem_range.mp (Finset.mem_filter.mp hn).1) rfl

private theorem greedyExponentCount_eight : greedyExponentCount 8 = 4 := by
  let S : Finset ℕ := {0,1,3,4}
  have hdata : ∀ n ∈ Finset.range 9, (∀ d ∈ Nat.digits 3 n, d ≤ 1) ↔ n ∈ S := by
    decide +kernel
  have hs : (Finset.range 9).filter (· ∈ greedyExponents) = S := by
    ext n
    by_cases hn : n ∈ Finset.range 9
    · simp only [Finset.mem_filter, hn, true_and, greedyExponents, Set.mem_setOf_eq]
      exact hdata n hn
    · have hS : S ⊆ Finset.range 9 := by decide +kernel
      have hnS : n ∉ S := fun h ↦ hn (hS h)
      simp [hn, hnS]
  unfold greedyExponentCount
  rw [hs]
  decide +kernel

private theorem five_le_rothNumberNat_nine : 5 ≤ rothNumberNat 9 := by
  apply ThreeAPFree.le_rothNumberNat ({0,1,3,7,8} : Finset ℕ)
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem summable_greedyExponentWeight {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    Summable (fun t ↦ (greedyExponentCount t : ℝ)*z^t) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun t ↦ ?_)
    (summable_roth_oneFreePrime_weight h₀ h₁)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg h₀ _)
  exact_mod_cast greedyExponentCount_le_roth t

/-- The actual greedy set has a degree-ball density given by its unchanged
free-prime exponent prefixes. -/
theorem tendsto_polynomialValuationGreedySet
    {P : F[X]} (hm : P.Monic) (hi : Irreducible P) (hP : P.natDegree = 1) :
    Tendsto (polynomialBallProportion (polynomialValuationGreedySet F)) atTop
      (𝓝 (let z := (Fintype.card F : ℝ)⁻¹
        (1-z)*greedyPrimeAvoidingDensity {P}*∑' t : ℕ, (greedyExponentCount t : ℝ)*z^t)) := by
  let z := (Fintype.card F : ℝ)⁻¹
  let w (t : ℕ) := (greedyExponentCount t : ℝ)*z^t
  have hz := oneFreePrime_field_inv_bounds (F := F)
  have hs : Summable w := summable_greedyExponentWeight hz.1.le hz.2
  have hc := tendsto_weighted_rough_convolution w hs (fun _ ↦ by dsimp [w]; positivity)
    (oneFreePrimeCofactorLayer_card_div_pow_mem_Icc P) (tendsto_oneFreePrimeCofactorLayer hm hi)
  have ht := hc.const_mul (1-z)
  rw [← oneFreePrimeFamily_greedy_eq hm hi]
  rw [mul_assoc]
  refine ht.congr (fun N ↦ ?_)
  symm
  rw [polynomialBallProportion_oneFreePrimeFamily hm hi hP]
  refine congrArg (fun S : ℝ ↦ (1-z)*S) ?_
  apply Finset.sum_congr rfl
  intro t _
  simp only [oneFreePrimeExponentPrefix, greedyExponentCount, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_id, w]
  ring

private theorem greedy_sum_add_power_le_roth_sum {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    (∑' t : ℕ, (greedyExponentCount t : ℝ)*z^t) + z^8 ≤
      ∑' t : ℕ, (rothNumberNat (t+1) : ℝ)*z^t := by
  let g (t : ℕ) := (greedyExponentCount t : ℝ)*z^t
  let δ (t : ℕ) := if t = 8 then z^8 else 0
  have hg : Summable g := summable_greedyExponentWeight h₀ h₁
  have hδ : Summable δ := summable_of_ne_finset_zero (s := {8}) (by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    exact if_neg ht)
  have hr := summable_roth_oneFreePrime_weight h₀ h₁
  have hdiff : (∑' t : ℕ, (g t + δ t)) ≤ ∑' t : ℕ, (rothNumberNat (t+1) : ℝ)*z^t := by
    refine (hg.add hδ).tsum_le_tsum (fun t ↦ ?_) hr
    by_cases ht : t = 8
    · subst t
      simp only [g, δ, if_pos rfl, greedyExponentCount_eight, Nat.cast_ofNat]
      have h : (5:ℝ) ≤ (rothNumberNat 9 : ℝ) := by exact_mod_cast five_le_rothNumberNat_nine
      calc
        _ = 5*z^8 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (pow_nonneg h₀ _)
    · simp only [δ, if_neg ht, add_zero, g]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg h₀ _)
      exact_mod_cast greedyExponentCount_le_roth t
  rw [hg.tsum_add hδ, show (∑' t : ℕ, δ t) = z^8 by simp [δ, tsum_ite_eq]] at hdiff
  exact hdiff

/-- The optimum exceeds the actual greedy valuation density by the stated
cofactor contribution, and in particular by `(1-z)^3 z^8`. -/
theorem polynomialOneFreePrimeOptimum_greedy_gain
    {P : F[X]} (hm : P.Monic) (hi : Irreducible P) (hP : P.natDegree = 1) :
    let z := (Fintype.card F : ℝ)⁻¹
    let D := limsup (polynomialBallProportion (polynomialValuationGreedySet F)) atTop
    D + greedyPrimeAvoidingDensity {P}*(1-z)*z^8 ≤ polynomialOneFreePrimeOptimum P ∧
      D + (1-z)^3*z^8 ≤ polynomialOneFreePrimeOptimum P := by
  let z := (Fintype.card F : ℝ)⁻¹
  let c := greedyPrimeAvoidingDensity ({P} : Finset F[X])
  have hz := oneFreePrime_field_inv_bounds (F := F)
  have h₀ : 0 ≤ 1-z := sub_nonneg.mpr hz.2.le
  have hc := greedyPrimeAvoidingDensity_ge_exclusion_product ({P} : Finset F[X])
    (by simpa using And.intro hm hi)
  have hc' : (1-z)^2 ≤ c := by simpa [c,z,hP,pow_two] using hc
  have hc₀ : 0 ≤ c := (sq_nonneg _).trans hc'
  rw [(tendsto_polynomialValuationGreedySet hm hi hP).limsup_eq]
  have hbound := mul_le_mul_of_nonneg_left (greedy_sum_add_power_le_roth_sum (z := z) hz.1.le hz.2)
    (mul_nonneg h₀ hc₀)
  have hbase : (1-z)*c*(∑' t : ℕ, (greedyExponentCount t : ℝ)*z^t) + c*(1-z)*z^8 ≤
      polynomialOneFreePrimeOptimum P := by
    calc
      _ = (1-z)*c*((∑' t : ℕ, (greedyExponentCount t : ℝ)*z^t) + z^8) := by ring
      _ ≤ _ := hbound
  refine ⟨hbase, ?_⟩
  apply le_trans _ hbase
  apply add_le_add_right
  have hcoef := mul_le_mul_of_nonneg_right hc' (mul_nonneg h₀ (pow_nonneg hz.1.le 8))
  calc
    (1-z)^3*z^8 = (1-z)^2*((1-z)*z^8) := by ring
    _ ≤ c*((1-z)*z^8) := hcoef
    _ = c*(1-z)*z^8 := by ring

end GRHArticle.ProgressionFree
