import GRHArticle.ProgressionFree.PolynomialJointValuationFiber
import GRHArticle.ProgressionFree.PolynomialNaturalExchange
import GRHArticle.ProgressionFree.PolynomialValuationScalarClosure

/-!
# The full joint valuation law with a greedy exterior

The exponent vectors allowed at the selected primes can form any subset,
including infinite sets with dependencies between the coordinates. The
limiting geometric weight is summed over that exact subset.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

private theorem valuationFamily_layer_sum (S : Finset F[X]) (V : Set (↥S → ℕ)) (n : ℕ) :
    monicFamilyProportion (polynomialValuationFamily S greedyExponents V) n =
      ∑' v : ↥S → ℕ, V.indicator
        (fun u ↦ monicFamilyProportion (greedyExteriorValuationFiber S u) n) v := by
  let B := monicFamilyLayer (polynomialValuationFamily S greedyExponents V) n
  let vOf := selectedPrimeExponents S
  let I := B.image vOf
  have hacc (f : F[X]) (hf : f ∈ B) : vOf f ∈ V := (mem_monicFamilyLayer.mp hf).2.2.2.2
  have hsplit := Finset.card_eq_sum_card_image vOf B
  have hsum (v : ↥S → ℕ) (hv : v ∈ V) :
      B.filter (fun f ↦ vOf f = v) = monicFamilyLayer (greedyExteriorValuationFiber S v) n := by
    ext f
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hf,he⟩
      obtain ⟨hm,hd,_,ho,_⟩ := mem_monicFamilyLayer.mp hf
      exact mem_monicFamilyLayer.mpr ⟨hm,hd,ho,he⟩
    · intro hf
      obtain ⟨hm,hd,ho,he⟩ := mem_monicFamilyLayer.mp hf
      exact ⟨mem_monicFamilyLayer.mpr ⟨hm,hd,hm.ne_zero,ho,show selectedPrimeExponents S f ∈ V by rw [he]; exact hv⟩,he⟩
  rw [tsum_eq_sum (s := I)]
  · change (B.card : ℝ) / (Fintype.card F : ℝ)^n = _
    rw [hsplit, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    obtain ⟨f,hf,hv'⟩ := Finset.mem_image.mp hv
    have hv₀ := hv' ▸ hacc f hf
    rw [hsum v hv₀, Set.indicator_of_mem hv₀]
    rfl
  · intro v hv
    by_cases h : v ∈ V
    · rw [Set.indicator_of_mem h, monicFamilyProportion, ← hsum v h]
      have hzero : B.filter (fun f ↦ vOf f = v) = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun f hf ↦ hv (Finset.mem_image.mpr ⟨f,(Finset.mem_filter.mp hf).1,(Finset.mem_filter.mp hf).2⟩))
      simp [hzero]
    · exact Set.indicator_of_notMem h _

/-- The limiting measure of an arbitrary joint exponent condition in exact
monic degree layers equals its geometric mass times the greedy cofactor density. -/
theorem tendsto_monicFamilyProportion_jointValuations (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (V : Set (↥S → ℕ)) :
    Tendsto (monicFamilyProportion (polynomialValuationFamily S greedyExponents V)) atTop
      (𝓝 (greedyPrimeAvoidingDensity S *
        reciprocalExponentMass (fun p : ↥S ↦ polynomialPrimeWeight p.val) V)) := by
  let w (p : ↥S) := polynomialPrimeWeight p.val
  let b := reciprocalExponentWeight w
  let a (n : ℕ) (v : ↥S → ℕ) := V.indicator
    (fun u ↦ monicFamilyProportion (greedyExteriorValuationFiber S u) n) v
  let c := greedyPrimeAvoidingDensity S
  have hw (p : ↥S) : 0 ≤ w p ∧ w p < 1 := by
    have hq : (1:ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
    have hz := inv_lt_one_of_one_lt₀ hq
    exact ⟨by dsimp [w, polynomialPrimeWeight]; positivity,
      pow_lt_one₀ (by positivity) hz (hS p p.property).2.natDegree_pos.ne'⟩
  have hb : Summable b := summable_reciprocalExponentWeight (fun p ↦ (hw p).1) (fun p ↦ (hw p).2)
  have hpoint (v : ↥S → ℕ) : Tendsto (a · v) atTop (𝓝 (c*V.indicator b v)) := by
    by_cases hv : v ∈ V
    · simpa only [a, Set.indicator_of_mem hv] using tendsto_monicFamilyProportion_valuationFiber S hS v
    · simp only [a, Set.indicator_of_notMem hv, mul_zero, tendsto_const_nhds]
  have hbound (n : ℕ) (v : ↥S → ℕ) : ‖a n v‖ ≤ b v := by
    by_cases hv : v ∈ V
    · simp only [a, Set.indicator_of_mem hv, Real.norm_eq_abs,
        abs_of_nonneg (monicFamilyProportion_mem_unitInterval _ _).1]
      exact monicFamilyProportion_valuationFiber_le S hS v n
    · simpa only [a, Set.indicator_of_notMem hv, norm_zero] using
        reciprocalExponentWeight_nonneg (fun p ↦ (hw p).1) v
  have ht := tendsto_tsum_of_dominated_convergence hb hpoint (Eventually.of_forall hbound)
  rw [tsum_mul_left] at ht
  exact ht.congr fun n ↦ (valuationFamily_layer_sum S V n).symm

/-- Full natural-density form of the article's joint law. The first factor
is the exterior Euler product. The remaining factors are exactly the joint
probability under the independent geometric laws on the selected primes. -/
theorem tendsto_polynomialBallProportion_jointValuations (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (V : Set (↥S → ℕ)) :
    Tendsto (polynomialBallProportion (polynomialValuationFamily S greedyExponents V)) atTop
      (𝓝 (greedyPrimeExteriorProduct S * (polynomialPrimeExclusionWeight S *
        reciprocalExponentMass (fun p : ↥S ↦ polynomialPrimeWeight p.val) V))) := by
  let W (e : F[X] → ℕ) := (∀ p ∉ S, e p ∈ greedyExponents) ∧ (fun p : ↥S ↦ e p.val) ∈ V
  have h := tendsto_monicFamilyProportion_jointValuations S hS V
  have hl : monicFamilyProportion {f : F[X] | W (fun p ↦ polynomialPrimeExponent p f)} =
      monicFamilyProportion (polynomialValuationFamily S greedyExponents V) := by
    funext n
    apply congrArg (fun A : Finset F[X] ↦ (A.card : ℝ)/(Fintype.card F : ℝ)^n)
    ext f
    rw [mem_monicFamilyLayer, mem_monicFamilyLayer]
    refine and_congr_right fun hm ↦ and_congr_right fun _ ↦ ⟨fun hf ↦ ⟨hm.ne_zero,hf⟩,fun hf ↦ hf.2⟩
  rw [← hl] at h
  have ht := tendsto_polynomialBallProportion_valuationPredicate W h
  rw [greedyPrimeAvoidingDensity_eq_exclusion_mul_exteriorProduct S hS, mul_right_comm,
    mul_comm (polynomialPrimeExclusionWeight S * _)] at ht
  exact ht

end GRHArticle.ProgressionFree
