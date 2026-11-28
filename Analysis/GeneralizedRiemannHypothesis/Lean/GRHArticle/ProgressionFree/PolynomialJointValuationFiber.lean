import GRHArticle.ProgressionFree.PolynomialExteriorValuationProduct
import GRHArticle.ProgressionFree.PolynomialPrimeDivisorTail
import GRHArticle.ProgressionFree.LightPrimeBlocks

/-!
# Exact valuation fibers in monic polynomial layers

An exact vector of selected multiplicities forces divisibility by the
corresponding product of prime powers. This gives a uniform geometric
majorant for summing over arbitrary joint valuation conditions.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The vector of prime multiplicities at a named finite collection. -/
noncomputable def selectedPrimeExponents (S : Finset F[X]) (f : F[X]) (p : ↥S) : ℕ :=
  polynomialPrimeExponent p.val f

/-- A single selected valuation vector with greedy exterior conditions. -/
def greedyExteriorValuationFiber (S : Finset F[X]) (v : ↥S → ℕ) : Set F[X] :=
  {f | (∀ p ∉ S, polynomialPrimeExponent p f ∈ greedyExponents) ∧ selectedPrimeExponents S f = v}

theorem monicFamilyProportion_valuationFiber_le (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (v : ↥S → ℕ) (n : ℕ) :
    monicFamilyProportion (greedyExteriorValuationFiber S v) n ≤
      reciprocalExponentWeight (fun p : ↥S ↦ polynomialPrimeWeight p.val) v := by
  let M := ∏ p : ↥S, p.val^(v p)
  have hm : M.Monic := monic_prod_of_monic _ _
    (fun (p : ↥S) _ ↦ (hS p p.property).1.pow _)
  have hd : M.natDegree = ∑ p : ↥S, v p * p.val.natDegree := by
    rw [show M = ∏ p : ↥S, p.val^(v p) from rfl, natDegree_prod _ _
      (fun (p : ↥S) _ ↦ pow_ne_zero _ (hS p p.property).2.ne_zero)]
    simp only [natDegree_pow]
  have hsub : monicFamilyLayer (greedyExteriorValuationFiber S v) n ⊆ monicMultipleLayer M n := by
    intro f hf
    obtain ⟨hfm,hfn,_,hv⟩ := mem_monicFamilyLayer.mp hf
    refine Finset.mem_filter.mpr ⟨mem_monicLayer.mpr ⟨hfm,hfn⟩, ?_⟩
    apply Fintype.prod_dvd_of_coprime
    · intro p r hne
      have hp := hS p p.property
      have hr := hS r r.property
      apply IsCoprime.pow
      exact isRelPrime_iff_isCoprime.mp (hp.2.isRelPrime_iff_not_dvd.mpr fun hdiv ↦
        hne (Subtype.ext (eq_of_monic_of_associated hp.1 hr.1 (hp.2.associated_of_dvd hr.2 hdiv))))
    · intro p
      have hp := hS p p.property
      have he := congrFun hv p
      change polynomialPrimeExponent p.val f = v p at he
      rw [pow_dvd_iff_le_emultiplicity, emultiplicity_eq_count_normalizedFactors hp.2 hfm.ne_zero,
        hp.1.normalize_eq_self, ← he]
      exact le_rfl
  let q : ℝ := Fintype.card F
  have hq : 0 < q := by dsimp [q]; positivity
  have hc := (Nat.mul_le_mul_right (Fintype.card F ^ M.natDegree)
    (Finset.card_le_card hsub)).trans (card_monicMultipleLayer_mul_pow_le hm n)
  have hreal : ((monicFamilyLayer (greedyExteriorValuationFiber S v) n).card : ℝ) *
      q^M.natDegree ≤ q^n := by dsimp [q]; exact_mod_cast hc
  have hw : reciprocalExponentWeight (fun p : ↥S ↦ polynomialPrimeWeight p.val) v =
      (q^M.natDegree)⁻¹ := by
    unfold reciprocalExponentWeight polynomialPrimeWeight
    rw [hd, ← inv_pow, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun p _ ↦ by rw [Nat.mul_comm (v p), pow_mul]
  rw [hw]
  change _ / q^n ≤ (q^M.natDegree)⁻¹
  rw [div_le_iff₀ (pow_pos hq _), ← div_eq_inv_mul, le_div_iff₀ (pow_pos hq _)]
  exact hreal

private theorem primeExponentWeight_singleton (w : ℝ) (n : ℕ) : primeExponentWeight w {n} = w^n := by
  unfold primeExponentWeight
  simp [Set.indicator_singleton]

/-- The exact pattern has its expected geometric limit even with infinitely
many exterior greedy requirements. -/
theorem tendsto_monicFamilyProportion_valuationFiber (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) (v : ↥S → ℕ) :
    Tendsto (monicFamilyProportion (greedyExteriorValuationFiber S v)) atTop
      (𝓝 (greedyPrimeAvoidingDensity S *
        reciprocalExponentWeight (fun p : ↥S ↦ polynomialPrimeWeight p.val) v)) := by
  let D (p : F[X]) : Set ℕ := if hp : p ∈ S then {v ⟨p,hp⟩} else Set.univ
  have ht := tendsto_monicValuationRuleSet_greedyExterior S D hS
  have hprod : (∏ p ∈ S, primeExponentWeight (polynomialPrimeWeight p) (D p)) =
      reciprocalExponentWeight (fun p : ↥S ↦ polynomialPrimeWeight p.val) v := by
    rw [← Finset.prod_attach S, reciprocalExponentWeight, Finset.univ_eq_attach]
    apply Finset.prod_congr rfl
    intro p _
    simp [D, p.property, primeExponentWeight_singleton]
  change Tendsto _ _ (𝓝 (greedyPrimeAvoidingDensity S *
    ∏ p ∈ S, primeExponentWeight (polynomialPrimeWeight p) (D p))) at ht
  rw [hprod] at ht
  refine ht.congr fun n ↦ ?_
  apply congrArg (fun A : Finset F[X] ↦ (A.card : ℝ) / (Fintype.card F : ℝ)^n)
  ext f
  rw [mem_monicFamilyLayer, mem_monicFamilyLayer]
  refine and_congr_right fun hm ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨_,hc⟩
    refine ⟨fun p hp ↦ by simpa [replacePrimeRules, hp] using hc p, funext fun p ↦ ?_⟩
    simpa [selectedPrimeExponents, replacePrimeRules, D, p.property] using hc p.val
  · rintro ⟨ho,hs⟩
    refine ⟨hm,fun p ↦ ?_⟩
    by_cases hp : p ∈ S
    · simpa [replacePrimeRules, D, hp, selectedPrimeExponents] using congrFun hs ⟨p,hp⟩
    · simpa [replacePrimeRules, hp] using ho p hp

end GRHArticle.ProgressionFree
