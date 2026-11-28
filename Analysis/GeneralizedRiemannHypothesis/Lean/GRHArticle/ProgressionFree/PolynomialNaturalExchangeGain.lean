import GRHArticle.ProgressionFree.PolynomialNaturalExchangeIdentity
import GRHArticle.ProgressionFree.PolynomialNaturalExchangeNumerics
import GRHArticle.ProgressionFree.PolynomialOneFreePrimeGain
import GRHArticle.ProgressionFree.PolynomialValuationScalarClosure

/-!
# Exact natural-density gain for a finite exchange of polynomial valuations

The limiting difference for the actual polynomial degree balls factors as
the greedy cofactor constant times the weight of one copy of every chosen
prime times the difference of three local exponent products.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The selected local weights in any enumeration of the finite set. -/
noncomputable def naturalExchangePrimeWeights (S : Finset F[X]) : List ℝ :=
  S.toList.map (fun p ↦ (Fintype.card F : ℝ)⁻¹^p.natDegree)

/-- Exact gain for the polynomial valuation exchange on a specified set. -/
noncomputable def polynomialNaturalExchangeGain (S : Finset F[X]) : ℝ :=
  greedyPrimeAvoidingDensity S * (naturalExchangePrimeWeights S).prod *
    naturalExchangeBracket (naturalExchangePrimeWeights S)

omit [Fintype F] in
private theorem scalarClosure_naturalExchangeFamily (S : Finset F[X]) :
    polynomialScalarClosure (polynomialNaturalExchangeFamily S) = polynomialNaturalExchangeFamily S := by
  let V (v : F[X] → ℕ) := (∀ p ∉ S, v p ∈ greedyExponents) ∧
    (fun i : ↥S ↦ v i.val) ∈ naturalExchangeRule greedyExponents ↥S
  change polynomialScalarClosure {f : F[X] | f ≠ 0 ∧ V (fun p ↦ polynomialPrimeExponent p f)} = _
  rw [show polynomialNaturalExchangeFamily S =
    polynomialScalarClosure {f : F[X] | V (fun p ↦ polynomialPrimeExponent p f)} from
      (polynomialScalarClosure_valuationPredicate V).symm]
  ext f
  constructor
  · rintro ⟨g,⟨_,hg⟩,hm,a,ha,h⟩; exact ⟨g,hg,hm,a,ha,h⟩
  · rintro ⟨g,hg,hm,a,ha,h⟩; exact ⟨g,⟨hm.ne_zero,hg⟩,hm,a,ha,h⟩

omit [Fintype F] in
private theorem scalarClosure_greedyExteriorProfile_greedy (S : Finset F[X]) :
    polynomialScalarClosure (greedyExteriorProfile S greedyExponents) = polynomialValuationGreedySet F := by
  let V (v : F[X] → ℕ) := ∀ p, v p ∈ greedyExponents
  rw [show polynomialValuationGreedySet F =
    polynomialScalarClosure {f : F[X] | V (fun p ↦ polynomialPrimeExponent p f)} from
      (polynomialScalarClosure_valuationPredicate V).symm]
  ext f
  constructor
  · rintro ⟨g,hg,hm,a,ha,h⟩
    obtain ⟨_,ho,hs⟩ := mem_greedyExteriorProfile.mp hg
    exact ⟨g,fun p ↦ if hp : p ∈ S then hs p hp else ho p hp,hm,a,ha,h⟩
  · rintro ⟨g,hg,hm,a,ha,h⟩
    exact ⟨g,mem_greedyExteriorProfile.mpr ⟨hm,fun p _ ↦ hg p,fun p _ ↦ hg p⟩,hm,a,ha,h⟩

/-- Both actual degree-ball proportions converge. Their limiting difference
is exactly the exchange gain, for any finite set of distinct monic primes. -/
theorem polynomialNaturalExchange_density_gain (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p) :
    ∃ g : ℝ, Tendsto (polynomialBallProportion (polynomialValuationGreedySet F)) atTop (𝓝 g) ∧
      Tendsto (polynomialBallProportion (polynomialNaturalExchangeFamily S)) atTop
        (𝓝 (g + polynomialNaturalExchangeGain S)) := by
  let z := (Fintype.card F : ℝ)⁻¹
  let w (p : F[X]) := z^p.natDegree
  let c := greedyPrimeAvoidingDensity S
  let m (D : Set ℕ) := c * ∏ p ∈ S, primeExponentWeight (w p) D
  let g := m greedyExponents
  have hz := oneFreePrime_field_inv_bounds (F := F)
  have hw (p : F[X]) (hp : p ∈ S) : w p ∈ Set.Ico 0 1 :=
    ⟨pow_nonneg hz.1.le _, pow_lt_one₀ hz.1.le hz.2 (hS p hp).2.natDegree_pos.ne'⟩
  have hl (D : Set ℕ) : Tendsto (monicFamilyProportion (greedyExteriorProfile S D)) atTop (𝓝 (m D)) :=
    tendsto_monicValuationRuleSet_greedyExterior S (fun _ ↦ D) hS
  have hmplus : m ({1,2}:Set ℕ) = c * ((∏ p ∈ S, w p) * ∏ p ∈ S, (1+w p)) := by
    simp only [m, primeExponentWeight_cube, Finset.prod_mul_distrib]
  have hmone : m ({1}:Set ℕ) = c * ∏ p ∈ S, w p := by simp only [m, primeExponentWeight_one]
  have hmpos : m strictlyPositiveGreedyExponents =
      c * ((∏ p ∈ S, w p) * ∏ p ∈ S, positiveGreedyWeight (w p)) := by
    unfold m
    congr 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp ↦ primeExponentWeight_positiveGreedy (hw p hp).1 (hw p hp).2
  have he : g + m {1,2} - m strictlyPositiveGreedyExponents - m {1} =
      g + polynomialNaturalExchangeGain S := by
    simp only [hmplus, hmone, hmpos, polynomialNaturalExchangeGain, naturalExchangePrimeWeights,
      naturalExchangeBracket, List.map_map, Finset.prod_map_toList, Function.comp_apply]
    dsimp only [Function.comp_def, c, w, z]
    ring
  have hE : Tendsto (monicFamilyProportion (polynomialNaturalExchangeFamily S)) atTop
      (𝓝 (g + polynomialNaturalExchangeGain S)) := by
    rw [← he]
    refine ((((hl greedyExponents).add (hl {1,2})).sub (hl strictlyPositiveGreedyExponents)).sub
      (hl {1})).congr fun n ↦ ?_
    have hn := card_monicFamilyLayer_naturalExchange S n
    have hreal : ((monicFamilyLayer (polynomialNaturalExchangeFamily S) n).card : ℝ) +
        (monicFamilyLayer (greedyExteriorProfile S strictlyPositiveGreedyExponents) n).card +
        (monicFamilyLayer (greedyExteriorProfile S {1}) n).card =
        (monicFamilyLayer (greedyExteriorProfile S greedyExponents) n).card +
        (monicFamilyLayer (greedyExteriorProfile S {1,2}) n).card := by exact_mod_cast hn
    dsimp only [monicFamilyProportion]
    rw [← add_div, ← sub_div, ← sub_div]
    congr 1
    linarith only [hreal]
  exact ⟨g, by simpa only [scalarClosure_greedyExteriorProfile_greedy] using
    tendsto_polynomialBallProportion_scalarClosure (hl greedyExponents),
    by simpa only [scalarClosure_naturalExchangeFamily] using
      tendsto_polynomialBallProportion_scalarClosure hE⟩

end GRHArticle.ProgressionFree
