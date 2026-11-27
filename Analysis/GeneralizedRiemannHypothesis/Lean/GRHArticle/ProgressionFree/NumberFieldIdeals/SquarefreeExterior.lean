import GRHArticle.ProgressionFree.NumberFieldIdeals.DensityExtrema
import GRHArticle.ProgressionFree.NumberFieldIdeals.ExteriorProductLoss

/-!
# Squarefree rough ideals

Outside the smooth primes allow only the exponents zero and one. Their
geometric mass is exactly one minus the squared reciprocal norm.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem localRuleMass_zero_one (p : HeightOneSpectrum (𝓞 K)) :
    localRuleMass p {0,1} = 1 - primeWeight p^2 := by
  classical
  rw [localRuleMass, tsum_eq_sum (s := ({0,1} : Finset ℕ))]
  · simp
    ring
  · intro n hn
    exact Set.indicator_of_notMem (by simpa using hn) _

/-- The exterior squarefree Euler factor after designating the smooth primes. -/
noncomputable def idealSquarefreeExteriorFactor (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∏' p : {p // p ∉ S}, (1 - primeWeight p.val^2)

/-- Rough ideals whose remaining prime exponents are at most one. -/
def squarefreeRoughIdeals (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (Ideal (𝓞 K))⁰ :=
  idealRoughLocalRule S (fun _ ↦ ({0,1} : Set ℕ))

theorem hasNaturalDensity_squarefreeRoughIdeals (S : Finset (HeightOneSpectrum (𝓞 K))) :
    HasNaturalDensity (squarefreeRoughIdeals S)
      ((∏ p ∈ S, (1 - primeWeight p)) * idealSquarefreeExteriorFactor S) := by
  simpa only [squarefreeRoughIdeals, idealSquarefreeExteriorFactor, localRuleMass_zero_one] using
    hasNaturalDensity_idealRoughLocalRule S (fun _ ↦ ({0,1} : Set ℕ)) (by simp)

theorem idealSquarefreeExteriorFactor_pos (S : Finset (HeightOneSpectrum (𝓞 K))) :
    0 < idealSquarefreeExteriorFactor S := by
  simpa only [idealSquarefreeExteriorFactor, localRuleMass_zero_one] using
    (exteriorRuleProduct_pos S (fun _ ↦ ({0,1} : Set ℕ)) (by simp)).2

/-- All prime ideals through the given absolute norm, including every prime
in a norm fiber. -/
noncomputable def primesThroughNorm (K : Type*) [Field K] [NumberField K] (Y : ℕ) :
    Finset (HeightOneSpectrum (𝓞 K)) := (finite_primes_norm_le (K := K) Y).toFinset

@[simp] theorem mem_primesThroughNorm (p : HeightOneSpectrum (𝓞 K)) (Y : ℕ) :
    p ∈ primesThroughNorm K Y ↔ absNorm p.asIdeal ≤ Y := Set.Finite.mem_toFinset _

/-- The error factor `1-v` in the article is at most the degree divided by the cutoff. -/
theorem one_sub_squarefreeExteriorFactor_le_finrank_div (Y : ℕ) (hY : 0 < Y) :
    1 - idealSquarefreeExteriorFactor (primesThroughNorm K Y) ≤ (Module.finrank ℚ K : ℝ) / Y := by
  let e : {p : HeightOneSpectrum (𝓞 K) // p ∉ primesThroughNorm K Y} ≃
      {p : HeightOneSpectrum (𝓞 K) // Y < absNorm p.asIdeal} :=
    Equiv.subtypeEquivRight fun p ↦ by simp
  have he := e.tprod_eq (fun p ↦ 1 - primeWeight p.val^2)
  change (∏' p : {p // p ∉ primesThroughNorm K Y}, (1-primeWeight p.val^2)) = _ at he
  rw [idealSquarefreeExteriorFactor,he]
  simpa only [localRuleMass_zero_one] using one_sub_exteriorRuleProduct_le_finrank_div Y hY
    (K := K) (fun _ ↦ ({0,1} : Set ℕ)) (by simp) (by simp)

theorem threeAPFree_zero_one : ThreeAPFree ({0,1} : Set ℕ) := by
  intro a ha b hb c hc he
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb hc
  omega

/-- Every admissible smooth template extends to an admissible global set
with exactly its normalized smooth weight times the exterior squarefree factor. -/
theorem squarefreeExterior_mul_weight_le_supremum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (integral : Bool) (F : Set (Ideal (𝓞 K))⁰) (hF : F ⊆ Set.range (smoothMultiplier S))
    (hf : IdealAdmissible integral F) :
    (∏ p ∈ S, (1-primeWeight p)) * (∑' J : F, (absNorm J.val.val : ℝ)⁻¹) *
      idealSquarefreeExteriorFactor S ≤ idealNaturalDensitySupremum K integral := by
  simpa only [idealSquarefreeExteriorFactor,localRuleMass_zero_one] using
    idealProductSet_density_le_supremum S ∅ integral F hF hf (fun _ ↦ ({0,1} : Set ℕ))
      (by simp) (by simp) (fun _ _ ↦ threeAPFree_zero_one)

end GRHArticle.ProgressionFree.NumberFieldIdeals
