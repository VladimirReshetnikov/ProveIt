import GRHArticle.ProgressionFree.NumberFieldIdeals.LocalMassBounds
import GRHArticle.ProgressionFree.NumberFieldIdeals.PrimeSquareSieve

/-!
# Euler density for infinitely many prime-ideal exponent restrictions

A finite approximation can miss a condition outside a large norm ball
only on a multiple of a large prime square. Uniform control of this error
transfers the finite product formula to the infinite rule.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors Classical

variable {K : Type*} [Field K] [NumberField K]

/-- All nonzero integral ideals satisfying the allowed-exponent rules. -/
def infiniteLocalRule (A : HeightOneSpectrum (𝓞 K) → Set ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {I | ∀ p, primeExponent p I ∈ A p}

theorem finite_primes_norm_le (Y : ℕ) :
    {p : HeightOneSpectrum (𝓞 K) | absNorm p.asIdeal ≤ Y}.Finite := by
  have hi : Function.Injective (primeIdeal (K := K)) := fun _ _ h ↦
    HeightOneSpectrum.ext (congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ I.val) h)
  exact (finite_setOf_absNorm_le₀ (S := 𝓞 K) Y).preimage hi.injOn

private theorem count_union_bound {A B C : Set (Ideal (𝓞 K))⁰} (h : B ⊆ A ∪ C)
    {X : ℝ} (hX : 0 ≤ X) : countUpTo B X ≤ countUpTo A X + countUpTo C X := by
  let ball := {I : (Ideal (𝓞 K))⁰ | (absNorm I.val : ℝ) ≤ X}
  have he : (A ∪ C) ∩ ball = A ∩ ball ∪ C ∩ ball := Set.union_inter_distrib_right _ _ _
  apply (countUpTo_mono h le_rfl hX).trans
  change ((A ∪ C) ∩ ball).ncard ≤ (A ∩ ball).ncard + (C ∩ ball).ncard
  rw [he]
  exact Set.ncard_union_le _ _

private theorem finite_approx_subset {S F : Finset (HeightOneSpectrum (𝓞 K))}
    {A : HeightOneSpectrum (𝓞 K) → Set ℕ} (h0 : ∀ p, 0 ∈ A p) (h1 : ∀ p ∉ S, 1 ∈ A p)
    (hS : S ⊆ F) {Y : ℕ} (hY : ∀ p, absNorm p.asIdeal ≤ Y → p ∈ F) :
    finiteLocalRule F A ⊆ infiniteLocalRule A ∪ largePrimeSquareMultiples K Y := by
  intro I hI
  by_cases h : I ∈ infiniteLocalRule A
  · exact Or.inl h
  · obtain ⟨p,hp⟩ := not_forall.mp h
    have hf : p ∉ F := fun pm ↦ hp (hI p pm)
    have hzero : primeExponent p I ≠ 0 := fun hz ↦ hp (hz ▸ h0 p)
    have hone : primeExponent p I ≠ 1 := fun ho ↦ hp (ho ▸ h1 p (fun pm ↦ hf (hS pm)))
    have he := ((primeExponent_eq_iff p I (primeExponent p I)).mp rfl).1
    refine Or.inr ⟨p,lt_of_not_ge (fun hy ↦ hf (hY p hy)),?_⟩
    rw [nonZeroDivisors_dvd_iff_dvd_coe,SubmonoidClass.coe_pow]
    exact (pow_dvd_pow p.asIdeal (by omega : 2 ≤ primeExponent p I)).trans he

/-- The infinite Euler density formula for prime-ideal rules containing
zero everywhere and one outside a finite exceptional set. -/
theorem hasNaturalDensity_infiniteLocalRule (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : HeightOneSpectrum (𝓞 K) → Set ℕ) (h0 : ∀ p, 0 ∈ A p) (h1 : ∀ p ∉ S, 1 ∈ A p) :
    HasNaturalDensity (infiniteLocalRule A) (∏' p, localRuleMass p (A p)) := by
  let D := ∏' p, localRuleMass p (A p)
  let r := dedekindZeta_residue K
  have hp := (localRuleEulerProduct S A h0 h1).1.hasProd
  have hlim : Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 K)) ↦
      (∏ p ∈ F, localRuleMass p (A p)) * r) atTop (𝓝 (D*r)) := hp.mul_const r
  apply (hasNaturalDensity_iff_tendsto_div _ _).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε/3 := by positivity
  obtain ⟨Y,hY⟩ := (eventually_largePrimeSquareMultiples_countUpTo_lt (K := K) he).exists
  obtain ⟨F₀,hF₀⟩ := Metric.tendsto_atTop.mp hlim (ε/3) he
  let F := F₀ ∪ S ∪ (finite_primes_norm_le (K := K) Y).toFinset
  have hF := hF₀ F (subset_union_left.trans subset_union_left)
  rw [Real.dist_eq] at hF
  have hleft : infiniteLocalRule A ⊆ finiteLocalRule F A := fun I h p _ ↦ h p
  have hright := finite_approx_subset h0 h1 (F := F) (subset_union_right.trans subset_union_left)
    (fun p hp ↦ mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hp))
  have ht := (hasNaturalDensity_iff_tendsto_div _ _).mp (hasNaturalDensity_finiteLocalRule F A)
  filter_upwards [Metric.tendsto_nhds.mp ht (ε/3) he, eventually_gt_atTop (0:ℝ)] with X hx hX
  rw [Real.dist_eq] at hx ⊢
  have hu := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).mpr (countUpTo_mono hleft le_rfl hX.le)) hX.le
  have hl := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).mpr (count_union_bound hright hX.le)) hX.le
  rw [Nat.cast_add,add_div] at hl
  change |(countUpTo (infiniteLocalRule A) X : ℝ)/X - D*r| < ε
  change |(countUpTo (finiteLocalRule F A) X : ℝ)/X - (∏ p ∈ F, localRuleMass p (A p))*r| < ε/3 at hx
  apply abs_lt.mpr
  constructor <;> linarith only [hl,hu,hY X hX,(abs_lt.mp hx).1,(abs_lt.mp hx).2,
    (abs_lt.mp hF).1,(abs_lt.mp hF).2,hε]

end GRHArticle.ProgressionFree.NumberFieldIdeals
