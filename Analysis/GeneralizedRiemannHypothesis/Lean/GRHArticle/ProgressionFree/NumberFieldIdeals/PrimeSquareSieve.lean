import GRHArticle.ProgressionFree.NumberFieldIdeals.SquareNormTail
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Discarding prime squares of large norm

Count a union of (possibly overlapping) divisibility conditions by a sum.
The ideal counting estimate makes the resulting inverse-square bound
uniform at every positive cutoff.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem countUpTo_iUnion_div_le {ι : Type*} (E : ι → Set (Ideal (𝓞 K))⁰)
    (g : ι → ℝ) (hg : Summable g) (hg0 : ∀ j, 0 ≤ g j) {X : ℝ} (hX : 0 < X)
    (h : ∀ j, (countUpTo (E j) X : ℝ)/X ≤ g j) :
    (countUpTo (⋃ j, E j) X : ℝ)/X ≤ ∑' j, g j := by
  classical
  let ball := {I : (Ideal (𝓞 K))⁰ | (absNorm I.val : ℝ) ≤ X}
  have hf : ball.Finite := (finite_setOf_absNorm_le₀ (S := 𝓞 K) ⌊X⌋₊).subset
    fun _ hI ↦ (Nat.le_floor_iff hX.le).mpr hI
  let F (A : Set (Ideal (𝓞 K))⁰) := (hf.subset (Set.inter_subset_right (s := A))).toFinset
  have hF (A : Set (Ideal (𝓞 K))⁰) : countUpTo A X = (F A).card :=
    Set.ncard_eq_toFinset_card (A ∩ ball) _
  let U := F (⋃ j, E j)
  choose witness hw using fun I : U ↦ Set.mem_iUnion.mp ((Set.Finite.mem_toFinset _).mp I.property).1
  let T := Finset.univ.image witness
  have hsub : U ⊆ T.biUnion (fun j ↦ F (E j)) := by
    intro I hI
    let u : U := ⟨I,hI⟩
    exact mem_biUnion.mpr ⟨witness u, mem_image_of_mem witness (mem_univ _),
      (Set.Finite.mem_toFinset _).mpr ⟨hw u, ((Set.Finite.mem_toFinset _).mp hI).2⟩⟩
  have hc := (card_le_card hsub).trans (card_biUnion_le)
  calc
    _ ≤ ((∑ j ∈ T, countUpTo (E j) X : ℕ) : ℝ)/X := by
      apply div_le_div_of_nonneg_right _ hX.le
      exact_mod_cast (by simpa only [hF,U] using hc :
        countUpTo (⋃ j, E j) X ≤ ∑ j ∈ T, countUpTo (E j) X)
    _ = ∑ j ∈ T, (countUpTo (E j) X : ℝ)/X := by rw [Nat.cast_sum, sum_div]
    _ ≤ ∑ j ∈ T, g j := sum_le_sum fun j _ ↦ h j
    _ ≤ _ := hg.sum_le_tsum T (fun j _ ↦ hg0 j)

/-- Ideals divisible by the square of at least one prime ideal of norm
strictly greater than the cutoff. -/
def largePrimeSquareMultiples (K : Type*) [Field K] [NumberField K] (Y : ℕ) :
    Set (Ideal (𝓞 K))⁰ :=
  {I | ∃ p : HeightOneSpectrum (𝓞 K), Y < absNorm p.asIdeal ∧ primeIdeal p ^ 2 ∣ I}

private noncomputable def weight (Y : ℕ) (p : HeightOneSpectrum (𝓞 K)) : ℝ :=
  if Y < absNorm p.asIdeal then ((absNorm p.asIdeal : ℝ)^2)⁻¹ else 0

private theorem weight_bound (Y : ℕ) (p : HeightOneSpectrum (𝓞 K)) :
    0 ≤ weight Y p ∧ weight Y p ≤ ((absNorm p.asIdeal : ℝ)^2)⁻¹ := by
  unfold weight
  split_ifs <;> constructor <;> first | rfl | positivity

private theorem summable_weight (Y : ℕ) : Summable (weight (K := K) Y) :=
  (summable_primeIdeal_inv_sq_absNorm (K := K)).of_nonneg_of_le (fun p ↦ (weight_bound Y p).1)
    (fun p ↦ (weight_bound Y p).2)

set_option maxHeartbeats 800000 in
/-- The norm-normalized counts of the discarded ideals tend to zero as
the norm cutoff on prime divisors increases, uniformly in the sample size. -/
theorem eventually_largePrimeSquareMultiples_countUpTo_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (countUpTo (largePrimeSquareMultiples K Y) X : ℝ)/X < ε := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_mul_image_bound (K := K)
  have hw (p : HeightOneSpectrum (𝓞 K)) : Tendsto (fun Y ↦ weight Y p) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (absNorm p.asIdeal)] with Y hY
    simp [weight,not_lt.mpr hY]
  have hs := tendsto_tsum_of_dominated_convergence (summable_primeIdeal_inv_sq_absNorm (K := K)) hw
    (Eventually.of_forall fun Y p ↦ by simpa only [Real.norm_of_nonneg (weight_bound Y p).1] using (weight_bound Y p).2)
  rw [tsum_zero] at hs
  have hlim := (tendsto_const_nhds (x := C)).mul hs
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually_lt_const hε] with Y hY
  intro X hX
  let E (p : HeightOneSpectrum (𝓞 K)) : Set (Ideal (𝓞 K))⁰ :=
    if Y < absNorm p.asIdeal then ((primeIdeal p^2) * ·) '' Set.univ else ∅
  have he : largePrimeSquareMultiples K Y = ⋃ p, E p := by
    ext I
    simp only [largePrimeSquareMultiples,Set.mem_setOf_eq,Set.mem_iUnion]
    apply exists_congr
    intro p
    by_cases hp : Y < absNorm p.asIdeal
    · simp only [E,if_pos hp,hp,true_and,Set.mem_image,Set.mem_univ,true_and]
      exact exists_congr fun _ ↦ eq_comm
    · simp [E,hp]
  rw [he]
  apply lt_of_le_of_lt _ hY
  rw [← tsum_mul_left]
  apply countUpTo_iUnion_div_le E _ ((summable_weight Y).mul_left C)
    (fun p ↦ mul_nonneg hC.le (weight_bound Y p).1) hX
  intro p
  by_cases hp : Y < absNorm p.asIdeal
  · simp only [E,weight,if_pos hp, ← div_eq_mul_inv]
    have h := hbound (primeIdeal p^2) (Set.univ : Set (Ideal (𝓞 K))⁰) X hX
    simpa only [show (primeIdeal p^2).val = p.asIdeal^2 from rfl,map_pow,Nat.cast_pow] using h
  · simp [E,weight,hp,countUpTo]

end GRHArticle.ProgressionFree.NumberFieldIdeals
