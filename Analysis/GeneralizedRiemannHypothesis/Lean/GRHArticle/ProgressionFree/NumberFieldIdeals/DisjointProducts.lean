import GRHArticle.ProgressionFree.NumberFieldIdeals.UniformCounts
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Density of an infinite union of disjoint ideal products

A summable reciprocal-norm bound justifies adding the densities of any
family of disjoint dilations. In particular the smooth template in the
article's product set may be infinite.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem countUpTo_iUnion {S : Type*} (J : S → (Ideal (𝓞 K))⁰) (hJ : Function.Injective J)
    (A : S → Set (Ideal (𝓞 K))⁰)
    (hdis : Pairwise fun i j : S ↦ Disjoint ((J i * ·) '' A i) ((J j * ·) '' A j))
    {X : ℝ} (hX : 0 ≤ X) :
    (countUpTo (⋃ j : S, (J j * ·) '' A j) X : ℝ) =
      ∑' j : S, (countUpTo ((J j * ·) '' A j) X : ℝ) := by
  classical
  let ball := {I : (Ideal (𝓞 K))⁰ | (absNorm I.val : ℝ) ≤ X}
  have hf : ball.Finite := (finite_setOf_absNorm_le₀ (S := 𝓞 K) ⌊X⌋₊).subset
    fun _ hI ↦ (Nat.le_floor_iff hX).mpr hI
  let T : Finset S := (hf.preimage (f := J) hJ.injOn).toFinset
  let F (B : Set (Ideal (𝓞 K))⁰) := (hf.subset (Set.inter_subset_right (s := B))).toFinset
  have hF (B : Set (Ideal (𝓞 K))⁰) : countUpTo B X = (F B).card :=
    Set.ncard_eq_toFinset_card (B ∩ ball) _
  let E (j : S) := (J j * ·) '' A j
  have hmem {j : S} {I : (Ideal (𝓞 K))⁰} (hI : I ∈ F (E j)) : j ∈ T := by
    obtain ⟨⟨I',_,rfl⟩,hx⟩ := (Set.Finite.mem_toFinset _).mp hI
    apply (Set.Finite.mem_toFinset _).mpr
    change (absNorm (J j).val : ℝ) ≤ X
    change (absNorm (J j*I').val : ℝ) ≤ X at hx
    rw [Submonoid.coe_mul,map_mul,Nat.cast_mul] at hx
    have hI1 : (1:ℝ) ≤ absNorm I'.val := by exact_mod_cast absNorm_pos_of_nonZeroDivisors I'
    exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hI1).trans hx
  have hUnion : F (⋃ j : S, E j) = T.biUnion (fun j ↦ F (E j)) := by
    ext I
    simp only [F,Set.Finite.mem_toFinset,Set.mem_inter_iff,Set.mem_iUnion,mem_biUnion]
    constructor
    · rintro ⟨⟨j,hj⟩,hb⟩
      exact ⟨j,hmem ((Set.Finite.mem_toFinset _).mpr ⟨hj,hb⟩),hj,hb⟩
    · rintro ⟨j,_,hj,hb⟩
      exact ⟨⟨j,hj⟩,hb⟩
  change (countUpTo (⋃ j : S, E j) X : ℝ) = ∑' j : S, (countUpTo (E j) X : ℝ)
  simp_rw [hF]
  rw [hUnion,card_biUnion, Nat.cast_sum,tsum_eq_sum (s := T)]
  · intro j hj
    simp [(eq_empty_iff_forall_notMem.mpr (fun _ hn ↦ hj (hmem hn)) : F (E j) = ∅)]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro I hi hj
    exact Set.disjoint_left.mp (hdis hij)
      ((Set.Finite.mem_toFinset _).mp hi).1 ((Set.Finite.mem_toFinset _).mp hj).1

/-- Density of pairwise disjoint ideal products with a summable family of
reciprocal multiplier norms, including variable rules on the factors. -/
theorem hasNaturalDensity_disjointMulImages {S : Type*} (J : S → (Ideal (𝓞 K))⁰)
    (hJ : Function.Injective J) (A : S → Set (Ideal (𝓞 K))⁰)
    {d : S → ℝ} (hA : ∀ j, HasNaturalDensity (A j) (d j))
    (hdis : Pairwise fun i j : S ↦ Disjoint ((J i * ·) '' A i) ((J j * ·) '' A j))
    (hS : Summable fun j : S ↦ (absNorm (J j).val : ℝ)⁻¹) :
    HasNaturalDensity (⋃ j : S, (J j * ·) '' A j) (∑' j : S, d j / absNorm (J j).val) := by
  let E (j : S) := (J j * ·) '' A j
  let f (X : ℝ) (j : S) := (countUpTo (E j) X : ℝ)/X
  have hlim (j : S) : Tendsto (f · j) atTop (𝓝 ((d j / absNorm (J j).val) * dedekindZeta_residue K)) :=
    (hasNaturalDensity_iff_tendsto_div _ _).mp ((hA j).mul_image (J j))
  obtain ⟨C,_,hC⟩ := exists_uniform_mul_image_bound (K := K)
  have hbound : ∀ᶠ X in atTop, ∀ j : S, ‖f X j‖ ≤ C * (absNorm (J j).val : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX j
    rw [Real.norm_of_nonneg (by dsimp [f]; positivity), ← div_eq_mul_inv]
    exact hC (J j) (A j) X hX
  have hlim' := tendsto_tsum_of_dominated_convergence (hS.mul_left C) hlim hbound
  rw [tsum_mul_right] at hlim'
  apply (hasNaturalDensity_iff_tendsto_div _ _).mpr (hlim'.congr' ?_)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
  rw [countUpTo_iUnion J hJ A hdis hX,← tsum_div_const]

/-- The version indexed directly by a set of ideals. -/
theorem hasNaturalDensity_disjointProducts {S : Set (Ideal (𝓞 K))⁰} (A : S → Set (Ideal (𝓞 K))⁰)
    {d : S → ℝ} (hA : ∀ j, HasNaturalDensity (A j) (d j))
    (hdis : Pairwise fun i j : S ↦ Disjoint ((i.val * ·) '' A i) ((j.val * ·) '' A j))
    (hS : Summable fun j : S ↦ (absNorm j.val.val : ℝ)⁻¹) :
    HasNaturalDensity (⋃ j : S, (j.val * ·) '' A j) (∑' j : S, d j / absNorm j.val.val) :=
  hasNaturalDensity_disjointMulImages Subtype.val Subtype.val_injective A hA hdis hS

end GRHArticle.ProgressionFree.NumberFieldIdeals
