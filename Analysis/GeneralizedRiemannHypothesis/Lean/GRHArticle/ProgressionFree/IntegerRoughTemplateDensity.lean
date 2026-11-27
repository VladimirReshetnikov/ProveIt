import GRHArticle.ProgressionFree.IntegerSquarefreeRoughDensity
import GRHArticle.ProgressionFree.IntegerSmoothNaturalBound
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Natural density of a fixed smooth template on rough factors

A positive integer in the construction factors uniquely as a rough part
times a smooth template element. The density of each dilation is its rough
density divided by the smooth factor. Summability of the reciprocals of the
smooth numbers justifies summing the limits for an infinite template.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- Products of an allowed rough part with a member of a fixed smooth template. -/
def integerRoughTemplateProducts (Q S : Set ℕ) : Set ℕ :=
  {n | ∃ r s : ℕ, r ∈ Q ∧ s ∈ S ∧ n = r*s}

private theorem densityUpTo_roughTemplateProducts {Q S : Set ℕ} {Y : ℕ}
    (hQ : Q ⊆ integerRoughNumbers Y) (hS : S ⊆ Nat.smoothNumbers (Y+1)) (N : ℕ) :
    densityUpTo (integerRoughTemplateProducts Q S) N =
      ∑' s : S, (countUpTo Q (N/s.val) : ℝ) / N := by
  let F : Finset S := (integerPrefixSlice S N).preimage Subtype.val Subtype.val_injective.injOn
  let D := F.sigma (fun s ↦ integerPrefixSlice Q (N / s.val))
  have hF (s : S) : s ∈ F ↔ s.val ≤ N := by
    have hp := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hS s.property))
    simp only [F, mem_preimage, integerPrefixSlice, mem_filter, integerPrefix, mem_Icc]
    exact ⟨fun h ↦ h.1.2,fun h ↦ ⟨⟨hp,h⟩,s.property⟩⟩
  have hcount : D.card = countUpTo (integerRoughTemplateProducts Q S) N := by
    unfold countUpTo
    apply card_bij (fun z _ ↦ z.2 * z.1.val)
    · rintro ⟨s,r⟩ hz
      obtain ⟨hs,hr⟩ := mem_sigma.mp hz
      obtain ⟨hi,hrQ⟩ := mem_filter.mp hr
      have hsp := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hS s.property))
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hi).1 hsp,
        (Nat.le_div_iff_mul_le hsp).mp (mem_Icc.mp hi).2⟩,r,s,hrQ,s.property,rfl⟩
    · rintro ⟨s,r⟩ hz ⟨s',r'⟩ hz' he
      have hrQ := (mem_filter.mp (mem_sigma.mp hz).2).2
      have hrQ' := (mem_filter.mp (mem_sigma.mp hz').2).2
      change r*s.val = r'*s'.val at he
      have heS := congrArg (integerSmoothPart Y) he
      rw [integerSmoothPart_mul_of_parts (hQ hrQ) (hS s.property),
        integerSmoothPart_mul_of_parts (hQ hrQ') (hS s'.property)] at heS
      obtain rfl : s = s' := Subtype.ext heS
      obtain rfl : r = r' := Nat.mul_right_cancel
        (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hS s.property))) he
      rfl
    · intro n hn
      obtain ⟨hi,r,s,hr,hs,rfl⟩ := mem_filter.mp hn
      have hr₀ := Nat.pos_of_ne_zero (hQ hr).1
      have hs₀ := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hS hs))
      have hNs := (Nat.le_mul_of_pos_left s hr₀).trans (mem_Icc.mp hi).2
      refine ⟨⟨⟨s,hs⟩,r⟩, mem_sigma.mpr ⟨(hF _).mpr hNs, mem_filter.mpr ⟨?_,hr⟩⟩,rfl⟩
      exact mem_Icc.mpr ⟨hr₀, (Nat.le_div_iff_mul_le hs₀).mpr (mem_Icc.mp hi).2⟩
  rw [densityUpTo, ← hcount, show D.card = ∑ s ∈ F, countUpTo Q (N/s.val) from card_sigma _ _,
    Nat.cast_sum, sum_div]
  symm
  apply tsum_eq_sum
  intro s hs
  have hlt : N < s.val := lt_of_not_ge (fun h ↦ hs ((hF s).mpr h))
  simp [Nat.div_eq_of_lt hlt, countUpTo]

/-- Every fixed smooth template has its predicted density on a chosen set of rough parts. -/
theorem hasNaturalDensity_integerRoughTemplateProducts {Q S : Set ℕ} {Y : ℕ} {d : ℝ}
    (hQ : Q ⊆ integerRoughNumbers Y) (hS : S ⊆ Nat.smoothNumbers (Y+1))
    (hd : HasNaturalDensity Q d) :
    HasNaturalDensity (integerRoughTemplateProducts Q S) (d * ∑' s : S, (s.val : ℝ)⁻¹) := by
  let f (N : ℕ) (s : S) : ℝ := (countUpTo Q (N/s.val) : ℝ) / N
  have hlim (s : S) : Tendsto (f · s) atTop (𝓝 (d * (s.val : ℝ)⁻¹)) := by
    rw [← div_eq_mul_inv]
    exact tendsto_countUpTo_div_cutoff hd
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hS s.property)))
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ s : S, ‖f N s‖ ≤ (s.val : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    intro s
    have hs := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hS s.property))
    have h := (Nat.mul_le_mul_right s.val (countUpTo_le_cutoff Q (N/s.val))).trans (Nat.div_mul_le_self N s.val)
    dsimp only [f]
    rw [Real.norm_of_nonneg (by positivity), ← one_div]
    apply (div_le_div_iff₀ (by exact_mod_cast hN) (by exact_mod_cast hs)).mpr
    rw [one_mul]
    exact_mod_cast h
  have hlim' := tendsto_tsum_of_dominated_convergence (smoothSubset_reciprocal_summable hS) hlim hbound
  rw [tsum_mul_left] at hlim'
  exact hlim'.congr (fun N ↦ (densityUpTo_roughTemplateProducts hQ hS N).symm)

end GRHArticle.ProgressionFree
