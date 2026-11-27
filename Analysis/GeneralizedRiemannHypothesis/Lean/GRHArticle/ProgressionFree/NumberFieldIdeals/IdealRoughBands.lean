import GRHArticle.ProgressionFree.IntegerPrefixTransfer
import GRHArticle.ProgressionFree.NumberFieldIdeals.UniformCounts

/-!
# Norm bands with a fixed smooth budget

At cutoff `X`, the rough budget `k` comes from rough factors with norms in
`(X/(k+1), X/k]`. Natural density determines the asymptotic count in each
of these bands.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The real norm cutoff in a set of nonzero integral ideals. -/
def idealRealNormCutoff (A : Set (Ideal (𝓞 K))⁰) (X : ℝ) : Set (Ideal (𝓞 K))⁰ :=
  {I | I ∈ A ∧ (absNorm I.val : ℝ) ≤ X}

theorem idealRealNormCutoff_finite (A : Set (Ideal (𝓞 K))⁰) (X : ℝ) : (idealRealNormCutoff A X).Finite := by
  obtain ⟨N,hN⟩ := exists_nat_ge X
  exact (finite_setOf_absNorm_le₀ (S := 𝓞 K) N).subset fun I h ↦ Nat.cast_le.mp (h.2.trans hN)

/-- The rough factors from `Q` with exact smooth budget `k` at norm `X`. -/
def idealRoughBudgetBand (Q : Set (Ideal (𝓞 K))⁰) (X : ℝ) (k : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {g | g ∈ Q ∧ X/((k : ℝ)+1) < (absNorm g.val : ℝ) ∧ (absNorm g.val : ℝ) ≤ X/(k : ℝ)}

theorem idealRoughBudgetBand_finite (Q : Set (Ideal (𝓞 K))⁰) (X : ℝ) (k : ℕ) :
    (idealRoughBudgetBand Q X k).Finite :=
  (idealRealNormCutoff_finite Q (X/(k : ℝ))).subset fun _ h ↦ ⟨h.1,h.2.2⟩

theorem idealRoughBudgetBand_ncard_real (Q : Set (Ideal (𝓞 K))⁰) {X : ℝ} (hX : 0 ≤ X)
    {k : ℕ} (hk : 0 < k) :
    ((idealRoughBudgetBand Q X k).ncard : ℝ) =
      (countUpTo Q (X/(k : ℝ)) : ℝ) - (countUpTo Q (X/((k : ℝ)+1)) : ℝ) := by
  let L := idealRealNormCutoff Q (X/((k : ℝ)+1))
  let R := idealRealNormCutoff Q (X/(k : ℝ))
  have hsub : L ⊆ R := by
    intro g hg
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    exact ⟨hg.1,hg.2.trans (div_le_div_of_nonneg_left hX hk' (by linarith))⟩
  have hband : idealRoughBudgetBand Q X k = R \ L := by
    ext g
    change (g ∈ Q ∧ _ ∧ _) ↔ (g ∈ Q ∧ _) ∧ ¬ (g ∈ Q ∧ _)
    simp only [not_and, not_le]
    exact ⟨fun h ↦ ⟨⟨h.1,h.2.2⟩,fun _ ↦ h.2.1⟩, fun h ↦ ⟨h.1.1,h.2 h.1.1,h.1.2⟩⟩
  have hc := Set.ncard_sdiff_add_ncard_of_subset hsub (idealRealNormCutoff_finite Q _)
  rw [hband]
  change ((R \ L).ncard : ℝ) = (R.ncard : ℝ) - (L.ncard : ℝ)
  exact eq_sub_of_add_eq (by exact_mod_cast hc)

private theorem tendsto_scaledCount_div {Q : Set (Ideal (𝓞 K))⁰} {d a : ℝ}
    (hQ : HasNaturalDensity Q d) (ha : 0 < a) :
    Tendsto (fun X : ℝ ↦ (countUpTo Q (X/a) : ℝ)/X) atTop (𝓝 (d * dedekindZeta_residue K / a)) := by
  have h := (((hasNaturalDensity_iff_tendsto_div Q d).mp hQ).comp (tendsto_id.atTop_div_const ha)).div_const a
  apply h.congr
  intro X
  change (countUpTo Q (X/a) : ℝ)/(X/a)/a = _
  rw [div_div, div_mul_cancel₀ X ha.ne']

/-- Each fixed positive rough budget has its predicted limiting normalized
count in the full ideal norm ball. -/
theorem tendsto_idealRoughBudgetBand_ncard_div {Q : Set (Ideal (𝓞 K))⁰}
    {d : ℝ} (hQ : HasNaturalDensity Q d) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun X : ℝ ↦ ((idealRoughBudgetBand Q X k).ncard : ℝ) /
      countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X) atTop (𝓝 (d * integerPrefixStepWeight k)) := by
  let r := dedekindZeta_residue K
  have hr : 0 < r := dedekindZeta_residue_pos K
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hdiff := (tendsto_scaledCount_div hQ hk').sub (tendsto_scaledCount_div hQ (a := (k : ℝ)+1) (by positivity))
  have he : d*r/(k : ℝ) - d*r/((k : ℝ)+1) = (d * integerPrefixStepWeight k)*r := by
    unfold integerPrefixStepWeight
    field_simp [hk'.ne']
    ring
  change Tendsto _ atTop (𝓝 (d*r/(k : ℝ) - d*r/((k : ℝ)+1))) at hdiff
  rw [he] at hdiff
  have hb : Tendsto (fun X : ℝ ↦ ((idealRoughBudgetBand Q X k).ncard : ℝ) / X) atTop
      (𝓝 ((d * integerPrefixStepWeight k)*r)) := by
    apply hdiff.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    rw [idealRoughBudgetBand_ncard_real Q hX hk, sub_div]
  have h := hb.div (tendsto_countUpTo_univ_div (K := K)) hr.ne'
  change Tendsto _ atTop (𝓝 ((d * integerPrefixStepWeight k)*r/r)) at h
  rw [mul_div_cancel_right₀ _ hr.ne'] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  exact div_div_div_cancel_right₀ hX.ne' _ _

end GRHArticle.ProgressionFree.NumberFieldIdeals
