import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughFibers
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughBands
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealPurePowerExchange

/-!
# Pasting the ideal optimizers along disjoint rough bands

For a fixed finite number of budgets, use geometric cutoff growth so the
rough bands from different stages never meet. Each retained rough factor
then receives only one template in the resulting global admissible set.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter
open scoped nonZeroDivisors BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- The geometric cutoffs used for disjoint stage bands. -/
noncomputable def idealRoughPastingCutoff (M j : ℕ) : ℝ := ((M : ℝ)+2)^j

theorem tendsto_idealRoughPastingCutoff (M : ℕ) : Tendsto (idealRoughPastingCutoff M) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by linarith [Nat.cast_nonneg (α := ℝ) M] : 1 < (M : ℝ)+2)

private theorem idealRoughPastingCutoff_pos (M j : ℕ) : 0 < idealRoughPastingCutoff M j := by
  unfold idealRoughPastingCutoff
  positivity

private theorem stage_intervals_disjoint {Q : Set (Ideal (𝓞 K))⁰} {g : (Ideal (𝓞 K))⁰}
    {M j j' k k' : ℕ} (hjj' : j < j') (hk : 0 < k) (hk'M : k' ≤ M)
    (h : g ∈ idealRoughBudgetBand Q (idealRoughPastingCutoff M j) k)
    (h' : g ∈ idealRoughBudgetBand Q (idealRoughPastingCutoff M j') k') : False := by
  have hu : (absNorm g.val : ℝ) ≤ idealRoughPastingCutoff M j := h.2.2.trans (by
    apply div_le_self (idealRoughPastingCutoff_pos M j).le
    exact_mod_cast hk)
  have hl : idealRoughPastingCutoff M j ≤ idealRoughPastingCutoff M j' / ((k' : ℝ)+1) := by
    apply (le_div_iff₀ (by positivity : 0 < (k' : ℝ)+1)).mpr
    have hcast : (k' : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk'M
    calc
      _ ≤ idealRoughPastingCutoff M j * ((M : ℝ)+2) :=
        mul_le_mul_of_nonneg_left (by linarith) (idealRoughPastingCutoff_pos M j).le
      _ = idealRoughPastingCutoff M (j+1) := (pow_succ _ _).symm
      _ ≤ idealRoughPastingCutoff M j' :=
        pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) M] : 1 ≤ (M : ℝ)+2) hjj'
  exact h'.2.1.not_ge (hu.trans hl)

private theorem fixed_stage_intervals_disjoint {Q : Set (Ideal (𝓞 K))⁰} {g : (Ideal (𝓞 K))⁰}
    {X : ℝ} (hX : 0 ≤ X) {k k' : ℕ} (hkk' : k < k')
    (h : g ∈ idealRoughBudgetBand Q X k) (h' : g ∈ idealRoughBudgetBand Q X k') : False := by
  have hle : (k : ℝ)+1 ≤ (k' : ℝ) := by exact_mod_cast hkk'
  exact h.2.1.not_ge (h'.2.2.trans (div_le_div_of_nonneg_left hX (by positivity) hle))

/-- The stage and the budget of a retained rough factor are unique. -/
theorem idealRoughPastingBand_unique {Q : Set (Ideal (𝓞 K))⁰} {g : (Ideal (𝓞 K))⁰}
    {M j j' k k' : ℕ} (hk : 0 < k) (hkM : k ≤ M) (hk' : 0 < k') (hk'M : k' ≤ M)
    (h : g ∈ idealRoughBudgetBand Q (idealRoughPastingCutoff M j) k)
    (h' : g ∈ idealRoughBudgetBand Q (idealRoughPastingCutoff M j') k') : j = j' ∧ k = k' := by
  have hj : j = j' := le_antisymm
    (le_of_not_gt (fun hlt ↦ stage_intervals_disjoint hlt hk' hkM h' h))
    (le_of_not_gt (fun hlt ↦ stage_intervals_disjoint hlt hk hk'M h h'))
  subst j'
  refine ⟨rfl,le_antisymm ?_ ?_⟩
  · exact le_of_not_gt (fun hlt ↦ fixed_stage_intervals_disjoint (idealRoughPastingCutoff_pos M j).le hlt h' h)
  · exact le_of_not_gt (fun hlt ↦ fixed_stage_intervals_disjoint (idealRoughPastingCutoff_pos M j).le hlt h h')

/-- Assign each retained rough factor its prescribed smooth template. -/
def idealRoughPastedTemplate (M : ℕ) (Q : Set (Ideal (𝓞 K))⁰)
    (F : ℕ → Set (Ideal (𝓞 K))⁰) (g : (Ideal (𝓞 K))⁰) : Set (Ideal (𝓞 K))⁰ :=
  {J | ∃ j k : ℕ, 0 < k ∧ k ≤ M ∧ g ∈ idealRoughBudgetBand Q (idealRoughPastingCutoff M j) k ∧ J ∈ F k}

/-- The single globally pasted set used to realize all stages. -/
def idealRoughPastedSet (M : ℕ) (Q : Set (Ideal (𝓞 K))⁰)
    (F : ℕ → Set (Ideal (𝓞 K))⁰) : Set (Ideal (𝓞 K))⁰ :=
  roughFiberUnion (K := K) Q (idealRoughPastedTemplate (K := K) M Q F)

theorem idealAdmissible_idealRoughPastedSet (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) {Q : Set (Ideal (𝓞 K))⁰}
    (hQ : Q ⊆ roughIdeals S) (hQsf : ∀ g ∈ Q, ∀ p ∉ S, primeExponent p g ≤ 1)
    (F : ℕ → Set (Ideal (𝓞 K))⁰) (hF : ∀ k, F k ⊆ Set.range (smoothMultiplier S))
    (hFf : ∀ k, IdealAdmissible integral (F k)) :
    IdealAdmissible integral (idealRoughPastedSet (K := K) M Q F) := by
  apply idealAdmissible_roughFiberUnion integral S hQ hQsf
  · rintro g _ J ⟨_,k,_,_,_,hJ⟩
    exact hF k hJ
  · rintro g _ a b c ⟨ja,ka,hka,haM,haB,ha⟩ ⟨jb,kb,hkb,hbM,hbB,hb⟩ ⟨jc,kc,hkc,hcM,hcB,hc⟩
    have hkab := (idealRoughPastingBand_unique hka haM hkb hbM haB hbB).2
    have hkac := (idealRoughPastingBand_unique hka haM hkc hcM haB hcB).2
    subst kb
    subst kc
    exact hFf ka ha hb hc

/-- At each stage the pasted set contains all copies of each of the finite
smooth optimizers in its designated rough budget band. -/
theorem countUpTo_idealRoughPastedSet_ge (S : Finset (HeightOneSpectrum (𝓞 K)))
    (M j : ℕ) {Q : Set (Ideal (𝓞 K))⁰} (hQ : Q ⊆ roughIdeals S)
    (F : ℕ → Finset (Ideal (𝓞 K))⁰)
    (hF : ∀ k, (F k : Set (Ideal (𝓞 K))⁰) ⊆ idealNormCutoff (Set.range (smoothMultiplier S)) k) :
    (∑ k ∈ Icc 1 M, (idealRoughBudgetBand Q (idealRoughPastingCutoff M j) k).ncard * (F k).card) ≤
      countUpTo (idealRoughPastedSet (K := K) M Q (fun k ↦ (F k : Set (Ideal (𝓞 K))⁰)))
        (idealRoughPastingCutoff M j) := by
  classical
  let X := idealRoughPastingCutoff M j
  let E := idealRoughPastedSet (K := K) M Q (fun k ↦ (F k : Set (Ideal (𝓞 K))⁰))
  let band (k : ℕ) := (idealRoughBudgetBand_finite Q X k).toFinset
  let D := (Icc 1 M).sigma fun k ↦ band k ×ˢ F k
  let product (z : Σ _ : ℕ, (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) := z.2.1 * z.2.2
  have hcard : D.card ≤ countUpTo E X := by
    change D.card ≤ (idealRealNormCutoff E X).ncard
    rw [Set.ncard_eq_toFinset_card _ (idealRealNormCutoff_finite E X)]
    apply Finset.card_le_card_of_injOn product
    · rintro ⟨k,g,J⟩ hz
      obtain ⟨hk,hz⟩ := Finset.mem_sigma.mp hz
      obtain ⟨hg,hJ⟩ := Finset.mem_product.mp hz
      obtain ⟨hkp,hkM⟩ := Finset.mem_Icc.mp hk
      have hgB : g ∈ idealRoughBudgetBand Q X k := (idealRoughBudgetBand_finite Q X k).mem_toFinset.mp hg
      apply (idealRealNormCutoff_finite E X).mem_toFinset.mpr
      change g*J ∈ E ∧ (absNorm (g*J).val : ℝ) ≤ X
      refine ⟨Set.mem_iUnion.mpr ⟨⟨g,hgB.1⟩, J, ⟨j,k,hkp,hkM,hgB,hJ⟩,rfl⟩, ?_⟩
      have hkp' : 0 < (k : ℝ) := by exact_mod_cast hkp
      have hJk : (absNorm J.val : ℝ) ≤ (k : ℝ) := by exact_mod_cast (hF k hJ).2
      rw [Submonoid.coe_mul, map_mul, Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left hJk (Nat.cast_nonneg _)).trans ((le_div_iff₀ hkp').mp hgB.2.2)
    · rintro ⟨k,g,J⟩ hz ⟨k',g',J'⟩ hz' he
      obtain ⟨hk,hz⟩ := Finset.mem_sigma.mp hz
      obtain ⟨hk',hz'⟩ := Finset.mem_sigma.mp hz'
      obtain ⟨hg,hJ⟩ := Finset.mem_product.mp hz
      obtain ⟨hg',hJ'⟩ := Finset.mem_product.mp hz'
      obtain ⟨hkp,hkM⟩ := Finset.mem_Icc.mp hk
      obtain ⟨hkp',hkM'⟩ := Finset.mem_Icc.mp hk'
      have hgB := (idealRoughBudgetBand_finite Q X k).mem_toFinset.mp hg
      have hgB' := (idealRoughBudgetBand_finite Q X k').mem_toFinset.mp hg'
      obtain ⟨rfl,rfl⟩ := eq_of_rough_mul_smooth_eq S (hQ hgB.1) (hQ hgB'.1) (hF k hJ).1 (hF k' hJ').1 he
      have hkk' := (idealRoughPastingBand_unique hkp hkM hkp' hkM' hgB hgB').2
      change k = k' at hkk'
      subst k'
      rfl
  have hs : D.card = ∑ k ∈ Icc 1 M, (idealRoughBudgetBand Q X k).ncard * (F k).card := by
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.card_product, Set.ncard_eq_toFinset_card _ (idealRoughBudgetBand_finite Q X k)]
  rwa [hs] at hcard

end GRHArticle.ProgressionFree.NumberFieldIdeals
