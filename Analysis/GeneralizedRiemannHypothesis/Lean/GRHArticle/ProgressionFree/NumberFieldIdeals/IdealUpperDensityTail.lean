import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughParts
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothOptimization

/-!
# Tail bounds for smooth-rough ideal counts

Large smooth factors have the density of a product with a fixed smooth
reciprocal tail. Small smooth factors paired with small rough factors
fit in a dilated full ideal norm ball.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- Smooth ideals beyond the integral norm cutoff. -/
def idealSmoothNormTail (S : Finset (HeightOneSpectrum (𝓞 K))) (L : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {J | J ∈ Set.range (smoothMultiplier S) ∧ L < absNorm J.val}

/-- The reciprocal norm of the smooth tail tends to zero. -/
theorem tendsto_idealSmoothNormTail_weight_zero (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun L : ℕ ↦ idealReciprocalWeight (K := K) (idealSmoothNormTail S L)) atTop (𝓝 0) := by
  classical
  let B := Set.range (smoothMultiplier S)
  let f (I : B) : ℝ := (absNorm I.val.val : ℝ)⁻¹
  let C (L : ℕ) : Set B := {J | absNorm J.val.val ≤ L}
  have hc (L : ℕ) : (C L).Finite :=
    (finite_setOf_absNorm_le₀ (S := 𝓞 K) L).preimage (f := fun J : B ↦ J.val) Subtype.val_injective.injOn
  let F (L : ℕ) : Finset B := (hc L).toFinset
  have hmem (L : ℕ) (J : B) : J ∈ F L ↔ absNorm J.val.val ≤ L := (hc L).mem_toFinset
  have hF : Tendsto F atTop atTop := by
    apply tendsto_atTop.mpr
    intro T
    refine eventually_atTop.mpr ⟨T.sup (fun J ↦ absNorm J.val.val), ?_⟩
    intro L hL J hJ
    exact (hmem L J).mpr ((Finset.le_sup (f := fun J : B ↦ absNorm J.val.val) hJ).trans hL)
  have hcomp : Tendsto (fun T : Finset B ↦ ∑' J : ↥((↑T : Set B)ᶜ), f J.val) atTop (𝓝 0) :=
    tendsto_tsum_compl_atTop_zero f
  have hlim := hcomp.comp hF
  apply hlim.congr
  intro L
  let E : ↥((↑(F L) : Set B)ᶜ) ≃ idealSmoothNormTail S L :=
    { toFun := fun J ↦ ⟨J.val.val,J.val.property, not_le.mp (fun h ↦ J.property ((hmem L J.val).mpr h))⟩
      invFun := fun J ↦ ⟨⟨J.val,J.property.1⟩,fun h ↦ J.property.2.not_ge ((hmem L ⟨J.val,J.property.1⟩).mp h)⟩
      left_inv := by intro J; exact Subtype.ext (Subtype.ext rfl)
      right_inv := by intro J; exact Subtype.ext rfl }
  exact E.tsum_eq (fun J : idealSmoothNormTail S L ↦ (absNorm J.val.val : ℝ)⁻¹)

/-- The ideals whose smooth part has norm above `L`. -/
def idealLargeSmoothPart (S : Finset (HeightOneSpectrum (𝓞 K))) (L : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {I | L < absNorm (idealSmoothPart S I).val}

theorem hasNaturalDensity_idealLargeSmoothPart (S : Finset (HeightOneSpectrum (𝓞 K))) (L : ℕ) :
    HasNaturalDensity (idealLargeSmoothPart S L)
      (idealSmoothDensityFactor S * idealReciprocalWeight (K := K) (idealSmoothNormTail S L)) := by
  let F := idealSmoothNormTail S L
  have hF : F ⊆ Set.range (smoothMultiplier S) := fun _ h ↦ h.1
  have hEq : idealLargeSmoothPart S L = ⋃ J : F, (J.val * ·) '' roughIdeals S := by
    ext I
    constructor
    · intro hI
      apply Set.mem_iUnion.mpr
      refine ⟨⟨idealSmoothPart S I,idealSmoothPart_mem S I,hI⟩, idealRoughPart S I, idealRoughPart_mem S I, ?_⟩
      exact (mul_comm _ _).trans (idealRoughPart_mul_smoothPart S I)
    · intro hI
      obtain ⟨J,g,hg,rfl⟩ := Set.mem_iUnion.mp hI
      change L < absNorm (idealSmoothPart S (J.val*g)).val
      rw [mul_comm, idealSmoothPart_mul_of_parts S hg (hF J.property)]
      exact J.property.2
  have hdis : Pairwise fun J H : F ↦
      Disjoint ((J.val * ·) '' roughIdeals S) ((H.val * ·) '' roughIdeals S) := by
    intro J H hne
    apply Set.disjoint_left.mpr
    rintro I ⟨g,hg,heg⟩ ⟨h,hh,heh⟩
    change J.val*g = I at heg
    change H.val*h = I at heh
    have he : g*J.val = h*H.val := (mul_comm _ _).trans (heg.trans (heh.symm.trans (mul_comm _ _)))
    exact hne (Subtype.ext (eq_of_rough_mul_smooth_eq S hg hh (hF J.property) (hF H.property) he).2)
  have h := hasNaturalDensity_disjointProducts (fun _ : F ↦ roughIdeals S)
    (fun _ ↦ hasNaturalDensity_roughIdeals S) hdis (summable_reciprocal_smoothIdealSubset (K := K) hF)
  rw [hEq]
  simpa only [idealSmoothDensityFactor, primeWeight, idealReciprocalWeight, ← tsum_mul_left, div_eq_mul_inv] using h

/-- A full ball dilated by a constant has the reciprocal limiting density. -/
theorem tendsto_countUpTo_univ_scaled_ratio {a : ℝ} (ha : 0 < a) :
    Tendsto (fun X : ℝ ↦ (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) (X/a) : ℝ) /
      countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X) atTop (𝓝 (1/a)) := by
  let r := dedekindZeta_residue K
  have hr : 0 < r := dedekindZeta_residue_pos K
  have hs := tendsto_countUpTo_univ_div (K := K)
  have hu : Tendsto (fun X : ℝ ↦ (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) (X/a) : ℝ)/X)
      atTop (𝓝 (r/a)) := by
    apply ((hs.comp (tendsto_id.atTop_div_const ha)).div_const a).congr
    intro X
    change (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) (X/a) : ℝ)/(X/a)/a = _
    rw [div_div, div_mul_cancel₀ X ha.ne']
  have h := hu.div hs hr.ne'
  have he : r/a/r = 1/a := by field_simp [hr.ne',ha.ne']
  change Tendsto _ atTop (𝓝 (r/a/r)) at h
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  exact div_div_div_cancel_right₀ hX.ne' _ _

end GRHArticle.ProgressionFree.NumberFieldIdeals
