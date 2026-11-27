import GRHArticle.ProgressionFree.NumberFieldIdeals.InfiniteLocalRules

/-!
# The number-field product-set density formula

Give the smooth set as a set of actual nonzero integral ideals. Its
reciprocal norm mass multiplies the finite roughness factor and the
positive convergent product of all the exterior local probabilities.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors Classical

variable {K : Type*} [Field K] [NumberField K]

/-- The rough ideals satisfying the prescribed rules outside the smooth primes. -/
def idealRoughLocalRule (S : Finset (HeightOneSpectrum (𝓞 K))) (A : HeightOneSpectrum (𝓞 K) → Set ℕ) :
    Set (Ideal (𝓞 K))⁰ :=
  {I | I ∈ roughIdeals S ∧ ∀ p ∉ S, primeExponent p I ∈ A p}

private theorem localRuleMass_zero (p : HeightOneSpectrum (𝓞 K)) :
    localRuleMass p {0} = 1-primeWeight p := by
  rw [localRuleMass, ← _root_.tsum_subtype ({0} : Set ℕ) (fun k ↦ primeWeight p^k)]
  simp

/-- The exterior Euler product exists and is strictly positive. -/
theorem exteriorRuleProduct_pos (S : Finset (HeightOneSpectrum (𝓞 K))) (A : HeightOneSpectrum (𝓞 K) → Set ℕ)
    (hA : ∀ p ∉ S, 0 ∈ A p ∧ 1 ∈ A p) :
    Multipliable (fun p : {p // p ∉ S} ↦ localRuleMass p.val (A p.val)) ∧
      0 < ∏' p : {p // p ∉ S}, localRuleMass p.val (A p.val) :=
  localRuleEulerProductOn Subtype.val Subtype.val_injective ∅ (fun p : {p // p ∉ S} ↦ A p.val)
    (fun p ↦ (hA p.val p.property).1) (fun p _ ↦ (hA p.val p.property).2)

theorem hasNaturalDensity_idealRoughLocalRule (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : HeightOneSpectrum (𝓞 K) → Set ℕ) (hA : ∀ p ∉ S, 0 ∈ A p ∧ 1 ∈ A p) :
    HasNaturalDensity (idealRoughLocalRule S A)
      ((∏ p ∈ S, (1-primeWeight p)) * ∏' p : {p // p ∉ S}, localRuleMass p.val (A p.val)) := by
  let B (p : HeightOneSpectrum (𝓞 K)) : Set ℕ := if p ∈ S then {0} else A p
  have h0 p : 0 ∈ B p := by
    by_cases hp : p ∈ S
    · simp [B,hp]
    · simpa [B,hp] using (hA p hp).1
  have h1 p (hp : p ∉ S) : 1 ∈ B p := by simpa [B,hp] using (hA p hp).2
  have he : idealRoughLocalRule S A = infiniteLocalRule B := by
    ext I
    have hzero (p) : primeExponent p I = 0 ↔ ¬ primeIdeal p ∣ I := by
      rw [primeExponent_eq_iff,nonZeroDivisors_dvd_iff_dvd_coe]
      simp [primeIdeal]
    constructor
    · intro h p
      by_cases hp : p ∈ S
      · simpa [B,hp] using (hzero p).mpr (h.1 p hp)
      · simpa [B,hp] using h.2 p hp
    · intro h
      refine ⟨fun p hp ↦ (hzero p).mp ?_,fun p hp ↦ ?_⟩
      · simpa [B,hp] using h p
      · simpa [B,hp] using h p
  let f (p : HeightOneSpectrum (𝓞 K)) := localRuleMass p (B p)
  have hfo (p : {p // p ∉ S}) : f p.val = localRuleMass p.val (A p.val) := by simp [f,B,p.property]
  have ho : Multipliable (fun p : {p // p ∉ S} ↦ f p.val) :=
    (exteriorRuleProduct_pos S A hA).1.congr fun p ↦ (hfo p).symm
  have hi : Multipliable (fun p : (S : Set _) ↦ f p.val) := (hasProd_fintype _).multipliable
  have hf := Multipliable.tprod_mul_tprod_compl (f := f) (s := (S : Set _)) hi ho
  change (∏' p : ↥S, f p.val) * (∏' p : {p // p ∉ S}, f p.val) = ∏' p, f p at hf
  rw [Finset.tprod_subtype S f] at hf
  have hin : (∏ p ∈ S, f p) = ∏ p ∈ S, (1-primeWeight p) := prod_congr rfl (fun p hp ↦ by
    simp only [f,B,if_pos hp,localRuleMass_zero])
  rw [hin] at hf
  rw [he]
  convert hasNaturalDensity_infiniteLocalRule S B h0 h1 using 1
  have hout : (∏' p : {p // p ∉ S}, f p.val) = ∏' p : {p // p ∉ S}, localRuleMass p.val (A p.val) :=
    tprod_congr hfo
  rw [← hout]
  exact hf

/-- The exact density in article equation `gpi:eq:product` for arbitrary
sets of smooth ideals and arbitrary allowed exterior exponents. -/
theorem idealProductSet_density (S : Finset (HeightOneSpectrum (𝓞 K)))
    (F : Set (Ideal (𝓞 K))⁰) (hF : F ⊆ Set.range (smoothMultiplier S))
    (A : HeightOneSpectrum (𝓞 K) → Set ℕ) (hA : ∀ p ∉ S, 0 ∈ A p ∧ 1 ∈ A p) :
    HasNaturalDensity (⋃ J : F, (J.val * ·) '' idealRoughLocalRule S A)
      ((∏ p ∈ S, (1-primeWeight p)) * (∑' J : F, (absNorm J.val.val : ℝ)⁻¹) *
        ∏' p : {p // p ∉ S}, localRuleMass p.val (A p.val)) := by
  let T : Set (S → ℕ) := {e | smoothMultiplier S e ∈ F}
  let φ (e : T) : F := ⟨smoothMultiplier S e.val,e.property⟩
  have hb : Function.Bijective φ := by
    refine ⟨fun i j h ↦ Subtype.ext (smoothMultiplier_injective S (congrArg Subtype.val h)),?_⟩
    intro J
    obtain ⟨e,he⟩ := hF J.property
    exact ⟨⟨e, show smoothMultiplier S e ∈ F from he.symm ▸ J.property⟩,Subtype.ext he⟩
  let E := Equiv.ofBijective φ hb
  have hunion : (⋃ J : F, (J.val * ·) '' idealRoughLocalRule S A) =
      ⋃ e : T, (smoothMultiplier S e.val * ·) '' idealRoughLocalRule S A := by
    ext I
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨J,hJ⟩ ↦ by obtain ⟨e,rfl⟩ := hb.surjective J; exact ⟨e,hJ⟩,
      fun ⟨e,he⟩ ↦ ⟨φ e,he⟩⟩
  have hw := E.tsum_eq (fun J : F ↦ (absNorm J.val.val : ℝ)⁻¹)
  change (∑' e : T, (absNorm (smoothMultiplier S e.val).val : ℝ)⁻¹) = _ at hw
  rw [hunion, ← hw, mul_right_comm]
  exact hasNaturalDensity_smoothTemplateProducts S T (fun _ h ↦ h.1)
    (hasNaturalDensity_idealRoughLocalRule S A hA)

end GRHArticle.ProgressionFree.NumberFieldIdeals
