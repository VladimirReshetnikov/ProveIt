import GRHArticle.ProgressionFree.PolynomialDeficitSet
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Progression exclusion for polynomial rough-factor replacements
-/

namespace GRHArticle.ProgressionFree

open UniqueFactorizationMonoid

noncomputable local instance {F : Type*} [Field F] : DecidableEq F := Classical.decEq F

/-- The normalized irreducible factors of degree greater than the smoothness cutoff. -/
noncomputable def polynomialRoughFactors {F : Type*} [Field F] (L : ℕ)
    (f : Polynomial F) : Multiset (Polynomial F) :=
  (normalizedFactors f).filter fun p ↦ L < p.natDegree

private theorem polynomialRoughFactors_mul {F : Type*} [Field F] (L : ℕ)
    {f g : Polynomial F} (hf : f ≠ 0) (hg : g ≠ 0) :
    polynomialRoughFactors L (f * g) =
      polynomialRoughFactors L f + polynomialRoughFactors L g := by
  simp only [polynomialRoughFactors, normalizedFactors_mul hf hg, Multiset.filter_add]

private theorem polynomialRoughFactors_eq_zero_of_natDegree_le {F : Type*} [Field F]
    {L : ℕ} {f : Polynomial F} (hf : f ≠ 0) (hdeg : f.natDegree ≤ L) :
    polynomialRoughFactors L f = 0 := by
  apply Multiset.filter_eq_nil.mpr
  intro p hp
  exact not_lt_of_ge ((Polynomial.natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hp) hf).trans hdeg)

/-- Select a new deficit rule for each marked rough factor multiset. -/
noncomputable def polynomialRoughReplacementSet {F : Type*} [Field F] (L N : ℕ)
    (A D : Set ℕ) (marked : Multiset (Polynomial F) → Prop) : Set (Polynomial F) :=
  {f | f ≠ 0 ∧ f.natDegree ≤ N ∧
    (marked (polynomialRoughFactors L f) → N - f.natDegree ∈ D) ∧
    (¬ marked (polynomialRoughFactors L f) → N - f.natDegree ∈ A)}

/-- Replacing the deficit rule on whole squarefree rough classes preserves freedom
from progressions of polynomial ratio of positive degree. -/
theorem polynomialRoughReplacementSet_no_ratio_progression {F : Type*} [Field F]
    {L : ℕ} (N : ℕ) {A D : Set ℕ} (hA : ThreeAPFree A) (hD : ThreeAPFree D)
    (hnew : ∀ d ∈ D, d ∉ A → d ≤ L) {marked : Multiset (Polynomial F) → Prop}
    (hsquarefree : ∀ w, marked w → w.Nodup) {f r : Polynomial F}
    (hr : 0 < r.natDegree) :
    ¬ (f ∈ polynomialRoughReplacementSet L N A D marked ∧
      f * r ∈ polynomialRoughReplacementSet L N A D marked ∧
      f * r * r ∈ polynomialRoughReplacementSet L N A D marked) := by
  rintro ⟨⟨hf, hfN, hfD, hfA⟩, ⟨hfr, hfrN, hfrD, hfrA⟩, ⟨hfrr, hfrrN, hfrrD, hfrrA⟩⟩
  have hr₀ : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hdeg₁ := Polynomial.natDegree_mul hf hr₀
  have hdeg₂ := Polynomial.natDegree_mul hfr hr₀
  have hR₁ := polynomialRoughFactors_mul L hf hr₀
  have hR₂ := polynomialRoughFactors_mul L hfr hr₀
  have hmark (g : Polynomial F)
      (hDg : marked (polynomialRoughFactors L g) → N - g.natDegree ∈ D)
      (hAg : ¬ marked (polynomialRoughFactors L g) → N - g.natDegree ∈ A)
      (hn : N - g.natDegree ∉ A) :
      marked (polynomialRoughFactors L g) ∧ N - g.natDegree ≤ L := by
    have hm : marked (polynomialRoughFactors L g) := by
      by_contra h
      exact hn (hAg h)
    exact ⟨hm, hnew _ (hDg hm) hn⟩
  have hmarked : (marked (polynomialRoughFactors L f) ∧ N - f.natDegree ≤ L) ∨
      (marked (polynomialRoughFactors L (f * r)) ∧ N - (f * r).natDegree ≤ L) ∨
      marked (polynomialRoughFactors L (f * r * r)) := by
    by_cases h₁ : N - f.natDegree ∈ A
    · by_cases h₂ : N - (f * r).natDegree ∈ A
      · by_cases h₃ : N - (f * r * r).natDegree ∈ A
        · exact False.elim (polynomialDeficitSet_no_ratio_progression hA N hr
            ⟨⟨hf, hfN, h₁⟩, ⟨hfr, hfrN, h₂⟩, ⟨hfrr, hfrrN, h₃⟩⟩)
        · exact Or.inr (Or.inr (hmark _ hfrrD hfrrA h₃).1)
      · exact Or.inr (Or.inl (hmark _ hfrD hfrA h₂))
    · exact Or.inl (hmark _ hfD hfA h₁)
  have hrR : polynomialRoughFactors L r = 0 := by
    rcases hmarked with ⟨_, hl⟩ | ⟨_, hl⟩ | hm
    · exact polynomialRoughFactors_eq_zero_of_natDegree_le hr₀ (by omega)
    · exact polynomialRoughFactors_eq_zero_of_natDegree_le hr₀ (by omega)
    · have hnodup := hsquarefree _ hm
      rw [hR₂, hR₁, add_assoc] at hnodup
      have hself := (Multiset.nodup_add.mp (Multiset.nodup_add.mp hnodup).2.1).2.2
      simpa using hself
  rw [hrR, add_zero] at hR₁ hR₂
  have hm : marked (polynomialRoughFactors L f) := by
    rcases hmarked with ⟨hm, _⟩ | ⟨hm, _⟩ | hm
    · exact hm
    · rwa [hR₁] at hm
    · rwa [hR₂, hR₁] at hm
  have hmfr := hR₁.symm ▸ hm
  have hmfrr := hR₂.symm ▸ hmfr
  exact polynomialDeficitSet_no_ratio_progression hD N hr
    ⟨⟨hf, hfN, hfD hm⟩, ⟨hfr, hfrN, hfrD hmfr⟩, ⟨hfrr, hfrrN, hfrrD hmfrr⟩⟩

/-- The concrete finite replacement using degree-480 smoothness and all squarefree
rough classes of total factor degree `N - R`. -/
noncomputable def polynomialDeficitReplacement {F : Type*} [Field F] (N R : ℕ) :
    Set (Polynomial F) :=
  polynomialRoughReplacementSet 480 N greedyExponents (polynomialDeficitWitness : Set ℕ)
    (fun w ↦ w.Nodup ∧ (w.map Polynomial.natDegree).sum = N - R)

/-- The article's explicit finite replacement is progression-free at every cutoff. -/
theorem polynomialDeficitReplacement_no_ratio_progression {F : Type*} [Field F]
    (N R : ℕ) {f r : Polynomial F} (hr : 0 < r.natDegree) :
    ¬ (f ∈ polynomialDeficitReplacement N R ∧ f * r ∈ polynomialDeficitReplacement N R ∧
      f * r * r ∈ polynomialDeficitReplacement N R) :=
  polynomialRoughReplacementSet_no_ratio_progression N threeAPFree_greedyExponents
    threeAPFree_polynomialDeficitWitness
    (fun d hd _ ↦ polynomialDeficitWitness_max_le d hd) (fun _ hm ↦ hm.1) hr

end GRHArticle.ProgressionFree
