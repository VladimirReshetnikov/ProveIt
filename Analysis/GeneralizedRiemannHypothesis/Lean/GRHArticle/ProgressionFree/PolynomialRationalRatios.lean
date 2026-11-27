import GRHArticle.ProgressionFree.PolynomialBlockAttainment
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Progression-free sets for rational-function ratios

A triple of nonzero polynomials has a common ratio precisely when its
middle square is the endpoint product. The ratio is constant precisely
when the middle polynomial is a scalar multiple of the first. This test
also detects nonconstant rational functions of degree zero.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology

variable {F : Type*} [Field F]

/-- For a geometric triple in the set, only constant rational-function
ratios are allowed. Polynomial representatives need not be monic. -/
def RationalFunctionRatioThreeGPFree (E : Set F[X]) : Prop :=
  ∀ ⦃a b c : F[X]⦄, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ∈ E → b ∈ E → c ∈ E →
    a*c = b*b → ∃ t : F, b = a * C t

theorem rationalFunctionRatioThreeGPFree_iff_ratFunc (E : Set F[X]) :
    RationalFunctionRatioThreeGPFree E ↔
      ∀ ⦃a b c : F[X]⦄ ⦃r : RatFunc F⦄, a ≠ 0 → a ∈ E → b ∈ E → c ∈ E →
        algebraMap F[X] (RatFunc F) b = algebraMap F[X] (RatFunc F) a * r →
        algebraMap F[X] (RatFunc F) c = algebraMap F[X] (RatFunc F) b * r →
        r ∈ Set.range (RatFunc.C (K := F)) := by
  let φ := algebraMap F[X] (RatFunc F)
  have hi : Function.Injective φ := RatFunc.algebraMap_injective F
  constructor
  · intro h a b c r ha ha' hb' hc' hab hbc
    by_cases hr : r = 0
    · exact ⟨0, by simp [hr]⟩
    have hφa : φ a ≠ 0 := fun he ↦ ha (hi (he.trans φ.map_zero.symm))
    change φ b = φ a * r at hab
    change φ c = φ b * r at hbc
    have hφb : φ b ≠ 0 := hab ▸ mul_ne_zero hφa hr
    have hφc : φ c ≠ 0 := hbc ▸ mul_ne_zero hφb hr
    have hb : b ≠ 0 := fun he ↦ hφb (he ▸ φ.map_zero)
    have hc : c ≠ 0 := fun he ↦ hφc (he ▸ φ.map_zero)
    have he : a*c = b*b := hi (by rw [map_mul,map_mul,hbc,hab]; ring)
    obtain ⟨t,ht⟩ := h ha hb hc ha' hb' hc' he
    refine ⟨t, mul_left_cancel₀ hφa ?_⟩
    change φ a * φ (C t) = φ a * r
    rw [← map_mul, ← ht, hab]
  · intro h a b c ha hb hc ha' hb' hc' he
    have hφa : φ a ≠ 0 := fun hz ↦ ha (hi (hz.trans φ.map_zero.symm))
    let r := φ b / φ a
    have hab : φ b = φ a * r := by dsimp [r]; field_simp
    have hbc : φ c = φ b * r := by
      dsimp [r]
      have hm := congrArg φ he
      simp only [map_mul] at hm
      field_simp
      linear_combination hm
    obtain ⟨t,ht⟩ := h ha ha' hb' hc' hab hbc
    exact ⟨t, hi (by rw [map_mul,hab]; change _ = φ a * RatFunc.C t; rw [ht])⟩

private theorem degree_blocks_same_of_midpoint {N : ℕ → ℕ}
    (hgap : ∀ ⦃i j⦄, i < j → 2*N i+2*j < N j) {i j k a b c : ℕ}
    (ha₀ : N i ≤ a+i) (ha₁ : a ≤ N i) (hb₀ : N j ≤ b+j) (hb₁ : b ≤ N j)
    (hc₀ : N k ≤ c+k) (hc₁ : c ≤ N k) (he : a+c = b+b) (hac : a ≤ c) :
    i = j ∧ j = k := by
  have hjk : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · have := hgap h; omega
    · exact h
    · have := hgap h; omega
  subst k
  refine ⟨?_,rfl⟩
  rcases lt_trichotomy i j with h | h | h
  · have := hgap h; omega
  · exact h
  · have := hgap h; omega

/-- Separated degree blocks cannot create a rational-ratio progression,
including one with all three degrees equal. -/
theorem rationalFunctionRatioThreeGPFree_blockUnion {N : ℕ → ℕ}
    (hgap : ∀ ⦃i j⦄, i < j → 2*N i + 2*j < N j) {E : ℕ → Set F[X]}
    (hE : ∀ j, RationalFunctionRatioThreeGPFree (E j)) :
    RationalFunctionRatioThreeGPFree (polynomialBlockUnion N E) := by
  rintro a b c ha hb hc ⟨i,ha',hi₀,hi₁⟩ ⟨j,hb',hj₀,hj₁⟩ ⟨k,hc',hk₀,hk₁⟩ he
  have hn := congrArg natDegree he
  simp only [natDegree_mul ha hc, natDegree_mul hb hb] at hn
  have hij : i = j ∧ j = k := by
    rcases le_total a.natDegree c.natDegree with h | h
    · exact degree_blocks_same_of_midpoint hgap hi₀ hi₁ hj₀ hj₁ hk₀ hk₁ hn h
    · have hm := degree_blocks_same_of_midpoint hgap hk₀ hk₁ hj₀ hj₁ hi₀ hi₁ (by omega) h
      exact ⟨hm.2.symm,hm.1.symm⟩
  obtain ⟨rfl,rfl⟩ := hij
  exact hE i ha hb hc ha' hb' hc' he

/-- Supremum of upper degree-ball densities under the rational-function
ratio convention of the article. -/
noncomputable def rationalFunctionRatioDensitySupremum (F : Type*) [Field F] [Fintype F] : ℝ :=
  polynomialBlockDensitySupremum (F := F) RationalFunctionRatioThreeGPFree

/-- The attainment assertion of `gpp:thm:supremum` for rational-function
ratios over every finite field. -/
theorem rationalFunctionRatioDensitySupremum_attained [Fintype F] :
    ∃ E : Set F[X], 0 ∉ E ∧ RationalFunctionRatioThreeGPFree E ∧
      limsup (polynomialBallProportion E) atTop = rationalFunctionRatioDensitySupremum F :=
  polynomialBlockDensitySupremum_attained RationalFunctionRatioThreeGPFree
    (by intro a b c _ _ _ h; exact h.elim)
    (by intro N hgap E hE; exact rationalFunctionRatioThreeGPFree_blockUnion hgap hE)

end GRHArticle.ProgressionFree
