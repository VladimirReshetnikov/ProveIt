import Surreal.Algebra.ComplexNumbers
import Surreal.HahnSeries.Complexify
import Surreal.HahnSeries.Conjugation
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Hahn series with native complex coefficients

The algebraic identity `K_Γ = F_Γ[i]` in `polynomial:prop:workspace` now
uses Mathlib's real and complex coefficient fields. Coefficient maps reuse
`HahnSeries.map`; the algebraic structure comes from the existing quadratic
bridge. Conjugation fixes exactly the embedded real Hahn series. No surreal
embedding or Hahn-field algebraic-closure theorem is asserted here.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R S : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R] [CommRing S]

/-- A ring equivalence on coefficients induces a ring equivalence on Hahn
series without changing their exponents or supports. -/
def coefficientEquiv (e : R ≃+* S) : R⟦Γ⟧ ≃+* S⟦Γ⟧ where
  toFun x := x.map e
  invFun x := x.map e.symm
  left_inv x := by
    apply _root_.HahnSeries.ext
    funext g
    exact e.symm_apply_apply (x.coeff g)
  right_inv x := by
    apply _root_.HahnSeries.ext
    funext g
    exact e.apply_symm_apply (x.coeff g)
  map_mul' _ _ := _root_.HahnSeries.map_mul e.toRingHom.toNonUnitalRingHom
  map_add' _ _ := _root_.HahnSeries.map_add e.toRingHom.toAddMonoidHom

@[simp] theorem coeff_coefficientEquiv (e : R ≃+* S) (x : R⟦Γ⟧) (g : Γ) :
    (coefficientEquiv e x).coeff g = e (x.coeff g) := rfl

@[simp] theorem support_coefficientEquiv (e : R ≃+* S) (x : R⟦Γ⟧) :
    (coefficientEquiv e x).support = x.support := by
  ext g
  simp only [mem_support, coeff_coefficientEquiv]
  rw [← e.map_zero, e.injective.ne_iff]

/-- A coefficient identification preserves the Hahn order. -/
@[simp] theorem orderTop_coefficientEquiv (e : R ≃+* S) (x : R⟦Γ⟧) :
    (coefficientEquiv e x).orderTop = x.orderTop := by
  apply le_antisymm
  · apply le_orderTop_iff_forall.mpr
    intro g hg
    apply e.map_eq_zero_iff.mp
    exact coeff_eq_zero_of_lt_orderTop hg
  · apply le_orderTop_iff_forall.mpr
    intro g hg
    rw [coeff_coefficientEquiv, coeff_eq_zero_of_lt_orderTop hg, map_zero]

/-- Hahn series over `ℂ` are the quadratic extension of Hahn series over `ℝ`.
This proves the displayed algebraic workspace identification with the actual
coefficient types from the manuscript. -/
def realComplexHahnEquiv : Complexify (ℝ⟦Γ⟧) ≃+* ℂ⟦Γ⟧ :=
  complexifyHahnEquiv.trans (coefficientEquiv Complexify.complexEquiv)

@[simp] theorem coeff_realComplexHahnEquiv (z : Complexify (ℝ⟦Γ⟧)) (g : Γ) :
    (realComplexHahnEquiv z).coeff g = ⟨z.re.coeff g, z.im.coeff g⟩ := by
  change Complexify.complexEquiv ((complexifyToHahn z).coeff g) = _
  rw [coeff_complexifyToHahn]
  rfl

@[simp] theorem coeff_realComplexHahnEquiv_symm_re (z : ℂ⟦Γ⟧) (g : Γ) :
    (realComplexHahnEquiv.symm z).re.coeff g = (z.coeff g).re := rfl

@[simp] theorem coeff_realComplexHahnEquiv_symm_im (z : ℂ⟦Γ⟧) (g : Γ) :
    (realComplexHahnEquiv.symm z).im.coeff g = (z.coeff g).im := rfl

theorem support_realComplexHahnEquiv (z : Complexify (ℝ⟦Γ⟧)) :
    (realComplexHahnEquiv z).support = z.re.support ∪ z.im.support := by
  change (coefficientEquiv Complexify.complexEquiv (complexifyToHahn z)).support = _
  rw [support_coefficientEquiv, support_complexifyToHahn]

/-- The real Hahn subring inside the complex Hahn ring. -/
def complexRealEmbedding : ℝ⟦Γ⟧ →+* ℂ⟦Γ⟧ :=
  (coefficientEquiv Complexify.complexEquiv).toRingHom.comp embedRealSeries

@[simp] theorem coeff_complexRealEmbedding (x : ℝ⟦Γ⟧) (g : Γ) :
    (complexRealEmbedding x).coeff g = (x.coeff g : ℂ) := rfl

theorem complexRealEmbedding_injective :
    Function.Injective (complexRealEmbedding : ℝ⟦Γ⟧ →+* ℂ⟦Γ⟧) := by
  intro x y h
  apply _root_.HahnSeries.ext
  funext g
  exact congrArg (fun z : ℂ⟦Γ⟧ => (z.coeff g).re) h

/-- Ordinary complex conjugation, applied coefficientwise. -/
def complexConjugation : ℂ⟦Γ⟧ ≃+* ℂ⟦Γ⟧ := coefficientEquiv (starRingAut : ℂ ≃+* ℂ)

@[simp] theorem coeff_complexConjugation (z : ℂ⟦Γ⟧) (g : Γ) :
    (complexConjugation z).coeff g = star (z.coeff g) := rfl

/-- The native complex coefficient identification respects conjugation. -/
theorem complexConjugation_coefficientEquiv (z : (Complexify ℝ)⟦Γ⟧) :
    complexConjugation (coefficientEquiv Complexify.complexEquiv z) =
      coefficientEquiv Complexify.complexEquiv (conjugation z) := by
  apply _root_.HahnSeries.ext
  funext g
  exact (Complexify.complexEquiv_conj (z.coeff g)).symm

@[simp] theorem complexConjugation_realComplexHahnEquiv (z : Complexify (ℝ⟦Γ⟧)) :
    complexConjugation (realComplexHahnEquiv z) = realComplexHahnEquiv (star z) := by
  change complexConjugation (coefficientEquiv Complexify.complexEquiv
    (complexifyToHahn z)) = _
  rw [complexConjugation_coefficientEquiv, conjugation_complexifyToHahn]
  rfl

@[simp] theorem support_complexConjugation (z : ℂ⟦Γ⟧) :
    (complexConjugation z).support = z.support := support_coefficientEquiv _ _

@[simp] theorem orderTop_complexConjugation (z : ℂ⟦Γ⟧) :
    (complexConjugation z).orderTop = z.orderTop := orderTop_coefficientEquiv _ _

theorem complexConjugation_eq_self_iff_im_eq_zero (z : ℂ⟦Γ⟧) :
    complexConjugation z = z ↔ ∀ g, (z.coeff g).im = 0 := by
  constructor
  · intro h g
    exact Complex.conj_eq_iff_im.mp (congrArg (fun w : ℂ⟦Γ⟧ => w.coeff g) h)
  · intro h
    apply _root_.HahnSeries.ext
    funext g
    exact Complex.conj_eq_iff_im.mpr (h g)

/-- The fixed-subfield identification in `polynomial:prop:workspace`,
with native real and complex coefficients. The ring statement already holds
for ordered cancellative exponent monoids; additive groups give Hahn fields. -/
theorem complexConjugation_eq_self_iff_mem_range (z : ℂ⟦Γ⟧) :
    complexConjugation z = z ↔ z ∈ Set.range
      (complexRealEmbedding : ℝ⟦Γ⟧ →+* ℂ⟦Γ⟧) := by
  rw [complexConjugation_eq_self_iff_im_eq_zero]
  constructor
  · intro h
    refine ⟨(realComplexHahnEquiv.symm z).re, ?_⟩
    apply _root_.HahnSeries.ext
    funext g
    apply Complex.ext <;> simp [h g]
  · rintro ⟨x, rfl⟩
    intro g
    simp

end

noncomputable section

variable (Δ : Type*) [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]

/-- For an exponent group, the embedded real Hahn ring is a subfield of
the complex Hahn field. -/
def realHahnSubfield : Subfield ℂ⟦Δ⟧ :=
  (complexRealEmbedding : ℝ⟦Δ⟧ →+* ℂ⟦Δ⟧).fieldRange

/-- The bundled real Hahn subfield is isomorphic to the real Hahn field. -/
def realHahnSubfieldEquiv : ℝ⟦Δ⟧ ≃+* realHahnSubfield Δ :=
  (complexRealEmbedding : ℝ⟦Δ⟧ →+* ℂ⟦Δ⟧).rangeRestrictFieldEquiv

/-- The fixed-field clause of `polynomial:prop:workspace` as a bundled
subfield equality of membership conditions. No closedness claim is needed. -/
theorem mem_realHahnSubfield_iff (z : ℂ⟦Δ⟧) :
    z ∈ realHahnSubfield Δ ↔ complexConjugation z = z :=
  (complexConjugation_eq_self_iff_mem_range z).symm

end

end Surreal.HahnSeries
