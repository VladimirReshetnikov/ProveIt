import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# Nonpositive-support Hahn rings and their constant-term retraction

The fixed-workspace algebra in `odg:prop:ring` and `odg:sec:formal`.
In the increasing `t`-exponent convention, purely infinite terms have
negative exponents. The support restriction applies to every term, not
merely to the valuation. No divisibility or nontriviality of the exponent
group is required.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable (Γ R : Type*) [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R]

/-- Series with no positive `t`-exponents form a subring of the Hahn ring. -/
def nonpositiveSupportSubring : Subring R⟦Γ⟧ where
  carrier := {f | ∀ a, 0 < a → f.coeff a = 0}
  zero_mem' := by simp
  one_mem' := by intro a ha; simp [coeff_one, ne_of_gt ha]
  add_mem' := by intro f g hf hg a ha; simp [hf a ha, hg a ha]
  neg_mem' := by intro f hf a ha; simp [hf a ha]
  mul_mem' := by
    intro f g hf hg a ha
    by_contra h
    obtain ⟨b, hb, c, hc, rfl⟩ := support_mul_subset h
    have hb' : b ≤ 0 := le_of_not_gt (fun h => hb (hf b h))
    have hc' : c ≤ 0 := le_of_not_gt (fun h => hc (hg c h))
    exact (not_lt_of_ge (add_nonpos hb' hc')) ha

variable {Γ R}

/-- Membership is equivalent to the entire support lying at or below zero. -/
theorem mem_nonpositiveSupportSubring_iff (f : R⟦Γ⟧) :
    f ∈ nonpositiveSupportSubring Γ R ↔ ∀ a ∈ f.support, a ≤ 0 := by
  constructor
  · intro hf a ha
    exact le_of_not_gt (fun h => ha (hf a h))
  · intro hf a ha
    by_contra hn
    exact (not_lt_of_ge (hf a hn)) ha

/-- Only the zero-zero pair can contribute to the constant coefficient of a product. -/
theorem coeff_zero_mul_of_nonpositive_support (f g : nonpositiveSupportSubring Γ R) :
    (f.val * g.val).coeff 0 = f.val.coeff 0 * g.val.coeff 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_single (0, 0)
  · intro ij hij hne
    have hmem := (Finset.mem_antidiagonal.mp hij)
    have hi := (mem_nonpositiveSupportSubring_iff f.val).mp f.property ij.1 hmem.1
    have hj := (mem_nonpositiveSupportSubring_iff g.val).mp g.property ij.2 hmem.2.1
    have hsum : ij.1 + ij.2 = 0 := hmem.2.2
    have hi0 : ij.1 = 0 := le_antisymm hi (by
      simpa only [hsum, add_zero] using add_le_add (le_refl ij.1) hj)
    have hj0 : ij.2 = 0 := by simpa only [hi0, zero_add] using hsum
    exact False.elim (hne (Prod.ext hi0 hj0))
  · intro hnot
    by_cases hf : f.val.coeff 0 = 0
    · simp [hf]
    by_cases hg : g.val.coeff 0 = 0
    · simp [hg]
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr ⟨hf, hg, zero_add 0⟩))

/-- Constant extraction is multiplicative on the support-restricted ring. -/
def nonpositiveConstantCoeff : nonpositiveSupportSubring Γ R →+* R where
  toFun f := f.val.coeff 0
  map_zero' := rfl
  map_one' := by simp
  map_add' _ _ := rfl
  map_mul' := coeff_zero_mul_of_nonpositive_support

/-- Constants embed in the support-restricted Hahn ring. -/
def nonpositiveConstants : R →+* nonpositiveSupportSubring Γ R :=
  (_root_.HahnSeries.C : R →+* R⟦Γ⟧).codRestrict _ (by
    intro r a ha
    simp [ne_of_gt ha])

@[simp] theorem nonpositiveConstantCoeff_constants (r : R) :
    nonpositiveConstantCoeff (nonpositiveConstants (Γ := Γ) r) = r := by
  change (_root_.HahnSeries.C r : R⟦Γ⟧).coeff 0 = r
  simp

/-- The constant-term retraction is onto the coefficient ring. -/
theorem nonpositiveConstantCoeff_surjective :
    Function.Surjective (nonpositiveConstantCoeff : nonpositiveSupportSubring Γ R →+* R) :=
  fun r => ⟨nonpositiveConstants r, nonpositiveConstantCoeff_constants r⟩

/-- The purely infinite ideal, expressed as the kernel of constant extraction. -/
def purelyInfiniteIdeal : Ideal (nonpositiveSupportSubring Γ R) :=
  RingHom.ker nonpositiveConstantCoeff

/-- The kernel is precisely the series supported at strictly negative `t`-exponents. -/
theorem mem_purelyInfiniteIdeal_iff (f : nonpositiveSupportSubring Γ R) :
    f ∈ purelyInfiniteIdeal ↔ ∀ a ∈ f.val.support, a < 0 := by
  change f.val.coeff 0 = 0 ↔ _
  constructor
  · intro hf a ha
    exact lt_of_le_of_ne ((mem_nonpositiveSupportSubring_iff f.val).mp f.property a ha)
      (fun h => ha (h ▸ hf))
  · intro hf
    by_contra h
    exact (lt_irrefl (0 : Γ)) (hf 0 h)

/-- Modding out the purely infinite ideal gives exactly the coefficient ring. -/
def nonpositiveQuotientEquiv :
    (nonpositiveSupportSubring Γ R) ⧸ purelyInfiniteIdeal (Γ := Γ) (R := R) ≃+* R :=
  (nonpositiveConstantCoeff (Γ := Γ) (R := R)).quotientKerEquivOfSurjective
    (nonpositiveConstantCoeff_surjective (Γ := Γ) (R := R))

end
end Surreal.HahnSeries
