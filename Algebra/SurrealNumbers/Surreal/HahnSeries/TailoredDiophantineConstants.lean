import Surreal.Algebra.TailoredArithmeticGuard
import Surreal.HahnSeries.DiophantineConstants

/-!
# The tailored guard in intermediate Hahn rings

The constant-definition part of `odg:def:thm:numberfield` for any supplied
prime pair satisfying the manuscript's arithmetic and nonsquareness conditions.
All algebraic and native-formula bridges are proved. The unconditional
number-field specialization is supplied in `NumberFieldArithmeticConstants`.
-/

namespace Surreal.HahnSeries
open TailoredIntersectivePolynomial TailoredDiophantineConstants
noncomputable section

variable {Γ L O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field L] [CharZero L] [CommRing O]

omit [CharZero L] in
/-- Ordinary root exclusion descends to every intermediate Hahn ring with the specified constants. -/
theorem intermediate_tailored_value_ne_zero (p q : ℕ)
    (φ : O →+* L) (hφ : Function.Injective φ) (hroot : ∀ a : O, value p q a ≠ 0)
    (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range) (x : A) : value p q x ≠ 0 := by
  have hp (c : φ.range) :
      ((polynomial p q).map (Int.castRingHom L)).eval (c : L) ≠ 0 := by
    obtain ⟨a, ha⟩ := c.property
    have he : ((polynomial p q).map (Int.castRingHom L)).eval (c : L) = value p q (c : L) := by
      simp [polynomial, value]
    rw [he, ← ha, ← map_value φ]
    exact (map_ne_zero_iff φ hφ).mpr (hroot a)
  have hn := intermediate_polynomial_no_root A φ.range hA
    ((polynomial p q).map (Int.castRingHom L)) hp x
  have he : ((polynomial p q).map (Int.castRingHom L)).eval₂ nonpositiveConstants x.val =
      value p q x.val := by simp [polynomial, value]
  rw [he] at hn
  intro hx
  apply hn
  have hv := congrArg A.subtype hx
  rw [map_value, map_zero] at hv
  exact hv

/-- Pell and divisor rigidity give correctness without a constant-term retraction. -/
theorem intermediate_tailored_xi_iff (p q : ℕ)
    (φ : O →+* L) (hφ : Function.Injective φ) (hroot : ∀ a : O, value p q a ≠ 0)
    (hordinary : ∀ a : O, Xi p q a)
    (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range) (x : A) :
    Xi p q x ↔ x ∈ (intermediateConstants φ A hA).range := by
  apply xi_iff_mem_range p q (intermediateConstants φ A hA) _
    (intermediate_tailored_value_ne_zero p q φ hφ hroot A hA)
    (intermediate_divisor_mem_constants φ A hA) hordinary
  intro u v hp
  obtain ⟨_, b, _, _, hb⟩ := intermediate_pell_two_rigidity A φ.range hA u v hp
  obtain ⟨a, ha⟩ := b.property
  refine ⟨a, Subtype.ext ?_⟩
  change nonpositiveConstants (φ a) = v.val
  rw [ha]
  exact hb.symm

section NumberField
variable {K : Type*} [Field K] [NumberField K]

/-- The tailored predicate defines any subring of a number field once its primes are supplied. -/
theorem numberField_intermediate_tailored_xi_iff {p q : ℕ} (h : Admissible p q)
    (hp : ¬IsSquare (p : K)) (hq : ¬IsSquare (q : K)) (hpq : ¬IsSquare ((p * q : ℕ) : K))
    (o : Subring K) (j : K →+* L) (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) (x : A) :
    Xi p q x ↔ x ∈ (intermediateConstants (j.comp o.subtype) A hA).range := by
  apply intermediate_tailored_xi_iff p q (j.comp o.subtype)
    (j.injective.comp Subtype.val_injective) _ (numberField_subring_xi h o) A hA x
  intro a ha
  have he := congrArg o.subtype ha
  rw [map_value, map_zero] at he
  exact value_ne_zero p q hp hq hpq (a : K) he

local instance tailoredGuardIntermediateStructure (A : Subring (nonpositiveSupportSubring Γ L)) :
    FirstOrder.Ring.CompatibleRing A := FirstOrder.Ring.compatibleRingOfRing A

/-- The actual native five-witness guard has the required coefficient-image semantics. -/
theorem numberField_intermediate_tailored_guard_iff {p q : ℕ} (h : Admissible p q)
    (hp : ¬IsSquare (p : K)) (hq : ¬IsSquare (q : K)) (hpq : ¬IsSquare ((p * q : ℕ) : K))
    (o : Subring K) (j : K →+* L) (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) (x : A) :
    (TailoredArithmeticGuard.guard p q).Realize (fun _ => x) ↔
      x ∈ (intermediateConstants (j.comp o.subtype) A hA).range := by
  rw [TailoredArithmeticGuard.realize_guard]
  exact numberField_intermediate_tailored_xi_iff h hp hq hpq o j A hA x

/-- Thus the coefficient image is parameter-free definable in the native ring language. -/
theorem numberField_intermediate_constants_definable {p q : ℕ} (h : Admissible p q)
    (hp : ¬IsSquare (p : K)) (hq : ¬IsSquare (q : K)) (hpq : ¬IsSquare ((p * q : ℕ) : K))
    (o : Subring K) (j : K →+* L) (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) :
    (∅ : Set A).Definable₁ FirstOrder.Language.ring
      (intermediateConstants (j.comp o.subtype) A hA).range :=
  TailoredArithmeticGuard.constants_definable p q _
    (numberField_intermediate_tailored_xi_iff h hp hq hpq o j A hA)

end NumberField
end
end Surreal.HahnSeries
