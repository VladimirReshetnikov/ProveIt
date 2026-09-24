import Surreal.Algebra.ArithmeticLanguage
import Surreal.Algebra.ArithmeticGuards
import Surreal.Algebra.FormulaRelativizationLanguageMap

/-!
# Interpreting natural arithmetic in rings with a standard-integer guard

The natural-arithmetic translation in `odg:def:cor:arithmetic` for any
ordered commutative ring in which Xi defines exactly the ordinary integers.
The source language has precisely zero, one, addition and multiplication.
-/

namespace Surreal.StandardArithmetic
open FirstOrder FirstOrder.Language

/-- Change the arithmetic symbols to ring symbols, then guard every quantifier by standard naturalness. -/
def naturalTranslation {α : Type*} {n : ℕ} (φ : language.BoundedFormula α n) :
    Language.ring.BoundedFormula α n :=
  FormulaRelativization.relativize ArithmeticGuards.naturalGuard (toRing.onBoundedFormula φ)

variable {R : Type*} [CommRing R] [CharZero R] [FirstOrder.Ring.CompatibleRing R]

/-- The semantic translation only requires the exact natural guard, independently of how it is proved. -/
theorem realize_naturalTranslation_of_guard
    (hNat : ∀ x : Fin 1 → R, ArithmeticGuards.naturalGuard.Realize x ↔
      ∃ a : ℕ, (a : R) = x 0)
    {α : Type*} {n : ℕ} (φ : language.BoundedFormula α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    (naturalTranslation φ).Realize (fun a => (v a : R)) (fun j => (xs j : R)) ↔
      φ.Realize v xs :=
  FormulaRelativization.realize_relativize_onBoundedFormula toRing ArithmeticGuards.naturalGuard
    (naturalEmbedding R) hNat φ v xs

omit [CharZero R] in
/-- A homomorphism to an ordered ring supplies the positivity argument, even when no order
has been chosen on the ambient ring itself. -/
theorem realize_naturalGuard_iff_of_ordered_hom
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] (ρ : R →+* S)
    (hXi : ∀ x : R, DiophantineConstants.Xi x ↔ ∃ a : ℤ, x = (a : R)) (x : Fin 1 → R) :
    ArithmeticGuards.naturalGuard.Realize x ↔ ∃ a : ℕ, (a : R) = x 0 := by
  rw [ArithmeticGuards.realize_naturalGuard]
  constructor
  · rintro ⟨hx, s, hs⟩
    obtain ⟨a, ha⟩ := (hXi _).mp hx
    have he := congrArg ρ hs
    rw [ha, map_intCast, map_sum] at he
    simp only [map_pow] at he
    have hp : (0 : S) ≤ (a : S) := he ▸ Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hn : 0 ≤ a := by exact_mod_cast hp
    refine ⟨a.toNat, ?_⟩
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
    exact ha.symm
  · rintro ⟨a, ha⟩
    rw [← ha]
    refine ⟨(hXi _).mpr ⟨a, by simp⟩, ?_⟩
    obtain ⟨s, hs⟩ := QuinticConstants.integer_four_squares (a : ℤ) (Int.natCast_nonneg _)
    refine ⟨fun j => (s j : R), ?_⟩
    have he := congrArg (Int.castRingHom R) hs
    simp only [map_sum, map_pow] at he
    change (∑ j, (s j : R) ^ 2) = ((a : ℤ) : R) at he
    simpa only [Int.cast_natCast] using he.symm

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The concrete natural guard recognizes the image of the natural-number embedding. -/
theorem realize_naturalGuard_iff
    (hXi : ∀ x : R, DiophantineConstants.Xi x ↔ ∃ a : ℤ, x = (a : R)) (x : Fin 1 → R) :
    ArithmeticGuards.naturalGuard.Realize x ↔ ∃ a : ℕ, naturalEmbedding R a = x 0 := by
  rw [ArithmeticGuards.realize_naturalGuard,
    ← NaturalNumbersDefinition.natural_iff_standard_four_squares _ hXi]
  exact exists_congr fun _ => eq_comm

/-- Arbitrary quantifier alternations are interpreted correctly at every natural tuple. -/
theorem realize_naturalTranslation
    (hXi : ∀ x : R, DiophantineConstants.Xi x ↔ ∃ a : ℤ, x = (a : R))
    {α : Type*} {n : ℕ} (φ : language.BoundedFormula α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    (naturalTranslation φ).Realize (fun a => (v a : R)) (fun j => (xs j : R)) ↔
      φ.Realize v xs :=
  FormulaRelativization.realize_relativize_onBoundedFormula toRing ArithmeticGuards.naturalGuard
    (naturalEmbedding R) (realize_naturalGuard_iff hXi) φ v xs

/-- Each natural arithmetic sentence has a truth-equivalent ring sentence using no parameters. -/
theorem naturalSentence_iff
    (hXi : ∀ x : R, DiophantineConstants.Xi x ↔ ∃ a : ℤ, x = (a : R))
    (φ : language.Sentence) : (R ⊨ naturalTranslation φ) ↔ (ℕ ⊨ φ) := by
  have h := realize_naturalTranslation hXi φ default default
  unfold Sentence.Realize Formula.Realize
  convert h using 2

end Surreal.StandardArithmetic
