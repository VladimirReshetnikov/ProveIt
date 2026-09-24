import Surreal.Algebra.TailoredDiophantineConstants
import Surreal.Algebra.ArithmeticGuards

/-!
# Native first-order syntax for the tailored number-field guard

The formula Xi_K of `odg:def:thm:numberfield`, with the two natural radicands
compiled into integer numerals. It is parameter-free and uses exactly the
same five witnesses as the fixed integer/Gaussian guard.
-/

namespace Surreal.TailoredArithmeticGuard
open FirstOrder FirstOrder.Language ArithmeticGuards

/-- The tailored sextic, expressed using only native ring-language operations. -/
def certificate {α : Type*} (p q : ℕ) (t : Language.ring.Term α) : Language.ring.Term α :=
  ((t * t + -numeral p) * (t * t + -numeral q)) * (t * t + -numeral (p * q))

/-- Three equations in one free variable and five witnesses. -/
def system (p q : ℕ) : Language.ring.BoundedFormula (Fin 1) 5 :=
  let x := Term.var (Sum.inl 0)
  let u := Term.var (Sum.inr 0)
  let v := Term.var (Sum.inr 1)
  let w := Term.var (Sum.inr 2)
  let s := Term.var (Sum.inr 3)
  let t := Term.var (Sum.inr 4)
  (x * (u * u + -(numeral 2 * (v * v)) + -1)).bdEqual 0 ⊓
    (x * (v + -(x * w))).bdEqual 0 ⊓ (x * (v * s + -certificate p q t)).bdEqual 0

/-- The native parameter-free tailored guard. -/
def guard (p q : ℕ) : Language.ring.Formula (Fin 1) := (system p q).exs

variable {R : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]

@[simp] theorem realize_certificate {α : Type*} (p q : ℕ) (t : Language.ring.Term α) (v : α → R) :
    (certificate p q t).realize v = TailoredIntersectivePolynomial.value p q (t.realize v) := by
  simp [certificate, TailoredIntersectivePolynomial.value, pow_two, sub_eq_add_neg]

@[simp] theorem realize_system (p q : ℕ) (x : Fin 1 → R) (w : Fin 5 → R) :
    (system p q).Realize x w ↔
      TailoredDiophantineConstants.System p q (x 0) (w 0) (w 1) (w 2) (w 3) (w 4) := by
  simp [system, TailoredDiophantineConstants.System, pow_two, sub_eq_add_neg, and_assoc]

/-- Realizing the native guard is exactly the tailored five-witness predicate. -/
theorem realize_guard (p q : ℕ) (x : Fin 1 → R) :
    (guard p q).Realize x ↔ TailoredDiophantineConstants.Xi p q (x 0) := by
  rw [guard, BoundedFormula.realize_exs]
  simp only [realize_system]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w 0, w 1, w 2, w 3, w 4, hw⟩
  · rintro ⟨u, v, w, s, t, h⟩
    exact ⟨![u, v, w, s, t], h⟩

/-- Correctness of the literal predicate supplies native parameter-free definability. -/
theorem constants_definable (p q : ℕ) (C : Set R)
    (hXi : ∀ x : R, TailoredDiophantineConstants.Xi p q x ↔ x ∈ C) :
    (∅ : Set R).Definable₁ Language.ring C := by
  apply Set.empty_definable_iff.mpr
  refine ⟨guard p q, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, realize_guard, hXi]

end Surreal.TailoredArithmeticGuard
