import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.CharP.Algebra

/-!
# Characteristic zero for Hahn series

The injective constant-coefficient homomorphism transfers characteristic zero
from the coefficient semiring. This is the field input needed for polynomial
depression; it does not use closedness or division of exponents.
-/

namespace Surreal.HahnSeries

open scoped _root_.HahnSeries

instance hahnCharZero {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [Semiring R] [CharZero R] : CharZero R⟦Γ⟧ :=
  charZero_of_injective_ringHom _root_.HahnSeries.C_injective

end Surreal.HahnSeries
