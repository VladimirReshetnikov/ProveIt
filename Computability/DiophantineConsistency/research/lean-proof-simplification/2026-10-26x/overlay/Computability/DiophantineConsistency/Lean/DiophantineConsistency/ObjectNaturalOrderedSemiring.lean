import DiophantineConsistency.ObjectResidualSquares
import Mathlib.Algebra.Order.Ring.Canonical

/-! # Multiplication respects the internal natural order -/
noncomputable section
namespace DiophantineConsistency.ObjectNaturalOrderedSemiring
open SetTheory ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem mul_strict_left (a b c : N H) (ha : 0<a) (hbc : b<c) : a*b<a*c := by
  obtain ⟨d,hd⟩ := exists_add_of_le hbc.le
  have hd0 : d≠0 := by
    intro hz
    apply hbc.ne
    simpa only [hz,add_zero] using hd.symm
  rw [hd,mul_add]
  exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr (mul_ne_zero ha.ne' hd0))

instance : IsStrictOrderedRing (N H) where
  __ := (inferInstance : IsOrderedCancelAddMonoid (N H))
  __ := (inferInstance : Nontrivial (N H))
  zero_le_one := ObjectNaturalOrder.Natural.zero_le H 1
  mul_lt_mul_of_pos_left a ha b c hbc := mul_strict_left H a b c ha hbc
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [mul_comm] using mul_strict_left H a b c ha hbc

end DiophantineConsistency.ObjectNaturalOrderedSemiring
