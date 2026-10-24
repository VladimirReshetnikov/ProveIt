import DiophantineConsistency.ObjectNaturalDiscrete
import Mathlib.Algebra.Order.Ring.Defs

/-! # Multiplication respects the internal natural order -/
noncomputable section
namespace DiophantineConsistency.ObjectNaturalOrderedSemiring
open SetTheory ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem mul_strict_left (a b c : N H) (ha : 0<a) (hbc : b<c) : a*b<a*c := by
  obtain ⟨t,ht⟩ := (ObjectNaturalDiscrete.lt_iff_exists_add_one H 0 a).mp ha
  obtain ⟨s,hs⟩ := (ObjectNaturalDiscrete.lt_iff_exists_add_one H b c).mp hbc
  have ha' : a=t+1 := by simpa only [zero_add] using ht
  apply (ObjectNaturalDiscrete.lt_iff_exists_add_one H _ _).mpr
  refine ⟨a*s+t,?_⟩
  rw [hs,ha']
  ring

instance : IsStrictOrderedRing (N H) where
  __ := (inferInstance : IsOrderedCancelAddMonoid (N H))
  __ := (inferInstance : Nontrivial (N H))
  zero_le_one := ObjectNaturalOrder.Natural.zero_le H 1
  mul_lt_mul_of_pos_left a ha b c hbc := mul_strict_left H a b c ha hbc
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [mul_comm] using mul_strict_left H a b c ha hbc

end DiophantineConsistency.ObjectNaturalOrderedSemiring
