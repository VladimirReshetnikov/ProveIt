import DiophantineConsistency.ControllerAuxiliaryChoice

namespace DiophantineConsistency.ControllerAuxiliaryChoiceChecks

open ControllerAuxiliaryChoice

set_option Elab.async false

-- A zero target uses the nonzero translate, including characteristic2.
example : ∃ e : ℕ, e ≤ 1 ∧ (0 : ZMod 2)-e • (1 : ZMod 2) ≠ 0 :=
  exists_boolean_sub_ne_zero 0 1 (by decide)

-- A nonzero target permits the unchanged choice.
example : ∃ e : ℕ, e ≤ 1 ∧ (3 : ZMod 5)-e • (2 : ZMod 5) ≠ 0 :=
  exists_boolean_sub_ne_zero 3 2 (by decide)

-- The nonzero translation is needed to avoid a zero residue.
example : ¬ ∃ e : ℕ, e ≤ 1 ∧ (0 : ZMod 5)-e • (0 : ZMod 5) ≠ 0 := by simp

-- Projection into the prime factor is actual castHom arithmetic.
example : ZMod.castHom (by decide : 5 ∣ 15) (ZMod 5) (2 : ZMod 15) ≠ 0 := by decide

example : ∃ e a : ℕ, e ≤ 1 ∧ 0 < a ∧ a < 15 ∧
    (a : ZMod 15) = 0-(e : ZMod 15)*2 ∧ Nat.Coprime a (5^3) :=
  exists_coprime_cardinality (by norm_num : Nat.Prime 5) (by decide) 0 2 (by decide) 3

-- The endpoint works for exponent0 as well as arbitrary positive powers.
example {p C0 : ℕ} [NeZero C0] (hp : Nat.Prime p) (hdiv : p ∣ C0)
    (t b : ZMod C0) (hb : ZMod.castHom hdiv (ZMod p) b ≠ 0) :
    ∃ e a : ℕ, e ≤ 1 ∧ 0 < a ∧ a < C0 ∧
      (a : ZMod C0) = t-(e : ZMod C0)*b ∧ Nat.Coprime a (p^0) :=
  exists_coprime_cardinality hp hdiv t b hb 0

#print axioms exists_boolean_sub_ne_zero
#print axioms exists_coprime_cardinality

end DiophantineConsistency.ControllerAuxiliaryChoiceChecks
