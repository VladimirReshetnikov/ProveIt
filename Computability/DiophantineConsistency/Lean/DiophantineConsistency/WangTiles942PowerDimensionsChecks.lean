import DiophantineConsistency.WangTiles942PowerDimensions

namespace DiophantineConsistency.WangTiles942PowerDimensionsChecks

open WangTiles942PowerDimensions WangTiles942Periodic

set_option Elab.async false

-- The dimension choice is unconditional arithmetic: T=0 and a composite
-- base are allowed. It does not claim the actual machine halts at zero.
example : ∃ rw rh : ℕ, 0 < rw ∧ 0 < rh ∧
    4 ≤ 4^rw ∧ 2 ≤ 4^rh ∧ 3 ≤ 4^rh ∧ 100 < 4^rw ∧ 2 < 4^rh :=
  exists_power_dimensions 4 (by decide) 0 100 2

-- Width and height bounds are independent and may be arbitrarily large.
example (T wBound hBound : ℕ) :
    ∃ rw rh : ℕ, 0 < rw ∧ 0 < rh ∧
      2*T+4 ≤ 120199^rw ∧ T+2 ≤ 120199^rh ∧ 3 ≤ 120199^rh ∧
      wBound < 120199^rw ∧ hBound < 120199^rh :=
  exists_power_dimensions 120199 (by decide) T wBound hBound

-- The strict base bound matters: powers of one cannot reach even bound1.
example : ¬ ∃ r : ℕ, 1 < 1^r := by simp

-- Retain both the actual word and its uniquely marked origin, without
-- replacing uniqueness by a supplied premise.
example (T w H : ℕ) (hh : (DecimalMachine215.machine.run T).state = none)
    (hw : 2*T+4 ≤ w) (hTH : T+2 ≤ H) (hH : 3 ≤ H) :
    letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
    ∃ a : ZMod (w*H) → Fin 942,
      MarkedWord (w*H) (w : ℤ) a ∧ (∀ z, a z = 0 ↔ z = 0) :=
  cofinal_unique_marked_word T w H hh hw hTH hH

-- Explicit exponent choice also preserves the literal width*height
-- modulus and exposes its equality to the sum-exponent power.
example (p : ℕ) (hp : 1 < p) (T wBound hBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ rw rh : ℕ, 0 < rw ∧ 0 < rh ∧ wBound < p^rw ∧ hBound < p^rh ∧
      p^rw*p^rh = p^(rw+rh) ∧
      letI : NeZero (p^rw*p^rh) := ⟨Nat.mul_ne_zero
        (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega))⟩
      ∃ a : ZMod (p^rw*p^rh) → Fin 942,
        MarkedWord (p^rw*p^rh) ((p^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) :=
  exists_power_marked_word p hp T wBound hBound hh

#print axioms cofinal_unique_marked_word
#print axioms exists_power_dimensions
#print axioms exists_power_marked_word

end DiophantineConsistency.WangTiles942PowerDimensionsChecks
