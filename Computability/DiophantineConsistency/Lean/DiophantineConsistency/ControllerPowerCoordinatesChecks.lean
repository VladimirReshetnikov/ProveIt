import DiophantineConsistency.ControllerPowerCoordinates

namespace DiophantineConsistency.ControllerPowerCoordinatesChecks

open ControllerPowerCoordinates
set_option Elab.async false

-- Actual powers1,4,7 give all three affine residues modulo9.
example : ∃ e : ZMod 3 ≃ ZMod 3, ∀ z : ZMod 3,
    (4 : ZMod (3*3))^(e z).val = 1+3*(z.val : ZMod (3*3)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ho : orderOf (4 : ZMod (3*3)) = 3 :=
    orderOf_eq_prime (by decide) (by decide)
  exact exists_power_coordinates (by decide) 4 (by decide) ho

-- C0 may be composite and T may be a nontrivial prime power.
example : ∃ e : ZMod 9 ≃ ZMod 9, ∀ z : ZMod 9,
    (7 : ZMod (6*9))^(e z).val = 1+6*(z.val : ZMod (6*9)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ho : orderOf (7 : ZMod (6*9)) = 9 :=
    orderOf_eq_prime_pow (p:=3) (n:=1) (by decide) (by decide)
  exact exists_power_coordinates (by decide) 7 (by decide) ho

-- The singleton exponent space T=1 is retained.
example : ∃ e : ZMod 1 ≃ ZMod 1, ∀ z : ZMod 1,
    (1 : ZMod (5*1))^(e z).val = 1+5*(z.val : ZMod (5*1)) :=
  exists_power_coordinates (by decide) 1 (by decide) (by simp)

-- Projection1 alone does not give the required full order.
example : ZMod.castHom (by decide : 3 ∣ 3*3) (ZMod 3) (1 : ZMod (3*3)) = 1 :=
  map_one _
example : orderOf (1 : ZMod (3*3)) ≠ 3 := by simp

#print axioms exists_power_coordinates

end DiophantineConsistency.ControllerPowerCoordinatesChecks
