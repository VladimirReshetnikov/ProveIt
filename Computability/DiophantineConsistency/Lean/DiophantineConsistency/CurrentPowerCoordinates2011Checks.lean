import DiophantineConsistency.CurrentPowerCoordinates2011

namespace DiophantineConsistency.CurrentPowerCoordinates2011Checks

open CurrentControllerData2011 CurrentPowerCoordinates2011
set_option Elab.async false
attribute [local irreducible] CurrentControllerData2011.B

example : (B : ZMod d)^(auxiliary-1) = 1 := generator_cast_fixed
example : Nat.Coprime d auxiliary := fixed_auxiliary_coprime
example : (B : ZMod (d*auxiliary))^(auxiliary-1) = 1 := generator_cast_C0

-- Full modulus, not merely the auxiliary component.
example (k : ℕ) :
    orderOf ((B : ZMod (d*auxiliary^(k+1)))^(auxiliary-1)) = auxiliary^k :=
  full_order k
example : orderOf ((B : ZMod ((d*auxiliary)*auxiliary^0))^(auxiliary-1)) = 1 := by
  simpa using block_order 0
example : orderOf ((B : ZMod ((d*auxiliary)*auxiliary^1))^(auxiliary-1)) = auxiliary := by
  simpa using block_order 1

-- No coordinate equivalence or affine formula is passed to this endpoint.
example (k : ℕ) :
    ∃ e : ZMod (auxiliary^k) ≃ ZMod (auxiliary^k), ∀ z : ZMod (auxiliary^k),
      (B : ZMod ((d*auxiliary)*auxiliary^k))^((auxiliary-1)*(e z).val) =
        1+((d*auxiliary : ℕ) : ZMod ((d*auxiliary)*auxiliary^k))*
          (z.val : ZMod ((d*auxiliary)*auxiliary^k)) :=
  exists_base_power_coordinates k

-- The actual product identity includes k=0 without truncation.
example : (d*auxiliary)*auxiliary^0 = d*auxiliary^(0+1) := modulus_factorization 0

#print axioms order_product
#print axioms generator_cast_47
#print axioms generator_cast_2011
#print axioms generator_cast_fixed
#print axioms generator_cast_auxiliary
#print axioms fixed_auxiliary_coprime
#print axioms full_order
#print axioms generator_cast_C0
#print axioms modulus_factorization
#print axioms block_order
#print axioms block_projection
#print axioms exists_coordinates
#print axioms exists_base_power_coordinates

end DiophantineConsistency.CurrentPowerCoordinates2011Checks
