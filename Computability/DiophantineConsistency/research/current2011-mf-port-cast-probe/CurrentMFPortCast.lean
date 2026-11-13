import CurrentMFRecipe
import Current14LiteralPortsMF

/-! Isolate the closed natural-sum cast to the fourth actual port. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMFPortCast
attribute [local irreducible] CurrentMasks2011.radix CurrentMasks2011.highPort
  CurrentMasks2011.beta CurrentWindowCarry2011.ports Current14LiteralPortsMF.omega

theorem cast_add_port_param (h b : ℕ) (p : ℤ)
    (hp : (h : ℤ) + (b : ℤ) = p) : ((h + b : ℕ) : ℤ) = p :=
  (Nat.cast_add h b).trans hp

theorem port_natural_cast :
    ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) =
      CurrentWindowCarry2011.ports 3 :=
  cast_add_port_param _ _ _
    (Current14LiteralPortsMF.omega_eq.trans Current14LiteralPortsMF.all_ports.2.2.2.symm)

#print axioms cast_add_port_param
#print axioms port_natural_cast
end DiophantineConsistency.CurrentMFPortCast
