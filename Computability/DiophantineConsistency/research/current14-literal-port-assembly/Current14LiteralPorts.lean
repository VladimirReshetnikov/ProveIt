import DiophantineConsistency.CurrentKernel2011
import DiophantineConsistency.CurrentMaskRecipes2011

/-! Assembly of the four printed constant recipes with the endpoint ports.
The right-hand sides transcribe the printed mathematical formulas; this file
is not a parser for TeX or a formal semantics for PDF. -/

namespace Current14LiteralPorts

open DiophantineConsistency
open scoped BigOperators

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

abbrev rho : ℕ := CurrentMasks2011.radix
abbrev G (n : ℕ) : ℤ := CurrentMasks2011.geometricInt rho n

def beta : ℤ := (rho : ℤ) ^ 2011 - 1

def mu : ℤ := beta - G 951 - (rho : ℤ)^960 * G 26 - (rho : ℤ)^1004

def omega : ℤ := beta + 8 * G 917 - 4 +
  (2^45-4) * (rho : ℤ)^1005 + (rho : ℤ)^960 * G 9 +
  (rho : ℤ)^987 * G 8 + (rho : ℤ)^1004

def phi (x : ℚ) : ℚ :=
  (∑ i : Fin 942, (WangTiles942.selectorWeight (WangTiles942.tile i) : ℚ) *
      x ^ WangTiles942.physicalPosition i) +
  2^10 * x^969 * (x^9 + 2^17) * CurrentKernel2011.geometric (2*x) 8 +
  2^18 * x^942 * (x^18 + 2^17) * CurrentKernel2011.geometric (2*x) 9

def K : ℚ := (rho : ℚ)^18 + (rho : ℚ)^1004 + (rho : ℚ)^2020 +
  2 * (rho : ℚ)^1005 * phi ((rho : ℚ)⁻¹)

theorem beta_eq : (CurrentMasks2011.beta : ℤ) = beta := by
  unfold beta
  unfold CurrentMasks2011.beta
  rw [Nat.cast_sub (one_le_pow₀ (by unfold rho CurrentMasks2011.radix; norm_num : 1 ≤ rho))]
  push_cast
  rfl

theorem mu_eq : (CurrentMasks2011.lowPort : ℤ) = mu := by
  unfold mu
  rw [← beta_eq]
  exact CurrentMasks2011.lowPort_printed_recipe

theorem omega_eq : (CurrentMasks2011.highPort : ℤ) + CurrentMasks2011.beta = omega := by
  unfold omega
  rw [← beta_eq, CurrentMasks2011.highPort_printed_recipe]
  ring

theorem K_eq : (CurrentKernel2011.K : ℚ) = K := by
  unfold K phi
  rw [CurrentKernel2011.K_printed, CurrentKernel2011.phi_printed]

theorem all_ports :
    CurrentWindowCarry2011.ports 0 = beta ∧
    (CurrentWindowCarry2011.ports 1 : ℚ) = K ∧
    CurrentWindowCarry2011.ports 2 = mu ∧
    CurrentWindowCarry2011.ports 3 = omega := by
  constructor
  · change (CurrentMasks2011.beta : ℤ) = beta
    exact beta_eq
  constructor
  · change (CurrentKernel2011.K : ℚ) = K
    exact K_eq
  constructor
  · change (CurrentMasks2011.lowPort : ℤ) = mu
    exact mu_eq
  · change (CurrentMasks2011.highPort : ℤ) + CurrentMasks2011.beta = omega
    exact omega_eq

#print axioms Current14LiteralPorts.beta_eq
#print axioms Current14LiteralPorts.mu_eq
#print axioms Current14LiteralPorts.omega_eq
#print axioms Current14LiteralPorts.K_eq
#print axioms Current14LiteralPorts.all_ports

end Current14LiteralPorts
