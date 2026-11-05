import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.ArithmeticMaskData
import DiophantineConsistency.MFPaper1982Digits

/-! Draft: bind the four displayed arithmetic recipes using only matrix-free
base modules. This does not parse TeX/PDF and has not yet been checked. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Current14LiteralPortsMF
open DiophantineConsistency
open scoped BigOperators
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

abbrev rho : ℕ := CurrentMasks2011.radix
abbrev G (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, (rho : ℤ) ^ j

def beta : ℤ := (rho : ℤ) ^ 2011 - 1

def mu : ℤ := beta - G 951 - (rho : ℤ)^960 * G 26 - (rho : ℤ)^1004

def omega : ℤ := beta + 8 * G 917 - 4 +
  (2^45-4) * (rho : ℤ)^1005 + (rho : ℤ)^960 * G 9 +
  (rho : ℤ)^987 * G 8 + (rho : ℤ)^1004

def phi (x : ℚ) : ℚ :=
  (∑ i : Fin 942, (WangTiles942.selectorWeight (WangTiles942.tile i) : ℚ) *
      x ^ WangTiles942.physicalPosition i) +
  2^10 * x^969 * (x^9 + 2^17) * MF.CurrentKernel2011.geometric (2*x) 8 +
  2^18 * x^942 * (x^18 + 2^17) * MF.CurrentKernel2011.geometric (2*x) 9

def K : ℚ := (rho : ℚ)^18 + (rho : ℚ)^1004 + (rho : ℚ)^2020 +
  2 * (rho : ℚ)^1005 * phi ((rho : ℚ)⁻¹)

theorem beta_eq : (CurrentMasks2011.beta : ℤ) = beta := by
  unfold beta
  unfold CurrentMasks2011.beta
  rw [Nat.cast_sub (one_le_pow₀ (by unfold rho CurrentMasks2011.radix; norm_num : 1 ≤ rho))]
  push_cast
  rfl

private theorem G_cast (n : ℕ) : (ArithmeticMaskData.G rho n : ℤ) = G n := by
  rw [← ArithmeticMaskData.sum_range_pow]
  push_cast
  rfl

theorem mu_eq : (CurrentMasks2011.lowPort : ℤ) = mu := by
  have h := ArithmeticMaskData.lowList_identity rho (rho-2)
    (by unfold rho CurrentMasks2011.radix; norm_num)
  change Nat.ofDigits rho ArithmeticMaskData.lowDigits +
    (ArithmeticMaskData.G rho 951 + rho^960 * ArithmeticMaskData.G rho 26 + rho^1004) + 1 = rho^2011 at h
  rw [← ArithmeticMaskData.lowPort_ofDigits] at h
  have hz := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hz
  rw [G_cast, G_cast] at hz
  have hb : (CurrentMasks2011.beta : ℤ) = (rho : ℤ)^2011 - 1 := by
    simpa only [beta] using beta_eq
  unfold mu
  rw [← beta_eq, hb]
  linarith

private def geometric (r n : ℕ) : ℕ := ∑ j ∈ Finset.range n, r ^ j
private def geometricInt (r : ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, r ^ j

private theorem geometric_cast (r n : ℕ) :
    (geometric r n : ℤ) = geometricInt r n := by
  simp [geometric, geometricInt]

private theorem highPort_recipe : CurrentMasks2011.highPort =
    4 + 8 * rho * geometric rho 916 +
      rho ^ 960 * geometric rho 9 + rho ^ 987 * geometric rho 8 +
      rho ^ 1004 + (2 ^ 45 - 4) * rho ^ 1005 := by
  unfold CurrentMasks2011.highPort CurrentMasks2011.highDigits
  rw [Nat.ofDigits_append_replicate_zero]
  unfold CurrentMasks2011.highPrefix geometric
  simp only [Nat.ofDigits_append, Nat.ofDigits_cons, Nat.ofDigits_nil,
    MF.Jones1982.ofDigits_replicate, List.length_append,
    List.length_replicate, mul_zero, add_zero]
  norm_num only [Nat.reduceAdd]
  ring

private theorem geometricInt_succ (r : ℤ) (n : ℕ) :
    geometricInt r (n+1) = 1 + r * geometricInt r n := by
  unfold geometricInt
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ, ← Finset.sum_mul]
  ring

private theorem highPort_printed_recipe : (CurrentMasks2011.highPort : ℤ) =
    8 * geometricInt rho 917 - 4 +
      (2^45-4) * (rho : ℤ)^1005 +
      (rho : ℤ)^960 * geometricInt rho 9 +
      (rho : ℤ)^987 * geometricInt rho 8 + (rho : ℤ)^1004 := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) highPort_recipe
  push_cast [Nat.cast_sub (by decide : 4 ≤ (2 : ℕ) ^ 45)] at h
  simp only [geometric_cast] at h
  rw [show 917 = 916 + 1 from rfl, geometricInt_succ]
  linear_combination h

theorem omega_eq : (CurrentMasks2011.highPort : ℤ) + CurrentMasks2011.beta = omega := by
  unfold omega
  rw [← beta_eq, highPort_printed_recipe]
  simp only [geometricInt, G]
  ring

theorem K_eq : (CurrentKernel2011.K : ℚ) = K := by
  unfold K phi
  rw [MF.CurrentKernel2011.K_printed, MF.CurrentKernel2011.phi_printed]

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

#print axioms Current14LiteralPortsMF.beta_eq
#print axioms Current14LiteralPortsMF.mu_eq
#print axioms Current14LiteralPortsMF.omega_eq
#print axioms Current14LiteralPortsMF.K_eq
#print axioms Current14LiteralPortsMF.all_ports
end Current14LiteralPortsMF
