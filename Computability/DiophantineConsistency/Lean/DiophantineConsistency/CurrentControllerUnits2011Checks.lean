import DiophantineConsistency.CurrentControllerUnits2011

namespace DiophantineConsistency.CurrentControllerUnits2011Checks

open CurrentControllerData2011 CurrentControllerUnits2011

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K CurrentControllerData2011.B

private theorem coprime_transport (a m n : ℕ) (hm : m = n)
    (h : Nat.Coprime a m) : Nat.Coprime a n := hm ▸ h

-- Zero exponents represent dimension one, not dimension zero.
example : dimension 0 = 1 := by simp only [dimension, pow_zero]
example : q 0 = B := by simp only [q, dimension, pow_zero, pow_one]
example : (A 0 : ZMod 47) = 16 := by
  rw [A, Nat.cast_add, power_dimension_47, CurrentKernelResidues2011.K_cast_47,
    B_cast_47]
  decide +kernel
example : Nat.Coprime (Gamma 0 0) d :=
  coprime_transport (Gamma 0 0) (d*dimension 0) d
    (by simp only [dimension, pow_zero, mul_one])
    (coprime_Gamma_width_cells 0 0)

-- Independent exponents: neither width divides count nor rw <= n is assumed.
example (rw n : ℕ) : Nat.Coprime (Gamma rw n) (d*auxiliary^n) :=
  coprime_Gamma_width_cells rw n
example : Nat.Coprime (Gamma 17 0) d :=
  coprime_transport (Gamma 17 0) (d*dimension 0) d
    (by simp only [dimension, pow_zero, mul_one])
    (coprime_Gamma_width_cells 17 0)
example (rw n : ℕ) : IsUnit (Gamma rw n : ZMod (d*auxiliary^n)) :=
  isUnit_Gamma_width_cells rw n

example (n : ℕ) : (q n : ZMod 47) = 37 ∧ (q n : ZMod 2011) = 1283 ∧
    (q n : ZMod auxiliary) = 37435 :=
  ⟨q_cast_47 n, q_cast_2011 n, q_cast_auxiliary n⟩

example (rw n : ℕ) : (1+q n*A rw) % 47 = 29 ∧
    (1+q n*A rw) % 2011 = 674 ∧ (1+q n*A rw) % auxiliary = 36379 :=
  ⟨coupling_mod_47 rw n, coupling_mod_2011 rw n, coupling_mod_auxiliary rw n⟩

example (n : ℕ) : (q n^2-1) % 47 = 5 ∧ (q n^2-1) % 2011 = 1090 ∧
    (q n^2-1) % auxiliary = 99282 :=
  ⟨quadratic_mod_47 n, quadratic_mod_2011 n, quadratic_mod_auxiliary n⟩

-- The literal signed perturbation has the coefficient proved coprime above.
example (rw n j : ℕ) (C F MC MF J : ℤ) :
    NativeRankVariation.windowRank (q n : ℤ)
      (C+(CurrentMasks2011.radix : ℤ)^977*(B : ℤ)^j)
      (F+(A rw : ℤ)*((CurrentMasks2011.radix : ℤ)^977*(B : ℤ)^j)) MC MF J =
      NativeRankVariation.windowRank (q n : ℤ) C F MC MF J-
        (Gamma rw n : ℤ)*(B : ℤ)^j := by
  rw [NativeRankVariation.rank_power_variation, ← Gamma_cast_rankGamma]

example (rw n : ℕ) : 0 < Gamma rw n := Gamma_pos rw n

-- Arbitrary widths do not retain the stated coupling residues.
-- Literal width 0 uses B^0 = 1; rw=0 instead gives width 1 and B^1 = B.
example (n : ℕ) : (1+(q n : ZMod 47)*((CurrentKernel2011.K : ZMod 47)+1)) ≠ 29 := by
  rw [q_cast_47, CurrentKernelResidues2011.K_cast_47]
  decide +kernel

-- q = 1 makes the discriminant factor vanish, rather than giving a unit.
example (a D : ℤ) : NativeRankVariation.rankGamma 1 a D = 0 :=
  NativeRankVariation.rankGamma_one a D
example : ¬Nat.Coprime 0 d := by rw [d_eq]; decide

#print axioms power_dimension_47
#print axioms power_dimension_2011
#print axioms power_dimension_auxiliary
#print axioms quadratic_mod_auxiliary
#print axioms coupling_mod_47
#print axioms coupling_mod_2011
#print axioms coupling_mod_auxiliary
#print axioms coprime_Gamma_47
#print axioms coprime_Gamma_2011
#print axioms coprime_Gamma_auxiliary
#print axioms coprime_Gamma_width_cells
#print axioms isUnit_Gamma_width_cells
#print axioms Gamma_cast_rankGamma
#print axioms Gamma_pos

end DiophantineConsistency.CurrentControllerUnits2011Checks
