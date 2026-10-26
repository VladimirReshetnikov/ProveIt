import FixedPointCore
import Mathlib.Tactic.ReduceModChar

/-! A complete checked finite-certificate kernel for CurrentControllerUnits2011.

The three kernel-residue assumptions below are exactly the statements supplied
by CurrentKernelResidues2011.K_cast_47 / K_cast_2011 / K_cast_auxiliary.
No assumption about Gamma, exact orders, or prime-power unit lifting is used.
The repository adapter still has to identify r, b and k with its original
radix, B and literal K. This file does not rebuild that repository dependency.
-/

namespace ProofSimplification20261026

abbrev controllerRadical : ℕ := 11360848883

theorem kernel_residue_CRT (k : ℕ)
    (h47 : (k : ZMod 47) = 26)
    (h2011 : (k : ZMod 2011) = 1995)
    (h120199 : (k : ZMod 120199) = 114787) :
    (k : ZMod controllerRadical) = 1491904576 := by
  have hd : (k : ZMod 94517) = 1491904576 := by
    apply (ZMod.chineseRemainder (by decide : Nat.Coprime 47 2011)).injective
    simp only [map_natCast]
    apply Prod.ext
    · change (k : ZMod 47) = 1491904576
      rw [h47]
      reduce_mod_char
    · change (k : ZMod 2011) = 1491904576
      rw [h2011]
      reduce_mod_char
  apply (ZMod.chineseRemainder
    (by decide : Nat.Coprime 94517 120199)).injective
  simp only [map_natCast]
  apply Prod.ext
  · change (k : ZMod 94517) = 1491904576
    exact hd
  · change (k : ZMod 120199) = 1491904576
    rw [h120199]
    reduce_mod_char

/-- The actual base and radix are reduced without constructing natural powers. -/
theorem actual_base_residue :
    ((2 ^ 94517 : ℕ) : ZMod controllerRadical) = 10287028452 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem actual_radix_residue :
    ((2 ^ 47 : ℕ) : ZMod controllerRadical) = 10653241607 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

def gammaNatural (radix base kernel auxiliary rw n : ℕ) : ℕ :=
  radix ^ 977 * ((base ^ (auxiliary ^ n)) ^ 2 - 1) *
    (1 + base ^ (auxiliary ^ n) * (kernel + base ^ (auxiliary ^ rw)))

/-- One finite residue certifies all independent width/cell exponents. -/
theorem gamma_residue (radix base kernel : ℕ)
    (hb : 1 ≤ base)
    (hB : (base : ZMod controllerRadical) = 10287028452)
    (hr : (radix : ZMod controllerRadical) = 10653241607)
    (hK : (kernel : ZMod controllerRadical) = 1491904576)
    (rw n : ℕ) :
    (gammaNatural radix base kernel 120199 rw n : ZMod controllerRadical) =
      706142772 := by
  have hfix : (base : ZMod controllerRadical) ^ 120199 =
      (base : ZMod controllerRadical) := by
    rw [hB]
    reduce_mod_char
  have hlow : 1 ≤ (base ^ (120199 ^ n)) ^ 2 :=
    one_le_pow₀ (one_le_pow₀ hb)
  simp only [gammaNatural, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Nat.cast_sub hlow, Nat.cast_one]
  rw [fixed_power hfix n, fixed_power hfix rw, hB, hr, hK]
  reduce_mod_char

/-- No primality, exact-order or positive-exponent hypotheses are needed. -/
theorem gamma_coprime_all (radix base kernel : ℕ)
    (hb : 1 ≤ base)
    (hB : (base : ZMod controllerRadical) = 10287028452)
    (hr : (radix : ZMod controllerRadical) = 10653241607)
    (hK : (kernel : ZMod controllerRadical) = 1491904576)
    (rw n : ℕ) :
    Nat.Coprime (gammaNatural radix base kernel 120199 rw n)
      (94517 * 120199 ^ n) :=
  coprime_power_modulus (b := 706142772)
    (gamma_residue radix base kernel hb hB hr hK rw n) (by decide)

/-- The literal base/radix specialization needs only the already proved K data. -/
theorem gamma_current_from_kernel_residues (kernel : ℕ)
    (h47 : (kernel : ZMod 47) = 26)
    (h2011 : (kernel : ZMod 2011) = 1995)
    (h120199 : (kernel : ZMod 120199) = 114787)
    (rw n : ℕ) :
    Nat.Coprime (gammaNatural (2 ^ 47) (2 ^ 94517) kernel 120199 rw n)
      (94517 * 120199 ^ n) :=
  gamma_coprime_all _ _ _ (one_le_pow₀ (by decide))
    actual_base_residue actual_radix_residue
    (kernel_residue_CRT kernel h47 h2011 h120199) rw n

#print axioms kernel_residue_CRT
#print axioms gamma_residue
#print axioms gamma_coprime_all
#print axioms gamma_current_from_kernel_residues

end ProofSimplification20261026
