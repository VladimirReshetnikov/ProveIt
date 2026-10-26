import PowerFixedPoint
import Mathlib.Data.Nat.GCD.Basic

/-! Optional synthesis of the common kernel residue and fixed power map.
The large natural constants remain parameters. Their three exact residue
premises and the natural-subtraction lower bound are explicit. -/
namespace ProofSimplification.GammaCommon
open ProofSimplification.PowerFixedPoint

abbrev modulus : ℕ := 11360848883

theorem fixed_common : (10287028452 : ZMod modulus) ^ 120199 = 10287028452 := by
  reduce_mod_char

/-- The actual binary radix and B have these common residues. -/
theorem radix_common : (((2 : ℕ)^47 : ℕ) : ZMod modulus) = 10653241607 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem B_common : (((2 : ℕ)^94517 : ℕ) : ZMod modulus) = 10287028452 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

/-- This algebraic step matches Gamma exactly; q^2 >= 1 justifies casting
its natural subtraction. No primality premise is used here. -/
theorem gamma_residue {radix q widthPower K : ℕ}
    (hr : (radix : ZMod modulus) = 10653241607)
    (hq : (q : ZMod modulus) = 10287028452)
    (hw : (widthPower : ZMod modulus) = 10287028452)
    (hK : (K : ZMod modulus) = 1491904576)
    (hq2 : 1 ≤ q^2) :
    ((radix^977*(q^2-1)*(1+q*(K+widthPower)) : ℕ) : ZMod modulus) = 706142772 := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hq2,
    Nat.cast_one, Nat.cast_add, hr, hq, hw, hK]
  reduce_mod_char

/-- The original formula after unfolding dimension, q and A, with the
actual fixed auxiliary prime and two independent dimension exponents. -/
def gammaExpression (radix B K rw n : ℕ) : ℕ :=
  radix^977*((B^(120199^n))^2-1)*(1+B^(120199^n)*(K+B^(120199^rw)))

theorem gammaExpression_residue (radix B K rw n : ℕ)
    (hr : (radix : ZMod modulus) = 10653241607)
    (hB : (B : ZMod modulus) = 10287028452)
    (hK : (K : ZMod modulus) = 1491904576) (hBpos : 1 ≤ B) :
    (gammaExpression radix B K rw n : ZMod modulus) = 706142772 := by
  have hn : ((B^(120199^n) : ℕ) : ZMod modulus) = 10287028452 :=
    (natCast_pow_pow_fixed B 120199 n 10287028452 hB fixed_common).trans hB
  have hw : ((B^(120199^rw) : ℕ) : ZMod modulus) = 10287028452 :=
    (natCast_pow_pow_fixed B 120199 rw 10287028452 hB fixed_common).trans hB
  have hq : 1 ≤ B^(120199^n) := one_le_pow₀ hBpos
  exact gamma_residue hr hn hw hK (one_le_pow₀ hq)

/-- A single ordinary gcd certificate handles all three modulus factors. -/
theorem coprime_common {g : ℕ}
    (hg : (g : ZMod modulus) = 706142772) : Nat.Coprime g modulus := by
  have hm : g % modulus = 706142772 :=
    ((ZMod.natCast_eq_natCast_iff' _ _ modulus).mp hg).trans (by decide)
  change Nat.gcd g modulus = 1
  rw [Nat.gcd_comm, Nat.gcd_rec, hm]
  decide

/-- The actual complete width-times-cells modulus, including exponent zero. -/
theorem coprime_width_cells {g : ℕ}
    (hg : (g : ZMod modulus) = 706142772) (n : ℕ) :
    Nat.Coprime g ((47*2011)*120199^n) := by
  have hc := coprime_common hg
  exact (hc.of_dvd_right (by decide : 47*2011 ∣ modulus)).mul_right
    ((hc.of_dvd_right (by decide : 120199 ∣ modulus)).pow_right n)

theorem gammaExpression_unit (radix B K rw n : ℕ)
    (hr : (radix : ZMod modulus) = 10653241607)
    (hB : (B : ZMod modulus) = 10287028452)
    (hK : (K : ZMod modulus) = 1491904576) (hBpos : 1 ≤ B) :
    IsUnit (gammaExpression radix B K rw n : ZMod ((47*2011)*120199^n)) :=
  (ZMod.isUnit_iff_coprime _ _).mpr
    (coprime_width_cells (gammaExpression_residue radix B K rw n hr hB hK hBpos) n)

#print axioms gammaExpression_residue
#print axioms gammaExpression_unit
end ProofSimplification.GammaCommon
