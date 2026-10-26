import DiophantineConsistency.CurrentKernelResidues2011
import DiophantineConsistency.NativeRankVariation
import Mathlib.FieldTheory.Finite.Basic

/-!
# Units for the actual 2011-cell rank step

The width and cell count are independent powers of the checked auxiliary
prime. Both exponents may be zero. The fixed-prime power reductions use the
checked orders; the auxiliary-prime reduction is Frobenius, not an LTE claim.
The kernel stays the original literal K. No orbit or safe mutation is asserted.
-/

namespace DiophantineConsistency.CurrentControllerUnits2011

open CurrentControllerData2011

set_option Elab.async false
set_option maxRecDepth 10000

/-- Either independent dimension is a power of the actual auxiliary prime. -/
def dimension (n : ℕ) : ℕ := auxiliary^n
def q (n : ℕ) : ℕ := B^(dimension n)
def A (rw : ℕ) : ℕ := CurrentKernel2011.K+B^(dimension rw)
def Gamma (rw n : ℕ) : ℕ :=
  CurrentMasks2011.radix^977*(q n^2-1)*(1+q n*A rw)

theorem dimension_pos (n : ℕ) : 0 < dimension n :=
  pow_pos prime_auxiliary.pos n

theorem B_gt_one : 1 < B := by
  rw [B_eq]
  exact one_lt_pow₀ (by decide) (by decide)

attribute [local irreducible] CurrentKernel2011.K CurrentControllerData2011.B

theorem q_gt_one (n : ℕ) : 1 < q n :=
  one_lt_pow₀ B_gt_one (Nat.ne_of_gt (dimension_pos n))

theorem quadratic_ge_one (n : ℕ) : 1 ≤ q n^2 := by
  have := q_gt_one n
  nlinarith

theorem auxiliary_modEq_23 : auxiliary ≡ 1 [MOD 23] := by decide
theorem auxiliary_modEq_402 : auxiliary ≡ 1 [MOD 402] := by decide

/-- Exact power reduction at the first fixed prime, for every exponent. -/
theorem power_dimension_47 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 47) = (B : ZMod 47) := by
  have he : dimension n ≡ 1 [MOD 23] := by
    simpa only [dimension, one_pow] using auxiliary_modEq_23.pow n
  have hp : (B : ZMod 47)^23 = 1 := by
    rw [← B_order_47]
    exact pow_orderOf_eq_one _
  simpa only [Nat.cast_pow, pow_one] using pow_eq_pow_of_modEq he hp

/-- The second fixed-prime order is 402, not 2010. -/
theorem power_dimension_2011 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 2011) = (B : ZMod 2011) := by
  have he : dimension n ≡ 1 [MOD 402] := by
    simpa only [dimension, one_pow] using auxiliary_modEq_402.pow n
  have hp : (B : ZMod 2011)^402 = 1 := by
    rw [← B_order_2011]
    exact pow_orderOf_eq_one _
  simpa only [Nat.cast_pow, pow_one] using pow_eq_pow_of_modEq he hp

/-- Frobenius handles all auxiliary powers, including auxiliary^0 = 1. -/
theorem power_dimension_auxiliary (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod auxiliary) = (B : ZMod auxiliary) := by
  letI : Fact auxiliary.Prime := ⟨prime_auxiliary⟩
  simpa only [dimension, Nat.cast_pow] using
    (ZMod.pow_card_pow (n := n) (B : ZMod auxiliary))

theorem q_cast_47 (n : ℕ) : (q n : ZMod 47) = 37 :=
  (power_dimension_47 n).trans B_cast_47
theorem q_cast_2011 (n : ℕ) : (q n : ZMod 2011) = 1283 :=
  (power_dimension_2011 n).trans B_cast_2011
theorem q_cast_auxiliary (n : ℕ) : (q n : ZMod auxiliary) = 37435 :=
  (power_dimension_auxiliary n).trans B_cast_auxiliary

private theorem mod_of_cast {m : ℕ} [NeZero m] (a b : ℕ)
    (h : (a : ZMod m) = (b : ZMod m)) (hb : b < m) : a % m = b := by
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hb] using hv

theorem quadratic_mod_47 (n : ℕ) : (q n^2-1) % 47 = 5 := by
  apply mod_of_cast _ 5 _ (by decide)
  rw [Nat.cast_sub (quadratic_ge_one n), Nat.cast_pow, Nat.cast_one, q_cast_47]
  reduce_mod_char

theorem quadratic_mod_2011 (n : ℕ) : (q n^2-1) % 2011 = 1090 := by
  apply mod_of_cast _ 1090 _ (by decide)
  rw [Nat.cast_sub (quadratic_ge_one n), Nat.cast_pow, Nat.cast_one, q_cast_2011]
  reduce_mod_char

theorem quadratic_mod_auxiliary (n : ℕ) : (q n^2-1) % auxiliary = 99282 := by
  apply mod_of_cast _ 99282 _ (by decide)
  rw [Nat.cast_sub (quadratic_ge_one n), Nat.cast_pow, Nat.cast_one, q_cast_auxiliary]
  unfold auxiliary
  reduce_mod_char

/-- The natural coupling factor reduces to the actual checked H expression. -/
theorem coupling_cast {p : ℕ} (rw n : ℕ)
    (hn : (q n : ZMod p) = (B : ZMod p))
    (hw : ((B^(dimension rw) : ℕ) : ZMod p) = (B : ZMod p)) :
    ((1+q n*A rw : ℕ) : ZMod p) =
      ((1+B*CurrentKernel2011.K+B^2 : ℕ) : ZMod p) := by
  simp only [A, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow] at *
  rw [hn, hw]
  ring

theorem coupling_mod_47 (rw n : ℕ) : (1+q n*A rw) % 47 = 29 := by
  have h := coupling_cast rw n (power_dimension_47 n) (power_dimension_47 rw)
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp h).trans
    CurrentKernelResidues2011.Hs_mod_47

theorem coupling_mod_2011 (rw n : ℕ) : (1+q n*A rw) % 2011 = 674 := by
  have h := coupling_cast rw n (power_dimension_2011 n) (power_dimension_2011 rw)
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp h).trans
    CurrentKernelResidues2011.Hs_mod_2011

private theorem transport_modulus (a m n r : ℕ) (hm : m = n)
    (h : a % m = r) : a % n = r := hm ▸ h

theorem coupling_mod_auxiliary (rw n : ℕ) :
    (1+q n*A rw) % auxiliary = 36379 := by
  have h := coupling_cast rw n (power_dimension_auxiliary n) (power_dimension_auxiliary rw)
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp h).trans
    (transport_modulus _ 120199 auxiliary 36379 rfl
      CurrentKernelResidues2011.Hs_mod_auxiliary)

private theorem coprime_of_mod_ne_zero {x p : ℕ} (hp : Nat.Prime p)
    (h : x % p ≠ 0) : Nat.Coprime x p := by
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hd
  exact h (Nat.mod_eq_zero_of_dvd hd)

theorem radix_coprime {p : ℕ} (ho : Odd p) :
    Nat.Coprime CurrentMasks2011.radix p :=
  (Nat.coprime_two_left.mpr ho).pow_left 47

private theorem gamma_coprime_of_factors (rw n p : ℕ) (ho : Odd p)
    (hs : Nat.Coprime (q n^2-1) p)
    (hh : Nat.Coprime (1+q n*A rw) p) : Nat.Coprime (Gamma rw n) p := by
  have hr : Nat.Coprime (CurrentMasks2011.radix^977) p :=
    (radix_coprime ho).pow_left 977
  exact (hr.mul_left hs).mul_left hh

theorem coprime_Gamma_47 (rw n : ℕ) : Nat.Coprime (Gamma rw n) 47 := by
  apply gamma_coprime_of_factors rw n 47 (by decide)
  · apply coprime_of_mod_ne_zero prime_47
    rw [quadratic_mod_47]
    decide
  · apply coprime_of_mod_ne_zero prime_47
    rw [coupling_mod_47]
    decide

theorem coprime_Gamma_2011 (rw n : ℕ) : Nat.Coprime (Gamma rw n) 2011 := by
  apply gamma_coprime_of_factors rw n 2011 (by decide)
  · apply coprime_of_mod_ne_zero prime_2011
    rw [quadratic_mod_2011]
    decide
  · apply coprime_of_mod_ne_zero prime_2011
    rw [coupling_mod_2011]
    decide

theorem coprime_Gamma_auxiliary (rw n : ℕ) :
    Nat.Coprime (Gamma rw n) auxiliary := by
  apply gamma_coprime_of_factors rw n auxiliary auxiliary_odd
  · apply coprime_of_mod_ne_zero prime_auxiliary
    rw [quadratic_mod_auxiliary]
    decide
  · apply coprime_of_mod_ne_zero prime_auxiliary
    rw [coupling_mod_auxiliary]
    decide

/-- Unit at the complete actual modulus d*N, with independent width exponent. -/
theorem coprime_Gamma_width_cells (rw n : ℕ) :
    Nat.Coprime (Gamma rw n) (d*dimension n) := by
  rw [d_factors]
  exact ((coprime_Gamma_47 rw n).mul_right (coprime_Gamma_2011 rw n)).mul_right
    ((coprime_Gamma_auxiliary rw n).pow_right n)

theorem isUnit_Gamma_width_cells (rw n : ℕ) :
    IsUnit (Gamma rw n : ZMod (d*dimension n)) :=
  (ZMod.isUnit_iff_coprime _ _).mpr (coprime_Gamma_width_cells rw n)

/-- The natural subtraction in Gamma agrees with the actual signed rank step. -/
theorem Gamma_cast_rankGamma (rw n : ℕ) :
    (Gamma rw n : ℤ) = NativeRankVariation.rankGamma (q n : ℤ) (A rw : ℤ)
      ((CurrentMasks2011.radix : ℤ)^977) := by
  simp only [Gamma, NativeRankVariation.rankGamma, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (quadratic_ge_one n), Nat.cast_one, Nat.cast_add]

theorem Gamma_pos (rw n : ℕ) : 0 < Gamma rw n := by
  have hq := q_gt_one n
  have hs : 0 < q n^2-1 := Nat.sub_pos_of_lt (by nlinarith)
  have hr : 0 < CurrentMasks2011.radix^977 := pow_pos (by decide) _
  exact mul_pos (mul_pos hr hs) (by omega)

end DiophantineConsistency.CurrentControllerUnits2011
