import FabiusFunction.StirlingBasisChange
import Mathlib.Data.ZMod.Basic

/-!
# First-kind Stirling numbers modulo a fixed integer

Grouping the factors of the rising factorial into blocks of `h` consecutive integers and reducing
each block modulo `h` expresses the reduced first-kind Stirling numbers as coefficients of a
power of one fixed polynomial:

`c(qh+s, m) ≡ [x^m] (∏_{r<h} (x+r))^q · ∏_{r<s} (x+r)  (mod h)`

(`stirlingFirst_cast_eq_coeff_block`).  Since the block polynomial `∏_{r<h}(x+r)` has constant
term `∏_{r<h} r = 0` in `ZMod h`, it is divisible by `x`, so its `q`-th power is divisible by
`x^q` and every reduced Stirling number with `m < q` vanishes
(`stirlingFirst_cast_eq_zero_of_lt`).  In particular, for fixed `m` the sequence
`q ↦ c(qh+s, m) mod h` is eventually identically zero, so no exponential-polynomial description
of it carries information beyond the finitely many `q ≤ m`.

## Main results

* `ascPochhammer_eq_prod_range`.
* `prod_range_mul_cast_zmod`, `stirlingFirst_cast_eq_coeff_block`.
* `X_dvd_blockPoly`, `stirlingFirst_cast_eq_zero_of_lt`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- The rising factorial as an explicit product: `x^{(n)} = ∏_{j<n} (x + j)`. -/
theorem ascPochhammer_eq_prod_range (S : Type*) [CommSemiring S] (n : ℕ) :
    ascPochhammer S n = ∏ j ∈ range n, (X + C (j : S)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_right, ih, Finset.prod_range_succ, C_eq_natCast]

section

variable (h : ℕ)

/-- The block polynomial `∏_{r<h} (x + r)` over `ZMod h`. -/
noncomputable def blockPoly : (ZMod h)[X] := ∏ r ∈ range h, (X + C (r : ZMod h))

/-- Reducing the index of a rising-factorial factor modulo `h`. -/
theorem prod_range_mul_cast_zmod (q : ℕ) :
    ∏ j ∈ range (q * h), (X + C ((j : ℕ) : ZMod h)) = blockPoly h ^ q := by
  induction q with
  | zero => simp [blockPoly]
  | succ q ih =>
    rw [show (q + 1) * h = q * h + h by ring, Finset.prod_range_add, ih, pow_succ, blockPoly]
    congr 1
    refine Finset.prod_congr rfl fun r _ => ?_
    congr 2
    push_cast
    rw [ZMod.natCast_self, mul_zero, zero_add]

/-- **The block product:** the reduced first-kind Stirling numbers are the coefficients of a
power of the block polynomial times a short tail. -/
theorem stirlingFirst_cast_eq_coeff_block (q s m : ℕ) :
    ((Nat.stirlingFirst (q * h + s) m : ℕ) : ZMod h) =
      coeff (blockPoly h ^ q * ∏ r ∈ range s, (X + C ((r : ℕ) : ZMod h))) m := by
  have hsplit : ascPochhammer (ZMod h) (q * h + s) =
      blockPoly h ^ q * ∏ r ∈ range s, (X + C ((r : ℕ) : ZMod h)) := by
    rw [ascPochhammer_eq_prod_range, Finset.prod_range_add, prod_range_mul_cast_zmod]
    congr 1
    refine Finset.prod_congr rfl fun r _ => ?_
    congr 2
    push_cast
    rw [ZMod.natCast_self, mul_zero, zero_add]
  rw [← hsplit, coeff_ascPochhammer]
  split_ifs with hm
  · rfl
  · rw [Nat.stirlingFirst_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- The block polynomial is divisible by `x`, because `0` is one of the shifts. -/
theorem X_dvd_blockPoly (hh : 0 < h) : (X : (ZMod h)[X]) ∣ blockPoly h := by
  have hdvd := Finset.dvd_prod_of_mem
    (fun r : ℕ => (X : (ZMod h)[X]) + C ((r : ℕ) : ZMod h)) (Finset.mem_range.mpr hh)
  simpa [blockPoly] using hdvd

/-- **Eventual vanishing:** for `m < q` the reduced Stirling number is zero.  So for fixed `m`
the sequence `q ↦ c(qh+s, m) mod h` is eventually identically zero. -/
theorem stirlingFirst_cast_eq_zero_of_lt (hh : 0 < h) (q s m : ℕ) (hm : m < q) :
    ((Nat.stirlingFirst (q * h + s) m : ℕ) : ZMod h) = 0 := by
  obtain ⟨f, hf⟩ : (X : (ZMod h)[X]) ^ q ∣
      blockPoly h ^ q * ∏ r ∈ range s, (X + C ((r : ℕ) : ZMod h)) :=
    dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_blockPoly h hh) q) _
  rw [stirlingFirst_cast_eq_coeff_block, hf, mul_comm ((X : (ZMod h)[X]) ^ q) f,
    Polynomial.coeff_mul_X_pow', if_neg (by omega : ¬ q ≤ m)]

end

end Fabius
