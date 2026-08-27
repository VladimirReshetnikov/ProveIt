import FabiusFunction.SincProductShells
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# The Euler product of the complex sinc

The bridge from Mathlib's Euler sine product to the sinc normalization
used throughout the Fabius development:

`∏'_{r} (1 - x²/(r+1)²) = sinc (πx)` for **every** complex `x` —

on the integer complement this is Mathlib's `euler_sineTerm_tprod`;
at a nonzero integer both sides vanish (the product has an exact zero
factor, the sine vanishes); at `0` both sides are `1`.  This is the
per-factor input for the canonical (Hadamard) product of the Rvachev
sinc product `Φ(z) = ∏_m (1 - z²/m²)^{1+v₂(m)}` — the audit's
zero-divisor structure with multiplicities `1 + v₂(m)`.

* `tprod_eq_zero_of_eq_zero` — an unordered product in `ℂ` with a
  vanishing factor vanishes (via `HasProd` at `0` directly; no
  multipliability needed).
* `tprod_one_add_sineTerm` — the unconditional Euler–sinc bridge.
-/

set_option autoImplicit false

open Complex Real Filter

namespace Fabius

/-- An unordered complex product with a vanishing factor vanishes:
once the index enters, every partial product is zero. -/
theorem tprod_eq_zero_of_eq_zero {ι : Type*} {f : ι → ℂ} {i₀ : ι}
    (h : f i₀ = 0) : ∏' i, f i = 0 := by
  classical
  have hev : (fun s : Finset ι => ∏ i ∈ s, f i) =ᶠ[Filter.atTop]
      fun _ => 0 := by
    filter_upwards [Filter.eventually_ge_atTop ({i₀} : Finset ι)] with s hs
    exact Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) h
  have h0 : HasProd f 0 := (Filter.tendsto_congr' hev).mpr tendsto_const_nhds
  exact h0.tprod_eq

/-- **The Euler product of the complex sinc**, unconditionally:
`∏'_{r} (1 + sineTerm x r) = sinc (πx)` for every `x : ℂ`, where
`1 + sineTerm x r = 1 - x²/(r+1)²`. -/
theorem tprod_one_add_sineTerm (x : ℂ) :
    ∏' i : ℕ, (1 + sineTerm x i) = complexSinc (π * x) := by
  by_cases hx : x ∈ Complex.integerComplement
  · rw [euler_sineTerm_tprod hx]
    have hx0 : x ≠ 0 := Complex.integerComplement.ne_zero hx
    have hπx : (π : ℂ) * x ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hx0
    rw [complexSinc, if_neg hπx]
  · rw [Complex.integerComplement, Set.mem_compl_iff, not_not] at hx
    obtain ⟨n, rfl⟩ := hx
    rcases eq_or_ne n 0 with rfl | hn
    · have h1 : ∀ i : ℕ, (1 : ℂ) + sineTerm ((0 : ℤ) : ℂ) i = 1 := by
        intro i
        simp [sineTerm]
      rw [tprod_congr h1, tprod_one]
      rw [show (π : ℂ) * ((0 : ℤ) : ℂ) = 0 by
        rw [Int.cast_zero, mul_zero]]
      rw [complexSinc, if_pos rfl]
    · have habs : ((n.natAbs : ℂ)) * ((n.natAbs : ℂ)) = (n : ℂ) * (n : ℂ) := by
        have h5 : ((n.natAbs * n.natAbs : ℕ) : ℤ) = n * n := Int.natAbs_mul_self
        calc ((n.natAbs : ℂ)) * ((n.natAbs : ℂ))
            = (((n.natAbs * n.natAbs : ℕ) : ℤ) : ℂ) := by norm_cast
          _ = ((n * n : ℤ) : ℂ) := by rw [h5]
          _ = (n : ℂ) * (n : ℂ) := by norm_cast
      have hzero : (1 : ℂ) + sineTerm ((n : ℤ) : ℂ) (n.natAbs - 1) = 0 := by
        rw [sineTerm]
        have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
        have h1 : ((n.natAbs - 1 : ℕ) : ℂ) + 1 = (n.natAbs : ℂ) := by
          have h2 := Nat.succ_pred_eq_of_pos hpos
          exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) h2
        have hne : ((n : ℤ) : ℂ) ^ 2 ≠ 0 :=
          pow_ne_zero _ (Int.cast_ne_zero.mpr hn)
        rw [h1]
        rw [show ((n.natAbs : ℂ)) ^ 2 = ((n : ℤ) : ℂ) ^ 2 by
          rw [pow_two, pow_two, habs]]
        rw [neg_div, div_self hne]
        ring
      rw [tprod_eq_zero_of_eq_zero
        (f := fun i : ℕ => 1 + sineTerm ((n : ℤ) : ℂ) i)
        (i₀ := n.natAbs - 1) hzero]
      have hπn : (π : ℂ) * ((n : ℤ) : ℂ) ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
          (Int.cast_ne_zero.mpr hn)
      have hsin : Complex.sin ((π : ℂ) * ((n : ℤ) : ℂ)) = 0 := by
        rw [show (π : ℂ) * ((n : ℤ) : ℂ) = ((n : ℤ) : ℂ) * π by ring]
        exact Complex.sin_int_mul_pi n
      rw [complexSinc, if_neg hπn, hsin, zero_div]

end Fabius
