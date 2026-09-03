import FabiusFunction.PoissonSummation
import FabiusFunction.SummableCyclicAlias
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The exact half-integer alias identity

The spectra volume's `p1:thm:alias-identity`.  Let `P` be the two-periodization
of the up-function, `P(t) = ∑_ℓ up(t - 2ℓ)`, sample it on the length-`2N`
grid `j/N`, and take the (twice-normalized) discrete Fourier transform

`A_{N,r} = (1/N) ∑_{j < 2N} P(j/N) e^{-πi r j/N}`.

Then every folded coefficient is a complete alias class of the sinc product:

`A_{N,r} = ∑_{q ∈ ℤ} Û(qN + r/2)`.

## Why there is no analysis to do

The corpus already has both halves.  `rvachev_even_translate_fourier` is the
absolutely convergent Fourier series `P(t) = ½ ∑_{k∈ℤ} Û(k/2) e^{iπ k t}`,
valid for every real `t`, and `SummableCyclicAlias` proves that the DFT of the
residue-class sums `R_s(a) = ∑_{k ≡ s} a_k` of any summable bilateral family
is the family of twisted sums `𝒜_k(a) = ∑_n χ(-nk) a_n`.  Sampling the series
at `j/N` turns the exponential into the standard character of `ℤ/2Nℤ`, so the
sample vector is `½ · 𝓕R ∘ neg`; two more DFT identities from Mathlib,
`dft_comp_neg` and `dft_dft`, then give `𝓕(samples) = N · R`.  The theorem is
therefore a chain of rewrites, and it holds for **every** `N ≥ 1` and every
residue `r`, not only for `N = 2^n` and odd `r`.

## Main declarations

* `periodizedUp` — `P`.
* `halfIntegerCoefficient` — `a_k = Û(k/2)`.
* `gridSample` — the sample vector `j ↦ P(j.val/N)` on `ZMod (2N)`.
* `foldedCoefficient` — `A_{N,r}`.
* `gridSample_eq` — the sample vector is `½ · (𝓕 R)(-j)`.
* `dft_gridSample` — `𝓕(samples) = N • R`.
* `foldedCoefficient_eq_intResidueTsum` — **the alias identity**, residue form.
* `foldedCoefficient_eq_tsum` — **`p1:eq:alias-identity`**, as `∑_q Û(qN + r/2)`.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-! ## The objects -/

/-- The two-periodization `P(t) = ∑_{k ∈ ℤ} up(t + 2k)` of the up-function. -/
noncomputable def periodizedUp (F : BoundedFabius) (t : ℝ) : ℂ :=
  ∑' k : ℤ, (rvachevUp F (t + 2 * k) : ℂ)

/-- The half-integer Fourier coefficients `a_k = Û(k/2)`. -/
noncomputable def halfIntegerCoefficient (F : BoundedFabius) (k : ℤ) : ℂ :=
  rvachevFourier F ((((k : ℝ) / 2 : ℝ) : ℂ))

/-- The sample vector of `P` on the grid `j/N`, `j < 2N`, indexed by `ZMod (2N)`. -/
noncomputable def gridSample (F : BoundedFabius) (N : ℕ) (j : ZMod (2 * N)) : ℂ :=
  periodizedUp F ((j.val : ℝ) / N)

/-- The folded coefficient `A_{N,r} = (1/N) ∑_{j<2N} P(j/N) e^{-πi r j/N}`, i.e.
`N⁻¹ · 𝓕(samples)(r)` in Mathlib's normalization of the DFT on `ℤ/2Nℤ`. -/
noncomputable def foldedCoefficient (F : BoundedFabius) (N : ℕ) [NeZero N]
    (r : ZMod (2 * N)) : ℂ :=
  (N : ℂ)⁻¹ * ZMod.dft (gridSample F N) r

/-! ## Sampling the Fourier series -/

/-- The character value at a lattice point: `e^{iπ k (j/N)} = χ_{2N}(k j)`. -/
theorem exp_pi_mul_I_eq_stdAddChar (N : ℕ) [NeZero N] (k : ℤ) (j : ZMod (2 * N)) :
    Complex.exp (Real.pi * Complex.I * (k : ℂ) * (((j.val : ℝ) / N : ℝ) : ℂ))
      = ZMod.stdAddChar ((k : ZMod (2 * N)) * j) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hj : ((k : ZMod (2 * N)) * j) = (((k * (j.val : ℤ) : ℤ)) : ZMod (2 * N)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hj, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp
  ring

/-- The sample vector is the twisted sum at `-j`:
`P(j/N) = ½ · 𝒜_{-j}(a)`, and hence `½ · (𝓕 R)(-j)`. -/
theorem gridSample_eq (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N]
    (j : ZMod (2 * N)) :
    gridSample F N j =
      (2 : ℂ)⁻¹ * intFourierTsum (q := 2 * N) (halfIntegerCoefficient F) (-j) := by
  unfold gridSample periodizedUp intFourierTsum
  rw [rvachev_even_translate_fourier F hF]
  congr 1
  refine tsum_congr fun k => ?_
  rw [smul_eq_mul, halfIntegerCoefficient, exp_pi_mul_I_eq_stdAddChar]
  rw [show -((k : ZMod (2 * N)) * -j) = (k : ZMod (2 * N)) * j by ring]
  ring

/-- **The DFT of the samples is `N` times the residue-class sums.** -/
theorem dft_gridSample (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N] :
    ZMod.dft (gridSample F N) =
      fun r => (N : ℂ) * intResidueTsum (q := 2 * N) (halfIntegerCoefficient F) r := by
  have ha : Summable (halfIntegerCoefficient F) := rvachevFourier_half_int_summable F hF
  have hS : gridSample F N =
      (2 : ℂ)⁻¹ • fun j => ZMod.dft (intResidueTsum (q := 2 * N) (halfIntegerCoefficient F)) (-j) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, gridSample_eq F hF N j, dft_intResidueTsum _ ha]
  rw [hS, map_smul, ZMod.dft_comp_neg, ZMod.dft_dft]
  funext r
  rw [Pi.smul_apply, neg_neg, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- **The alias identity, residue form**: `A_{N,r} = R_r(a) = ∑_{k ≡ r (2N)} Û(k/2)`. -/
theorem foldedCoefficient_eq_intResidueTsum (F : BoundedFabius) (hF : IsFabius F) (N : ℕ)
    [NeZero N] (r : ZMod (2 * N)) :
    foldedCoefficient F N r = intResidueTsum (q := 2 * N) (halfIntegerCoefficient F) r := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold foldedCoefficient
  rw [dft_gridSample F hF N]
  field_simp

/-! ## The alias class as a bilateral series -/

/-- The residue class of `r` modulo `2N` is the affine line `q ↦ 2Nq + r.val`. -/
noncomputable def residueClassEquiv (N : ℕ) [NeZero N] (r : ZMod (2 * N)) :
    ℤ ≃ (fun n : ℤ => (n : ZMod (2 * N))) ⁻¹' {r} where
  toFun q := ⟨2 * N * q + r.val, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self]
    ring⟩
  invFun k := (k.1 - r.val) / (2 * N)
  left_inv q := by
    simp only
    rw [add_sub_cancel_right, mul_comm, Int.mul_ediv_cancel _ (by exact_mod_cast
      Nat.mul_ne_zero two_ne_zero (NeZero.ne N))]
  right_inv k := by
    obtain ⟨k, hk⟩ := k
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hk
    apply Subtype.ext
    simp only
    have hdvd : ((2 * N : ℕ) : ℤ) ∣ k - r.val := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hk, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨c, hc⟩ := hdvd
    push_cast at hc
    rw [hc, mul_comm ((2 : ℤ) * N) c, Int.mul_ediv_cancel _ (by exact_mod_cast
      Nat.mul_ne_zero two_ne_zero (NeZero.ne N))]
    omega

/-- **`p1:eq:alias-identity`**: for every `N ≥ 1` and every residue `r`,

`A_{N,r} = ∑_{q ∈ ℤ} Û(q N + r/2)`. -/
theorem foldedCoefficient_eq_tsum (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N]
    (r : ZMod (2 * N)) :
    foldedCoefficient F N r =
      ∑' q : ℤ, rvachevFourier F (((q : ℂ) * N + (r.val : ℂ) / 2)) := by
  rw [foldedCoefficient_eq_intResidueTsum F hF N r, intResidueTsum,
    ← (residueClassEquiv N r).tsum_eq]
  refine tsum_congr fun q => ?_
  simp only [residueClassEquiv, Equiv.coe_fn_mk, halfIntegerCoefficient]
  congr 1
  push_cast
  ring

/-! ## Even modes and the inverse transform -/

/-- The constant folded mode is `1`: only `q = 0` survives in `∑_q Û(qN)`. -/
theorem foldedCoefficient_zero (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N] :
    foldedCoefficient F N 0 = 1 := by
  rw [foldedCoefficient_eq_tsum F hF N 0, ZMod.val_zero]
  rw [tsum_eq_single 0]
  · simp [rvachevFourier_zero F hF]
  · intro q hq
    have hz : ((q : ℂ) * N + ((0 : ℕ) : ℂ) / 2) = ((q * N : ℤ) : ℂ) := by push_cast; ring
    rw [hz, (rvachevFourier_int_eq_zero_iff F hF _).mpr]
    exact mul_ne_zero hq (by exact_mod_cast NeZero.ne N)

/-- Every nonzero even folded mode vanishes: at `r = 2s` with `0 < s < N`, every
alias point `qN + s` is a nonzero integer, where `Û` has its zeros. -/
theorem foldedCoefficient_two_mul_eq_zero (F : BoundedFabius) (hF : IsFabius F) (N : ℕ)
    [NeZero N] {s : ℕ} (hs0 : s ≠ 0) (hsN : s < N) :
    foldedCoefficient F N ((2 * s : ℕ) : ZMod (2 * N)) = 0 := by
  rw [foldedCoefficient_eq_tsum F hF N]
  have hval : (((2 * s : ℕ) : ZMod (2 * N)).val) = 2 * s := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [hval]
  have hterm : ∀ q : ℤ, rvachevFourier F ((q : ℂ) * N + ((2 * s : ℕ) : ℂ) / 2) = 0 := by
    intro q
    have hne : (q * N + s : ℤ) ≠ 0 := by
      intro h0
      have hmod : (q * N + s : ℤ) % N = s := by
        rw [show (q * N + s : ℤ) = s + N * q by ring, Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt (by omega) (by omega)]
      rw [h0, Int.zero_emod] at hmod
      omega
    have hz : ((q : ℂ) * N + ((2 * s : ℕ) : ℂ) / 2) = ((q * N + s : ℤ) : ℂ) := by
      push_cast
      ring
    rw [hz, (rvachevFourier_int_eq_zero_iff F hF _).mpr hne]
  simp only [hterm, tsum_zero]

/-- **The inverse transform**: the samples are recovered from the folded
coefficients, `P(j/N) = ½ ∑_{r} A_{N,r} χ_{2N}(rj)`. -/
theorem gridSample_eq_sum_foldedCoefficient (F : BoundedFabius) (N : ℕ) [NeZero N]
    (j : ZMod (2 * N)) :
    gridSample F N j =
      (2 : ℂ)⁻¹ * ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) * foldedCoefficient F N r := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h := congrFun (ZMod.dft_dft (gridSample F N)) (-j)
  rw [neg_neg, ZMod.dft_apply] at h
  -- h : ∑ r, χ(-(r * -j)) • 𝓕S r = (2N) • S j
  have h' : ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) * ZMod.dft (gridSample F N) r
      = (2 * N : ℂ) * gridSample F N j := by
    rw [← h]
    push_cast
    refine sum_congr rfl fun r _ => ?_
    rw [smul_eq_mul, show -(r * -j) = r * j by ring]
  simp only [foldedCoefficient]
  have h2N : (2 * (N : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hN
  calc gridSample F N j
      = (2 * (N : ℂ))⁻¹ * ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) * ZMod.dft (gridSample F N) r := by
        rw [h']
        field_simp
    _ = (2 : ℂ)⁻¹ * ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) *
          ((N : ℂ)⁻¹ * ZMod.dft (gridSample F N) r) := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun r _ => ?_
        field_simp

end Fabius
