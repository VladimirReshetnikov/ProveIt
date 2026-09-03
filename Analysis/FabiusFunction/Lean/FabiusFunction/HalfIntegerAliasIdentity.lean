import FabiusFunction.PoissonSummation
import FabiusFunction.SummableCyclicAlias
import FabiusFunction.BaseDigitProduct
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
* `foldedCoefficient_zero`, `foldedCoefficient_two_mul_eq_zero` — the constant mode is
  `1`; every nonzero even mode vanishes.
* `gridSample_eq_sum_foldedCoefficient` — the inverse transform.
* `foldedCoefficient_neg` — `A_{N,-r} = A_{N,r}`.
* `sum_dft_mul_dft_neg` — a Parseval-type identity for `ZMod.dft`, for every vector.
* `sum_foldedCoefficient_sq` — the discrete energy identity, all residues.
* `sum_zmod_two_mul_eq_sum_even_add_odd` — the parity split of a sum over `ℤ/2Nℤ`.
* `sum_foldedCoefficient`, `sum_foldedCoefficient_odd` — `∑_r A_{N,r} = 2` and the
  universal trace `∑_{s<N} A_{N,2s+1} = 1`.
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
  try ring

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
  simp only [Pi.smul_apply, smul_eq_mul, neg_neg]
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
    have h2N : (2 : ZMod (2 * N)) * (N : ZMod (2 * N)) = 0 := by
      exact_mod_cast ZMod.natCast_self (2 * N)
    rw [h2N, zero_mul, zero_add]
    try rw [ZMod.natCast_zmod_val]⟩
  invFun k := (k.1 - r.val) / (2 * N)
  left_inv q := by
    have h2N : (2 * (N : ℤ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast NeZero.ne N)
    simp only
    rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ h2N]
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
    have h2N : (2 * (N : ℤ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast NeZero.ne N)
    rw [hc, Int.mul_ediv_cancel_left _ h2N]
    linear_combination -hc

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
  simp only [smul_eq_mul] at h
  push_cast at h
  -- h : ∑ r, χ(-(r * -j)) * 𝓕S r = 2 * N * S j
  have h' : ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) * ZMod.dft (gridSample F N) r
      = 2 * (N : ℂ) * gridSample F N j := by
    rw [← h]
    refine sum_congr rfl fun r _ => ?_
    rw [show -(r * -j) = r * j by ring]
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

/-! ## Symmetry and the discrete energy identity -/

/-- The residue classes of `r` and `-r` are exchanged by negation. -/
noncomputable def residueClassNegEquiv (M : ℕ) (r : ZMod M) :
    (fun n : ℤ => (n : ZMod M)) ⁻¹' {-r} ≃ (fun n : ℤ => (n : ZMod M)) ⁻¹' {r} :=
  (Equiv.neg ℤ).subtypeEquiv fun k => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.neg_apply, Int.cast_neg,
      neg_eq_iff_eq_neg]

/-- The half-integer coefficients are even, `a_{-k} = a_k`. -/
theorem halfIntegerCoefficient_neg (F : BoundedFabius) (hF : IsFabius F) (k : ℤ) :
    halfIntegerCoefficient F (-k) = halfIntegerCoefficient F k := by
  unfold halfIntegerCoefficient
  rw [← rvachevFourier_neg F hF]
  congr 1
  push_cast
  ring

/-- **Folded coefficients are even in the residue**: `A_{N,-r} = A_{N,r}`. -/
theorem foldedCoefficient_neg (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N]
    (r : ZMod (2 * N)) :
    foldedCoefficient F N (-r) = foldedCoefficient F N r := by
  rw [foldedCoefficient_eq_intResidueTsum F hF N, foldedCoefficient_eq_intResidueTsum F hF N,
    intResidueTsum, intResidueTsum, ← (residueClassNegEquiv (2 * N) r).tsum_eq]
  refine tsum_congr fun k => ?_
  exact (halfIntegerCoefficient_neg F hF k.1).symm

/-- **A Parseval-type identity for Mathlib's DFT on `ℤ/Mℤ`**, for every
`Φ : ZMod M → ℂ`: `∑_r 𝓕Φ(r) 𝓕Φ(-r) = M ∑_j Φ(j)²`.  Only `dft_apply`,
`dft_dft`, and an exchange of finite sums are used. -/
theorem sum_dft_mul_dft_neg {M : ℕ} [NeZero M] (Φ : ZMod M → ℂ) :
    ∑ r : ZMod M, ZMod.dft Φ r * ZMod.dft Φ (-r) = (M : ℂ) * ∑ j : ZMod M, Φ j ^ 2 := by
  have hdd := ZMod.dft_dft Φ
  calc ∑ r : ZMod M, ZMod.dft Φ r * ZMod.dft Φ (-r)
      = ∑ r : ZMod M, ∑ j : ZMod M, ZMod.dft Φ r * (ZMod.stdAddChar (-(j * -r)) • Φ j) := by
        refine sum_congr rfl fun r _ => ?_
        rw [ZMod.dft_apply Φ (-r), mul_sum]
    _ = ∑ j : ZMod M, Φ j * ∑ r : ZMod M, ZMod.stdAddChar (-(r * -j)) • ZMod.dft Φ r := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun r _ => ?_
        rw [smul_eq_mul, smul_eq_mul, show -(j * -r) = -(r * -j) by ring]
        ring
    _ = ∑ j : ZMod M, Φ j * ZMod.dft (ZMod.dft Φ) (-j) := by
        refine sum_congr rfl fun j _ => ?_
        rw [ZMod.dft_apply (ZMod.dft Φ) (-j)]
    _ = (M : ℂ) * ∑ j : ZMod M, Φ j ^ 2 := by
        rw [hdd, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [neg_neg, smul_eq_mul]
        ring

/-- **The discrete energy identity, all residues**
(`p1:cor:discrete-energy` before pairing the odd modes):

`∑_{r} A_{N,r}² = (2/N) ∑_{j<2N} P(j/N)²`. -/
theorem sum_foldedCoefficient_sq (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N] :
    ∑ r : ZMod (2 * N), foldedCoefficient F N r ^ 2 =
      2 / (N : ℂ) * ∑ j : ZMod (2 * N), gridSample F N j ^ 2 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h := sum_dft_mul_dft_neg (gridSample F N)
  have hsq : ∀ r : ZMod (2 * N), foldedCoefficient F N r ^ 2
      = (N : ℂ)⁻¹ ^ 2 * (ZMod.dft (gridSample F N) r * ZMod.dft (gridSample F N) (-r)) := by
    intro r
    have hneg : ZMod.dft (gridSample F N) (-r) = ZMod.dft (gridSample F N) r := by
      have h1 := foldedCoefficient_neg F hF N r
      simp only [foldedCoefficient] at h1
      exact mul_left_cancel₀ (inv_ne_zero hN) h1
    simp only [foldedCoefficient]
    rw [hneg]
    ring
  rw [sum_congr rfl fun r _ => hsq r, ← mul_sum, h]
  push_cast
  field_simp
  try ring

/-! ## The parity split and the universal trace -/

/-- A sum over `ℤ/2Nℤ` is a sum over the even and odd residues `2s`, `2s+1`,
`s < N`. -/
theorem sum_zmod_two_mul_eq_sum_even_add_odd (N : ℕ) [NeZero N] (f : ZMod (2 * N) → ℂ) :
    ∑ r : ZMod (2 * N), f r =
      ∑ s ∈ range N, (f ((2 * s : ℕ) : ZMod (2 * N)) + f ((2 * s + 1 : ℕ) : ZMod (2 * N))) := by
  have h2N : 0 < 2 * N := Nat.mul_pos two_pos (Nat.pos_of_ne_zero (NeZero.ne N))
  have hval : ∑ r : ZMod (2 * N), f r = ∑ n ∈ range (2 * N), f ((n : ℕ) : ZMod (2 * N)) := by
    refine sum_nbij' (fun r => r.val) (fun n => (n : ZMod (2 * N))) ?_ ?_ ?_ ?_ ?_
    · intro r _
      exact mem_range.mpr (ZMod.val_lt r)
    · intro n _
      exact mem_univ _
    · intro r _
      exact ZMod.natCast_zmod_val r
    · intro n hn
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hn)]
    · intro r _
      rw [ZMod.natCast_zmod_val]
  rw [hval, sum_range_mul_eq_sum_sum (fun n => f ((n : ℕ) : ZMod (2 * N))) 2 N]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_range_succ, sum_range_succ, sum_range_zero, zero_add, add_zero]

/-- `P(0) = 1`: the periodization at the origin is the central value of `up`. -/
theorem periodizedUp_zero (F : BoundedFabius) (hF : IsFabius F) : periodizedUp F 0 = 1 := by
  unfold periodizedUp
  rw [← Complex.ofReal_tsum]
  have h := rvachev_even_translate_sum_eq_self F hF (t := 0) (by norm_num) (by norm_num)
  simp only [zero_add] at h ⊢
  rw [h, rvachevUp_zero F hF]
  simp

/-- The sum of all folded coefficients is `2`: the inverse transform at `j = 0`. -/
theorem sum_foldedCoefficient (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N] :
    ∑ r : ZMod (2 * N), foldedCoefficient F N r = 2 := by
  have h := gridSample_eq_sum_foldedCoefficient F N 0
  have h0 : gridSample F N 0 = 1 := by
    unfold gridSample
    rw [ZMod.val_zero, Nat.cast_zero, zero_div, periodizedUp_zero F hF]
  rw [h0] at h
  have hchar : ∀ r : ZMod (2 * N), ZMod.stdAddChar (r * (0 : ZMod (2 * N))) = 1 := by
    intro r
    rw [mul_zero, AddChar.map_zero_eq_one]
  simp only [hchar, one_mul] at h
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  field_simp at h
  linear_combination -h

/-- The even residues contribute exactly `A_{N,0} = 1`. -/
theorem sum_foldedCoefficient_even (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N] :
    ∑ s ∈ range N, foldedCoefficient F N ((2 * s : ℕ) : ZMod (2 * N)) = 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [sum_eq_single_of_mem 0 (mem_range.mpr hN)]
  · simp only [mul_zero, Nat.cast_zero]
    exact foldedCoefficient_zero F hF N
  · intro s hs hs0
    exact foldedCoefficient_two_mul_eq_zero F hF N hs0 (mem_range.mp hs)

/-- **The universal trace** (`p1:eq:universal-trace` before pairing): the odd
folded coefficients sum to `1`, for every `N ≥ 1`,
`∑_{s<N} A_{N,2s+1} = 1`. -/
theorem sum_foldedCoefficient_odd (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N] :
    ∑ s ∈ range N, foldedCoefficient F N ((2 * s + 1 : ℕ) : ZMod (2 * N)) = 1 := by
  have h := sum_foldedCoefficient F hF N
  rw [sum_zmod_two_mul_eq_sum_even_add_odd, sum_add_distrib, sum_foldedCoefficient_even F hF N]
    at h
  linear_combination h

end Fabius
