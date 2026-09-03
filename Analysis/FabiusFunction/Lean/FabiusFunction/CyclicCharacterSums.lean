import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Character sums on `ℤ/Mℤ` from the DFT alone

Two finite character sums that the spectra volume's Layer-1 finite Fourier
algebra rests on, both obtained without any orthogonality lemma: Mathlib's
`ZMod.dft_apply` and `ZMod.dft_dft`, applied to the delta function at `0`,
give

`∑_{j ∈ ℤ/Mℤ} χ_M(j k) = M · [k = 0]`,

and reading the standard character through `stdAddChar_coe` turns this into
the geometric sum `∑_{s<N} e^{-2πi s S/N} = N · [N ∣ S]` for an integer `S`.
The volume's **Ramanujan sum for a power-of-two modulus**
(`p1:eq:Ramanujan-power-two`), over the odd residues `r = 2s+1` modulo `2N`,

`∑_{r odd mod 2N} e^{-πi r S/N} = N (-1)^{S/N}` if `N ∣ S`, `0` otherwise,

then follows by factoring out `e^{-πi S/N}`.  Nothing uses that `N` is a
power of two: the identity holds for every `N ≥ 1`.

## Main declarations

* `zmodDelta`, `dft_zmodDelta` — the delta at `0` and its flat transform.
* `sum_stdAddChar_mul` — character orthogonality on `ℤ/Mℤ`.
* `sum_exp_neg_two_pi_I_mul` — the geometric character sum for an integer `S`.
* `ramanujanOddSum`, `ramanujanOddSum_eq` — **`p1:eq:Ramanujan-power-two`**.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-! ## Orthogonality from the DFT -/

/-- The delta function at `0` on `ZMod M`. -/
noncomputable def zmodDelta (M : ℕ) : ZMod M → ℂ := fun j => if j = 0 then 1 else 0

/-- The transform of the delta at `0` is the constant `1`. -/
theorem dft_zmodDelta (M : ℕ) [NeZero M] : ZMod.dft (zmodDelta M) = fun _ => 1 := by
  funext k
  rw [ZMod.dft_apply]
  simp [zmodDelta]

/-- **Character orthogonality on `ℤ/Mℤ`**: `∑_j χ_M(j k) = M` if `k = 0`, else `0`. -/
theorem sum_stdAddChar_mul (M : ℕ) [NeZero M] (k : ZMod M) :
    ∑ j : ZMod M, ZMod.stdAddChar (j * k) = if k = 0 then (M : ℂ) else 0 := by
  have h := congrFun (ZMod.dft_dft (zmodDelta M)) (-k)
  rw [dft_zmodDelta, ZMod.dft_apply, neg_neg] at h
  simp only [smul_eq_mul, mul_one, zmodDelta] at h
  have h' : ∑ j : ZMod M, ZMod.stdAddChar (j * k)
      = ∑ j : ZMod M, ZMod.stdAddChar (-(j * -k)) :=
    sum_congr rfl fun j _ => by rw [show -(j * -k) = j * k by ring]
  rw [h', h]
  split_ifs <;> simp

/-- The geometric character sum `∑_{s ∈ ℤ/Nℤ} e^{-2πi s S/N} = N · [N ∣ S]`. -/
theorem sum_exp_neg_two_pi_I_mul (N : ℕ) [NeZero N] (S : ℤ) :
    ∑ s : ZMod N, Complex.exp (-(2 * Real.pi * Complex.I * (s.val : ℂ) * S / N))
      = if (N : ℤ) ∣ S then (N : ℂ) else 0 := by
  have hterm : ∀ s : ZMod N,
      Complex.exp (-(2 * Real.pi * Complex.I * (s.val : ℂ) * S / N))
        = ZMod.stdAddChar (s * ((-S : ℤ) : ZMod N)) := by
    intro s
    have hcast : s * ((-S : ℤ) : ZMod N) = (((s.val : ℤ) * (-S) : ℤ) : ZMod N) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hcast, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl fun s _ => hterm s, sum_stdAddChar_mul]
  have hiff : (((-S : ℤ) : ZMod N) = 0) ↔ (N : ℤ) ∣ S := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_neg
  simp only [hiff]

/-! ## The Ramanujan sum for the odd residues modulo `2N` -/

/-- The Ramanujan sum over the odd residues `r = 2s + 1` modulo `2N`:
`c_{2N}(S) = ∑_{s<N} e^{-πi (2s+1) S/N}`. -/
noncomputable def ramanujanOddSum (N : ℕ) [NeZero N] (S : ℤ) : ℂ :=
  ∑ s : ZMod N, Complex.exp (-(Real.pi * Complex.I * (2 * (s.val : ℂ) + 1) * S / N))

/-- **`p1:eq:Ramanujan-power-two`**, for every `N ≥ 1`:
`c_{2N}(S) = N (-1)^{S/N}` if `N ∣ S`, and `0` otherwise. -/
theorem ramanujanOddSum_eq (N : ℕ) [NeZero N] (S : ℤ) :
    ramanujanOddSum N S =
      if (N : ℤ) ∣ S then (N : ℂ) * (-1 : ℂ) ^ (S / N) else 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hfac : ∀ s : ZMod N,
      Complex.exp (-(Real.pi * Complex.I * (2 * (s.val : ℂ) + 1) * S / N))
        = Complex.exp (-(Real.pi * Complex.I * S / N)) *
            Complex.exp (-(2 * Real.pi * Complex.I * (s.val : ℂ) * S / N)) := by
    intro s
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring
  unfold ramanujanOddSum
  rw [sum_congr rfl fun s _ => hfac s, ← mul_sum, sum_exp_neg_two_pi_I_mul]
  split_ifs with hdvd
  · obtain ⟨t, ht⟩ := hdvd
    have hS : (S : ℂ) = N * t := by exact_mod_cast ht
    have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hdiv : S / N = t := by rw [ht, Int.mul_ediv_cancel_left _ hNZ]
    have harg : -(Real.pi * Complex.I * (S : ℂ) / N) = (t : ℂ) * (-(Real.pi * Complex.I)) := by
      rw [hS]
      field_simp
      ring
    rw [hdiv, harg, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg_one]
    ring
  · simp

end Fabius
