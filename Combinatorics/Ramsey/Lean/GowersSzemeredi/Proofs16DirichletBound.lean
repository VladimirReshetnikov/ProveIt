import GowersSzemeredi.Proofs16BohrSpectrum
import GowersSzemeredi.Proofs05PhaseMetric

/-! The Dirichlet-kernel bound in `ℤ/N`: the first brick of [49]'s Proposition 26.

Proposition 26 of arXiv:2109.03093 shows that a large Fourier coefficient of a
weakly regular Bohr set lies in a bounded span. Its proof sandwiches the
Bohr indicator between products of trapezoid functions, whose Fourier
coefficients decay like `1/ξ²`. The basic estimate is the interval sum below.
It uses the corpus's `four_centeredAbs_div_le_phase_norm`
(`Proofs05PhaseMetric`), `|e(ξ) − 1| ≥ 4|ξ|/N`.

* `interval_exponential_sum_le`: for `ξ ≠ 0`, the sum of `e((c+i)ξ)` over
  `i < L` has absolute value at most `N/(2|ξ|)`, by the geometric sum. Here
  `|ξ|` is the centered absolute value. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **Interval sums of characters.** -/
theorem interval_exponential_sum_le {N : Nat} [NeZero N] {ξ : ZMod N} (hξ : ξ ≠ 0)
    (c : ZMod N) (L : Nat) :
    ‖∑ i ∈ Finset.range L, exponential ((c + (i : ZMod N)) * ξ)‖ ≤ N / (2 * (centeredAbs ξ : Real)) := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcpos : (0 : Real) < centeredAbs ξ := by
    have : centeredAbs ξ ≠ 0 := by
      unfold centeredAbs
      rwa [Ne, Int.natAbs_eq_zero, ZMod.valMinAbs_eq_zero]
    exact_mod_cast Nat.pos_of_ne_zero this
  set ω := exponential ξ
  have hsplit : ∑ i ∈ Finset.range L, exponential ((c + (i : ZMod N)) * ξ) =
      exponential (c * ξ) * ∑ i ∈ Finset.range L, ω ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_mul, show exponential (c * ξ + (i : ZMod N) * ξ) =
      exponential (c * ξ) * exponential ((i : ZMod N) * ξ) from
      AddChar.map_add_eq_mul ZMod.stdAddChar _ _]
    congr 1
    rw [← nsmul_eq_mul]
    exact AddChar.map_nsmul_eq_pow ZMod.stdAddChar i ξ
  have hnorm1 : ∀ z : ZMod N, ‖exponential z‖ = 1 := fun z => (ZMod.stdAddChar (N := N)).norm_apply z
  have hgeom : (∑ i ∈ Finset.range L, ω ^ i) * (ω - 1) = ω ^ L - 1 := geom_sum_mul ω L
  have hlow : 4 * (centeredAbs ξ : Real) / N ≤ ‖ω - 1‖ := four_centeredAbs_div_le_phase_norm ξ
  have hω1 : 0 < ‖ω - 1‖ := lt_of_lt_of_le (by positivity) hlow
  have hnum : ‖ω ^ L - 1‖ ≤ 2 := by
    calc ‖ω ^ L - 1‖ ≤ ‖ω ^ L‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hnorm1, one_pow, norm_one]; norm_num
  have hbound : ‖∑ i ∈ Finset.range L, ω ^ i‖ ≤ 2 / ‖ω - 1‖ := by
    rw [le_div_iff₀ hω1, ← norm_mul, hgeom]
    exact hnum
  rw [hsplit, norm_mul, hnorm1, one_mul]
  calc ‖∑ i ∈ Finset.range L, ω ^ i‖ ≤ 2 / ‖ω - 1‖ := hbound
    _ ≤ 2 / (4 * (centeredAbs ξ : Real) / N) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hlow
    _ = N / (2 * (centeredAbs ξ : Real)) := by field_simp; ring

end LeanProofs.GowersSzemeredi
