import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# The leading term of a harmonic increment

The first-order half of the transseries volume's `plt:lem:mot-harmonic`,
the discrete counterpart of "antidifferentiating `t` makes a logarithm".
The volume considers a sequence with

`w_{n+1} = w_n + c₀ + c₁/w_n + O(w_n^{-2})`,  `w_n → +∞`,  `c₀ > 0`,

and concludes `w_n = c₀n + (c₁/c₀)·log n + C + o(1)`.  Formalized here:
the **leading term** `w_n ∼ c₀n`, in the sharp form `w_n / n → c₀`,
together with the general Stolz-type step it rests on.  The logarithmic
correction and the constant `C` are *not* formalized; they need the
Euler–Mascheroni comparison `∑_{k<n} 1/w_k = (1/c₀)log n + C' + o(1)`,
which is a separate piece of work.

* `tendsto_div_atTop_of_tendsto_sub` — **the Stolz step**: if the
  increments of `w` converge, then `w_n / n` converges to the same limit.
  Stated for an arbitrary real sequence; no positivity, monotonicity or
  divergence hypothesis is needed.
* `tendsto_div_atTop_of_harmonic_increment` — the volume's hypothesis
  gives `w_n / n → c₀`.
-/

set_option autoImplicit false

open Filter Topology Asymptotics Finset

namespace Fabius

/-- **The Stolz step.**  If consecutive differences of a real sequence
converge to `c`, then `w n / n → c`.  The telescoped sum of the
increments is `w n - w 0`, so this is Cesàro convergence of the
increments plus `w 0 / n → 0`. -/
theorem tendsto_div_atTop_of_tendsto_sub {w : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n => w (n + 1) - w n) atTop (𝓝 c)) :
    Tendsto (fun n => w n / n) atTop (𝓝 c) := by
  have hces := h.cesaro
  have htel : ∀ n : ℕ, ∑ i ∈ range n, (w (i + 1) - w i) = w n - w 0 :=
    fun n => Finset.sum_range_sub w n
  have hces' : Tendsto (fun n : ℕ => (w n - w 0) / n) atTop (𝓝 c) := by
    refine hces.congr fun n => ?_
    rw [htel n]
    ring
  have hzero : Tendsto (fun n : ℕ => w 0 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (w 0)
  have hsum := hces'.add hzero
  rw [add_zero] at hsum
  refine hsum.congr fun n => ?_
  ring

/-- **The leading term of a harmonic increment.**  Under the volume's
hypothesis — `w` diverges and its increments are `c₀ + c₁/w_n` up to a
term of order `w_n^{-2}` — the sequence grows linearly with slope `c₀`:
`w_n / n → c₀`.  Note that `c₀ > 0` is not needed for this half. -/
theorem tendsto_div_atTop_of_harmonic_increment {w r : ℕ → ℝ} {c₀ c₁ : ℝ}
    (hw : Tendsto w atTop atTop)
    (hrec : ∀ n, w (n + 1) = w n + c₀ + c₁ / w n + r n)
    (hr : r =O[atTop] fun n => (w n)⁻¹ ^ 2) :
    Tendsto (fun n => w n / n) atTop (𝓝 c₀) := by
  have hinv : Tendsto (fun n => (w n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hw
  have hc₁ : Tendsto (fun n => c₁ / w n) atTop (𝓝 0) := by
    have := hinv.const_mul c₁
    rw [mul_zero] at this
    exact this.congr fun n => by rw [div_eq_mul_inv]
  have hsq : Tendsto (fun n => (w n)⁻¹ ^ 2) atTop (𝓝 0) := by
    have := hinv.pow 2
    simpa using this
  have hr0 : Tendsto r atTop (𝓝 0) := hr.trans_tendsto hsq
  refine tendsto_div_atTop_of_tendsto_sub ?_
  have hstep : ∀ n, w (n + 1) - w n = c₀ + (c₁ / w n + r n) := by
    intro n
    rw [hrec n]
    ring
  have hlim : Tendsto (fun n => c₀ + (c₁ / w n + r n)) atTop (𝓝 (c₀ + (0 + 0))) :=
    tendsto_const_nhds.add (hc₁.add hr0)
  rw [add_zero, add_zero] at hlim
  exact hlim.congr fun n => (hstep n).symm

end Fabius
