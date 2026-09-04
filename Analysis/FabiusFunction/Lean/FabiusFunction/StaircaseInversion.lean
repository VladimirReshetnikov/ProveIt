import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Staircase recovery: the generalized inverse of a monotone sequence

The transseries volume's `p0:thm:staircase` describes how the *integer*
generalized inverse `N_*(y) = min {n : A_n ≥ y}` of a monotone sequence relates
to the *real* inverse `ν(y)` of an admissible interpolation.  Its five parts are
exact rounding, a separation condition, the unconditional case along the range,
a residue-class refinement, and the statement that no continuous function
represents `N_*` to better than `1/2`.

Everything here is order theory and one application of the intermediate value
theorem; the analytic content of the volume's chapter is entirely in producing
the interpolation, and none of it is needed to state or prove these.
Accordingly the interpolation is reduced to its two working hypotheses:
`StrictMono A` and `A ν = y`.

## Main results

* `Fabius.isLeast_ceil`: `⌈ν⌉` is the least integer `≥ ν`.  This is the whole of
  `p0:eq:ceil-identity` once monotonicity is used to turn `A_n ≥ y` into
  `n ≥ ν(y)`, which is `Fabius.staircase_ceil`.
* `Fabius.staircase_separation`: `p0:eq:separation` — if `|x - ν| ≤ η` and
  `⌈x-η⌉ = ⌈x+η⌉` then `⌈ν⌉` is that common value.
* `Fabius.staircase_separation_fails`: the failure mode is real — for every
  `ε > 0` there are data with `0 < η < ε` for which the separation condition
  fails.  So part (2) genuinely needs its hypothesis.
* `Fabius.staircase_round`: `p0:thm:staircase`(3) — along the range, `η < 1/2`
  suffices and no separation hypothesis is needed.
* `Fabius.isLeast_residue_class`: the arithmetic of `p0:eq:residue-staircase` —
  `ρ + r⌈(ν-ρ)/r⌉` is the least integer `≥ ν` in the class of `ρ` mod `r`.
* `Fabius.exists_half_error_of_jump`: `p0:eq:no-smooth` — across a single unit
  jump, every continuous `g` misses by at least `1/2` somewhere.  This is what
  makes the periodic layer `⌈x⌉ - x - 1/2` a genuine transmonomial rather than a
  refinement that could be dropped.

Not formalized here: the Fourier expansion of that periodic layer, and the
construction of admissible interpolations, which is the analytic part.
-/

set_option autoImplicit false

namespace Fabius

open Set

/-- `⌈ν⌉` is the least integer at or above `ν`. -/
theorem isLeast_ceil (ν : ℝ) : IsLeast {n : ℤ | ν ≤ (n : ℝ)} ⌈ν⌉ :=
  ⟨Int.le_ceil ν, fun _ hn => Int.ceil_le.mpr hn⟩

/-- `p0:eq:ceil-identity`: for a strictly monotone interpolation `A` with
`A ν = y`, the least integer `n` with `y ≤ A n` is `⌈ν⌉`. -/
theorem staircase_ceil {A : ℝ → ℝ} (hA : StrictMono A) {ν y : ℝ} (hν : A ν = y) :
    IsLeast {n : ℤ | y ≤ A (n : ℝ)} ⌈ν⌉ := by
  have hset : {n : ℤ | y ≤ A (n : ℝ)} = {n : ℤ | ν ≤ (n : ℝ)} := by
    ext n
    simp only [mem_setOf_eq, ← hν, hA.le_iff_le]
  rw [hset]
  exact isLeast_ceil ν

/-- `p0:eq:separation`: if the uncertainty interval about `x` does not straddle
an integer, the ceiling is determined. -/
theorem staircase_separation {x η ν : ℝ} (hη : |x - ν| ≤ η)
    (hsep : ⌈x - η⌉ = ⌈x + η⌉) : ⌈ν⌉ = ⌈x + η⌉ := by
  have habs := abs_le.mp hη
  have hlo : x - η ≤ ν := by linarith [habs.2]
  have hhi : ν ≤ x + η := by linarith [habs.1]
  exact le_antisymm (Int.ceil_mono hhi) (hsep ▸ Int.ceil_mono hlo)

/-- The separation condition can fail for arbitrarily small `η`: precisely when
`ν` sits just above an integer.  So the hypothesis of `staircase_separation` is
not removable. -/
theorem staircase_separation_fails {ε : ℝ} (hε : 0 < ε) :
    ∃ x η ν : ℝ, 0 < η ∧ η < ε ∧ |x - ν| ≤ η ∧ ⌈x - η⌉ ≠ ⌈x + η⌉ := by
  have h1 : (0:ℝ) < min (ε / 2) (1 / 2) := by positivity
  have h2 : min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  refine ⟨0, min (ε / 2) (1 / 2), 0, h1, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · rw [sub_zero, abs_zero]
    linarith
  · rw [zero_sub, zero_add]
    have hne : ⌈-min (ε / 2) (1 / 2)⌉ = 0 := by
      rw [Int.ceil_eq_iff]
      push_cast
      exact ⟨by linarith, by linarith⟩
    have hpos : ⌈min (ε / 2) (1 / 2)⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      push_cast
      exact ⟨by linarith, by linarith⟩
    rw [hne, hpos]
    exact zero_ne_one

/-- `p0:thm:staircase`(3): along the range the answer is unconditional — an
approximation with error below `1/2` rounds to the exact index. -/
theorem staircase_round {x η : ℝ} {n : ℤ} (hη : η < 1 / 2)
    (h : |x - (n : ℝ)| ≤ η) : ⌊x + 1 / 2⌋ = n := by
  have habs := abs_le.mp h
  rw [Int.floor_eq_iff]
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

/-- The arithmetic of `p0:eq:residue-staircase`: the least integer at or above
`ν` lying in the residue class of `ρ` modulo `r` is `ρ + r⌈(ν - ρ)/r⌉`. -/
theorem isLeast_residue_class {r ρ : ℤ} (hr : 0 < r) (ν : ℝ) :
    IsLeast {n : ℤ | ν ≤ (n : ℝ) ∧ r ∣ n - ρ}
      (ρ + r * ⌈(ν - (ρ : ℝ)) / (r : ℝ)⌉) := by
  have hrR : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr
  set k : ℤ := ⌈(ν - (ρ : ℝ)) / (r : ℝ)⌉ with hk
  constructor
  · refine ⟨?_, ⟨k, by ring⟩⟩
    have h1 : (ν - (ρ : ℝ)) / (r : ℝ) ≤ (k : ℝ) := Int.le_ceil _
    have h2 : ν - (ρ : ℝ) ≤ (r : ℝ) * (k : ℝ) := by
      rw [div_le_iff₀ hrR] at h1
      linarith
    push_cast
    linarith
  · rintro n ⟨hn, j, hj⟩
    have hnj : n = ρ + r * j := by omega
    have h1 : ν ≤ (ρ : ℝ) + (r : ℝ) * (j : ℝ) := by
      rw [hnj] at hn
      push_cast at hn
      linarith
    have h2 : (ν - (ρ : ℝ)) / (r : ℝ) ≤ (j : ℝ) := by
      rw [div_le_iff₀ hrR]
      linarith
    have h3 : k ≤ j := Int.ceil_le.mpr h2
    have : r * k ≤ r * j := by
      exact mul_le_mul_of_nonneg_left h3 (le_of_lt hr)
    omega

private theorem half_le_abs_sub_half (j : ℤ) : (1:ℝ) / 2 ≤ |(j : ℝ) - 1 / 2| := by
  by_cases h : j ≤ 0
  · have hj : (j : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1 : (1:ℤ) ≤ j := by omega
    have hj : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast h1
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- `p0:eq:no-smooth`: across a single unit jump of an integer-valued staircase,
any continuous `g` is off by at least `1/2` somewhere.  The intermediate value
theorem forces `g` to pass through the half-integer, where every integer value
is at distance at least `1/2`. -/
theorem exists_half_error_of_jump {a b : ℝ} (hab : a ≤ b) {N : ℝ → ℤ} {g : ℝ → ℝ}
    {m : ℤ} (hNa : N a = m) (hNb : N b = m + 1) (hg : ContinuousOn g (Icc a b)) :
    ∃ c ∈ Icc a b, (1:ℝ) / 2 ≤ |(N c : ℝ) - g c| := by
  by_contra hcon
  push Not at hcon
  have ha : g a < (m : ℝ) + 1 / 2 := by
    have h := hcon a (left_mem_Icc.mpr hab)
    rw [hNa] at h
    have := (abs_lt.mp h).1
    linarith
  have hb : (m : ℝ) + 1 / 2 < g b := by
    have h := hcon b (right_mem_Icc.mpr hab)
    rw [hNb] at h
    push_cast at h
    have := (abs_lt.mp h).2
    linarith
  obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc hab hg ⟨ha.le, hb.le⟩
  have hlt := hcon c hc
  rw [hgc] at hlt
  have hge : (1:ℝ) / 2 ≤ |(N c : ℝ) - ((m : ℝ) + 1 / 2)| := by
    have h := half_le_abs_sub_half (N c - m)
    push_cast at h
    have hrw : ((N c : ℝ) - (m : ℝ)) - 1 / 2 = (N c : ℝ) - ((m : ℝ) + 1 / 2) := by ring
    rwa [hrw] at h
  linarith

end Fabius
