import FabiusFunction.PeakRayEnvelope

/-!
# The exponent dictionary `Λ ↦ κ(Λ)`

Every decay exponent of the audits' spectrum comes from one mean:
a per-shell rate `Λ` of the lacunary sine product produces the
frequency exponent

`κ(Λ) = 1/2 + log(π/Λ)/log 2`,

by the shell bookkeeping of `shell_exponent_identity`.  The dictionary
is a single strictly decreasing function of `Λ`, and the audits' three
named exponents are its values at three explicit means:

| mean `Λ` | exponent |
| --- | --- |
| `1/2` (the trivial rate) | `κ₀ = 3/2 + log₂π = 3.1515…` |
| `ϱ₁ = 0.66132…` (the Perron root) | `κ₁ = 2.7481…` |
| `√2/2` (the `L²`/RMS rate) | `κ₂ = 1 + log₂π = log₂(2π) = 2.6515…` |
| `√3/2` (the sharp Gelfond rate) | `κ∞ = 2.3590…` |

One formula reproduces all four constants reported by the audits, and gives
`κ∞ < κ₂ < κ₀`, with the exact gaps `κ₀ − κ₂ = 1/2`,
`κ₀ − κ∞ = log 3/(2 log 2)` and `κ₂ − κ∞ = (log 3 − log 2)/(2 log 2)`.
A smaller mean means slower decay: the dictionary is *anti*-tone, which
is why the sharp (largest) mean `√3/2` gives the extremal (smallest)
exponent `κ∞` of `GlobalDecayEnvelope`.

Note that `κ₁` cannot be a definition here: the Perron root is
available only existentially (`exists_perron_root`), so statements
about it stay hypothesis-carrying.

* `kappaOf` — the dictionary.
* `kappaOf_half`, `kappaOf_sqrt_two`, `kappaOf_sqrt_three` — values.
* `kappaOf_strictAntiOn` — strict antitonicity.
* `kappa_zero_sub_kappa_two`, … — the exact gaps and the ordering.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- **The exponent dictionary**: a per-shell mean `Λ` yields the decay
exponent `κ(Λ) = 1/2 + log(π/Λ)/log 2`. -/
noncomputable def kappaOf (Λ : ℝ) : ℝ :=
  1 / 2 + Real.log (π / Λ) / Real.log 2

/-- The natural logarithm of two is positive. -/
theorem log_two_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- Expanded form of the dictionary at a positive mean. -/
theorem kappaOf_eq {Λ : ℝ} (hΛ : 0 < Λ) :
    kappaOf Λ = 1 / 2 + (Real.log π - Real.log Λ) / Real.log 2 := by
  rw [kappaOf, Real.log_div Real.pi_ne_zero (ne_of_gt hΛ)]

/-- **Strict antitonicity**: a larger mean gives a smaller exponent. -/
theorem kappaOf_strictAntiOn : StrictAntiOn kappaOf (Set.Ioi (0:ℝ)) := by
  intro a ha b hb hab
  rw [kappaOf_eq (Set.mem_Ioi.mp ha), kappaOf_eq (Set.mem_Ioi.mp hb)]
  have hlog : Real.log a < Real.log b :=
    Real.log_lt_log (Set.mem_Ioi.mp ha) hab
  have hinv : (0:ℝ) < (Real.log 2)⁻¹ := inv_pos.mpr log_two_pos
  have h2 : (Real.log π - Real.log b) * (Real.log 2)⁻¹ <
      (Real.log π - Real.log a) * (Real.log 2)⁻¹ :=
    mul_lt_mul_of_pos_right (by linarith) hinv
  simp only [div_eq_mul_inv]
  linarith

/-- The `L¹`-trivial mean `Λ = 1/2` gives `κ₀ = 3/2 + log₂π`. -/
theorem kappaOf_half :
    kappaOf (1/2) = 3 / 2 + Real.log π / Real.log 2 := by
  have hl2 := log_two_pos
  rw [kappaOf_eq (by norm_num), show (1/2 : ℝ) = 2⁻¹ by norm_num,
    Real.log_inv]
  field_simp
  ring

/-- The RMS mean `Λ = √2/2` gives `κ₂ = 1 + log₂π = log₂(2π)`. -/
theorem kappaOf_sqrt_two :
    kappaOf (Real.sqrt 2 / 2) = 1 + Real.log π / Real.log 2 := by
  have hl2 := log_two_pos
  have hs : Real.log (Real.sqrt 2 / 2) = -(Real.log 2 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [kappaOf_eq (by positivity), hs]
  field_simp
  ring

/-- The sharp Gelfond mean `Λ = √3/2` gives the extremal `κ∞`. -/
theorem kappaOf_sqrt_three :
    kappaOf (Real.sqrt 3 / 2) = kappaInf := by
  have hl2 := log_two_pos
  have hs : Real.log (Real.sqrt 3 / 2) =
      Real.log 3 / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hps : Real.log (π / Real.sqrt 3) =
      Real.log π - Real.log 3 / 2 := by
    rw [Real.log_div Real.pi_ne_zero (by positivity),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [kappaOf_eq (by positivity), hs, kappaInf, hps]
  field_simp
  ring

/-! ## The exact gaps -/

/-- The trivial-rate exponent exceeds the root-mean-square exponent by
exactly one half. -/
theorem kappa_zero_sub_kappa_two :
    kappaOf (1/2) - kappaOf (Real.sqrt 2 / 2) = 1 / 2 := by
  rw [kappaOf_half, kappaOf_sqrt_two]
  ring

/-- The gap from the trivial-rate exponent to the sharp Gelfond exponent is
`log 3 / (2 log 2)`. -/
theorem kappa_zero_sub_kappa_inf :
    kappaOf (1/2) - kappaInf = Real.log 3 / (2 * Real.log 2) := by
  have hl2 := log_two_pos
  rw [kappaOf_half, kappaInf,
    Real.log_div Real.pi_ne_zero (by positivity),
    Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  field_simp
  ring

/-- The gap from the root-mean-square exponent to the sharp Gelfond exponent
is `(log 3 - log 2) / (2 log 2)`. -/
theorem kappa_two_sub_kappa_inf :
    kappaOf (Real.sqrt 2 / 2) - kappaInf =
      (Real.log 3 - Real.log 2) / (2 * Real.log 2) := by
  have hl2 := log_two_pos
  rw [kappaOf_sqrt_two, kappaInf,
    Real.log_div Real.pi_ne_zero (by positivity),
    Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  field_simp
  ring

/-! ## Where `κ₁` sits

The audits' `κ₁` is `κ(ϱ₁)` at the Perron root.  `ϱ₁` is available
only existentially, but `exists_perron_root` brackets it in
`[1/2, √2/2]`, and antitonicity turns that bracket into a bracket for
the exponent: `κ₂ ≤ κ₁ ≤ κ₀`.  Numerically
`ϱ₁ = 0.66132…` gives `κ₁ = 2.7481…`, between `κ₂ = 2.6515…` and
`κ₀ = 3.1515…`, exactly as the audits report. -/

/-- The non-strict form of antitonicity. -/
theorem kappaOf_antitoneOn : AntitoneOn kappaOf (Set.Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | h
  · exact le_rfl
  · exact (kappaOf_strictAntiOn hx hy h).le

/-- **The exponent bracket for any Perron-type rate**: a mean in
`[1/2, √2/2]` — which is where `exists_perron_root` puts `ϱ₁` — has
exponent between `κ₂` and `κ₀`. -/
theorem kappaOf_mem_of_mem_perron_bracket {ρ : ℝ}
    (hlow : (1:ℝ)/2 ≤ ρ) (hhigh : ρ ≤ Real.sqrt 2 / 2) :
    kappaOf (Real.sqrt 2 / 2) ≤ kappaOf ρ ∧ kappaOf ρ ≤ kappaOf (1/2) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le (by norm_num) hlow
  have hs2 : (0:ℝ) < Real.sqrt 2 / 2 := by positivity
  exact ⟨kappaOf_antitoneOn (Set.mem_Ioi.mpr hρ0)
      (Set.mem_Ioi.mpr hs2) hhigh,
    kappaOf_antitoneOn (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr hρ0) hlow⟩

/-- **The ordering of the spectrum**: `κ∞ < κ₂ < κ₀`. -/
theorem kappaInf_lt_kappa_two :
    kappaInf < kappaOf (Real.sqrt 2 / 2) := by
  have hl2 := log_two_pos
  have hgap := kappa_two_sub_kappa_inf
  have hlt : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hpos : 0 < (Real.log 3 - Real.log 2) / (2 * Real.log 2) := by
    apply div_pos (by linarith)
    linarith
  linarith

/-- The root-mean-square exponent is strictly smaller than the trivial-rate
exponent. -/
theorem kappa_two_lt_kappa_zero :
    kappaOf (Real.sqrt 2 / 2) < kappaOf (1/2) := by
  have h := kappa_zero_sub_kappa_two
  linarith

end Fabius
