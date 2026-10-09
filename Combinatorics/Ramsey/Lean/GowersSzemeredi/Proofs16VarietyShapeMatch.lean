import GowersSzemeredi.Proofs16VarietyLossPower
import GowersSzemeredi.Proofs16VarietyControlAbsorption

/-! The ceiling-free controls have the absorbed variety shape.

`MultiplyLinearWith.multiplyLinear_of_variety_shape` takes controls of the form
* width `≥ W·(γ/(2r))^(18b)·(ρ/4)^(17+18b)`,
* count `≤ max (81·Q²·7⁴·((2r/γ)^b·(4/ρ)^(1+b))⁴) 27`,

with `b = M·r`, `M = multipleCExponent 3`. This module shows that the controls
`section16VarietyCeilingFreeExponent` and `section16VarietyCeilingFreeGraphBound`
of `Proofs16VarietyCeilingFreeCover` have exactly this form. Here `r` is the
Lemma 16.9 scale and `W` is the explicit `ρ`-free factor
`section16VarietyCeilingFreeWidthCoeff`. Both use
`section16_variety_line_factor_power`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The `ρ`-free factor of the ceiling-free width exponent. -/
def section16VarietyCeilingFreeWidthCoeff (C p Cv pv D Q q : Nat) (c theta gamma E : Real) : Real :=
  E / (8 * (p : Real) * ((q : Real) + 1) ^ 16) /
    (1024 * (pv : Real) ^ 2 * (4 * Cv + 18) * (milicevicBound D c + 2) ^ 17 *
      (7 ^ 17 * ((Q : Real) + 1) ^ 17)) /
    (16 + 4 * Real.log (16 / (section16Zeta (theta / 2) gamma 2 /
      (4 * ((C * (q + 1) : Nat) : Real)))))

/-- **The ceiling-free width exponent in the absorbed shape.** -/
theorem section16VarietyCeilingFreeExponent_eq_shape (C p Cv pv D Q q : Nat)
    {c theta gamma E rho : Real} (hr : 0 < section16Lemma9R (theta / 2) gamma 2)
    (hrho : 0 < rho) (hg : 0 < gamma) :
    section16VarietyCeilingFreeExponent C p Cv pv D Q q c theta gamma E rho =
      section16VarietyCeilingFreeWidthCoeff C p Cv pv D Q q c theta gamma E *
        (gamma / (2 * section16Lemma9R (theta / 2) gamma 2)) ^
          (18 * (multipleCExponent 3 * section16Lemma9R (theta / 2) gamma 2)) *
        (rho / 4) ^ (17 + 18 * (multipleCExponent 3 * section16Lemma9R (theta / 2) gamma 2)) := by
  have hloss := section16_variety_loss_factor_power hr (by positivity : 0 < rho / 4) hg
  simp only at hloss
  unfold section16VarietyCeilingFreeExponent section16VarietyCeilingFreeWidthCoeff
  simp only
  rw [show multipleCExponent 3 = (((2 : Nat) ^ ((2 : Nat) ^ (3 + 8)) : Nat) : Real) from rfl,
    mul_assoc _ ((gamma / (2 * section16Lemma9R (theta / 2) gamma 2)) ^ _), ← hloss]
  generalize (multipleC (rho / 4 / (2 * section16Lemma9R (theta / 2) gamma 2)) gamma 3) ^
    section16Lemma9R (theta / 2) gamma 2 = u
  ring

/-- **The ceiling-free graph count in the absorbed shape.** -/
theorem section16VarietyCeilingFreeGraphBound_eq_shape (Q : Nat) {theta gamma rho : Real}
    (hr : 0 < section16Lemma9R (theta / 2) gamma 2) (hrho : 0 < rho) (hg : 0 < gamma) :
    section16VarietyCeilingFreeGraphBound Q theta gamma rho =
      max (81 * (Q : Real) ^ 2 * 7 ^ 4 *
        ((2 * section16Lemma9R (theta / 2) gamma 2 / gamma) ^
            (multipleCExponent 3 * section16Lemma9R (theta / 2) gamma 2) *
          (4 / rho) ^ (1 + multipleCExponent 3 * section16Lemma9R (theta / 2) gamma 2)) ^ 4) 27 := by
  have hline := section16_variety_line_factor_power hr (by positivity : 0 < rho / 4) hg
  simp only at hline
  unfold section16VarietyCeilingFreeGraphBound
  simp only
  rw [hline, show (((2 : Nat) ^ ((2 : Nat) ^ (3 + 8)) : Nat) : Real) = multipleCExponent 3 from rfl]
  generalize section16Lemma9R (theta / 2) gamma 2 = r at hr ⊢
  generalize multipleCExponent 3 * r = b
  have hR : 0 < 2 * r / gamma := by positivity
  have h4 : 0 < rho / 4 := by positivity
  -- `7 / ((ρ/4)·((γ/(2r))^b·(ρ/4)^b)) = 7·(2r/γ)^b·(4/ρ)^(1+b)`
  have hkey : 7 / (rho / 4 * ((gamma / (2 * r)) ^ b * (rho / 4) ^ b)) =
      7 * ((2 * r / gamma) ^ b * (4 / rho) ^ (1 + b)) := by
    have e1 : gamma / (2 * r) = (2 * r / gamma)⁻¹ := by rw [inv_div]
    have e2 : rho / 4 = (4 / rho)⁻¹ := by rw [inv_div]
    rw [e1, e2, Real.inv_rpow hR.le, Real.inv_rpow (by positivity),
      Real.rpow_add (by positivity), Real.rpow_one]
    field_simp
  rw [hkey]
  congr 1
  ring

end LeanProofs.GowersSzemeredi
