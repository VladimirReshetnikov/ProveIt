import GowersSzemeredi.Proofs16VarietyCeilingFreeCover

/-! The remaining inner-loss dependence is a single real power. Its
exponent depends only on the outer density parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Separate the inner loss from the line factor without evaluating the
large natural exponent in `multipleC`. -/
theorem section16_variety_line_factor_power {r sigma gamma : Real}
    (hr : 0 < r) (hs : 0 < sigma) (hg : 0 < gamma) :
    let b := (((2 : Nat) ^ ((2 : Nat) ^ (3 + 8)) : Nat) : Real) * r
    (multipleC (sigma / (2 * r)) gamma 3)^r =
      (gamma / (2 * r))^b * sigma^b := by
  intro b
  unfold multipleC
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [show gamma * (sigma / (2 * r)) = (gamma / (2 * r)) * sigma by ring]
  exact Real.mul_rpow (by positivity) hs.le

/-- The exact inner-loss factor is a fixed coefficient times
`sigma^(17+18*b)`, where `b` is independent of `sigma`. -/
theorem section16_variety_loss_factor_power {r sigma gamma : Real}
    (hr : 0 < r) (hs : 0 < sigma) (hg : 0 < gamma) :
    let b := (((2 : Nat) ^ ((2 : Nat) ^ (3 + 8)) : Nat) : Real) * r
    let u := (multipleC (sigma / (2 * r)) gamma 3)^r
    u * (sigma * u)^17 = (gamma / (2 * r))^(18 * b) * sigma^(17 + 18 * b) := by
  intro b u
  have hu := section16_variety_line_factor_power hr hs hg
  change u = (gamma / (2 * r))^b * sigma^b at hu
  rw [hu]
  calc
    _ = ((gamma / (2 * r))^b)^18 * (sigma^17 * (sigma^b)^18) := by ring
    _ = (gamma / (2 * r))^(b * (18 : Real)) * (sigma^(17 : Real) * sigma^(b * (18 : Real))) := by
      rw [Real.rpow_mul (by positivity : 0 ≤ gamma / (2 * r)) b 18,
        Real.rpow_mul hs.le b 18]
      simp only [show (18 : Real) = ((18 : Nat) : Real) by rfl,
        show (17 : Real) = ((17 : Nat) : Real) by rfl, Real.rpow_natCast]
    _ = _ := by rw [← Real.rpow_add hs]; congr 2 <;> ring

end LeanProofs.GowersSzemeredi
