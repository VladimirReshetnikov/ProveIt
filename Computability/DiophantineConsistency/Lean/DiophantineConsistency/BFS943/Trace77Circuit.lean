import DiophantineConsistency.BFS943.Trace76Circuit

/-! # The ten-positive 77-operation, degree-348 trace equation

Package 171 (`con-zfc-diophantine-forms/171-pooled-powers-separated-radicals`),
`positive/q4_interpolation/equation.json`: chart `q4`, weight `L = bV`. It has
the ten unknowns and four ports of the 75/76 circuits and the rows of the
76/352 circuit, except that the denominator `D = XY` of the carrier and of
`M` is replaced by the new row `q4 = q2 * q2`, i.e. `D = q⁴`. (`XY` stays
in the graph: it is still used by `Am1` and `V0k`.)

`value77` reuses the 75 register map `regs` for every row other than `D`,
`Z` and `M`, and spells those out. Since `XY = (w s) q⁴`, the 75 multiplier
`M = h XY H` is `w s` times the 77 multiplier `h q⁴ H`; hence
(`norm_scaled`)

  `normValue (regs p v) (w s Z77) = (w s)² value77`,

so the root extraction of `TraceNormRoots` applies at the carrier `w s Z77`.
`value75_shift` and `value77_shift` are the two ring identities of the
soundness and completeness maps (`Trace77ToTrace75`, `Trace77FromTrace76`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace77
open DiophantineConsistency.TenPositiveTrace75 DiophantineConsistency.TenPositiveTrace76

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]

/-- The 77 carrier `Z = hD (H (n - L B) + K) - H (D B + h e)`, `D = q⁴`, `L = b V`. -/
def Z77 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let L := r.b * r.V
  let D := r.q * r.q * (r.q * r.q)
  r.h * D * (r.H * (v 7 - L * r.B) + r.K) - r.H * (D * r.B + r.h * r.e)

/-- The 77 multiplier `M = h q⁴ H`. -/
def M77 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.h * (r.q * r.q * (r.q * r.q)) * r.H

/-- The value of the 77-operation circuit (its output row `N`). -/
def value77 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let L := r.b * r.V
  let D := r.q * r.q * (r.q * r.q)
  let Z := r.h * D * (r.H * (v 7 - L * r.B) + r.K) - r.H * (D * r.B + r.h * r.e)
  let M := r.h * D * r.H
  r.Q * (Z * Z - M * M * r.Gn * (r.V * r.V)) + (M * M * r.Gn - Z * Z)

theorem value77_def (p : Fin 4 → R) (v : Fin 10 → R) :
    value77 p v = (regs p v).Q * (Z77 p v * Z77 p v - M77 p v * M77 p v * (regs p v).Gn *
      ((regs p v).V * (regs p v).V)) + (M77 p v * M77 p v * (regs p v).Gn - Z77 p v * Z77 p v) :=
  rfl

theorem Z77_def (p : Fin 4 → R) (v : Fin 10 → R) :
    Z77 p v = (regs p v).h * ((regs p v).q * (regs p v).q * ((regs p v).q * (regs p v).q)) *
      ((regs p v).H * (v 7 - (regs p v).b * (regs p v).V * (regs p v).B) + (regs p v).K) -
      (regs p v).H * ((regs p v).q * (regs p v).q * ((regs p v).q * (regs p v).q) * (regs p v).B +
        (regs p v).h * (regs p v).e) := rfl

theorem M77_def (p : Fin 4 → R) (v : Fin 10 → R) :
    M77 p v = (regs p v).h * ((regs p v).q * (regs p v).q * ((regs p v).q * (regs p v).q)) *
      (regs p v).H := rfl

end Generic

section Ring
variable {R : Type*} [CommRing R]

/-- `M75 = (w s) M77`. -/
theorem M_scaled (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p v).M = v 5 * v 6 * M77 p v := by
  rw [M_def, X_def, Y_def, M77_def]
  ring

/-- The 75 output at the carrier `w s Z77` is `(w s)²` times the 77 output. -/
theorem norm_scaled (p : Fin 4 → R) (v : Fin 10 → R) :
    normValue (regs p v) (v 5 * v 6 * Z77 p v) = (v 5 * v 6) * (v 5 * v 6) * value77 p v := by
  rw [value77_def, normValue, M_scaled]
  ring

/-- `w s Z77` is the 76-shape carrier with offset `w s e` instead of `e`. -/
theorem scaled_shape (p : Fin 4 → R) (v : Fin 10 → R) :
    v 5 * v 6 * Z77 p v = (regs p v).h * (regs p v).D *
      ((regs p v).H * (v 7 - (regs p v).b * (regs p v).V * (regs p v).B) + (regs p v).K) -
      (regs p v).H * ((regs p v).D * (regs p v).B + (regs p v).h * (v 5 * v 6 * (regs p v).e)) := by
  rw [Z77_def, D_def, X_def, Y_def]
  ring

/-- Soundness map. If `e = XY ρ` and `w s Z77 = M z`, moving `n` to
`n + (V² - bV) B - (w s - 1) ρ + δ` makes the 75 carrier `M (z + δ)`. -/
theorem Z75_shift (p : Fin 4 → R) (v : Fin 10 → R) (rho z d x : R)
    (he : (regs p v).e = (regs p v).X * (regs p v).Y * rho)
    (hz : v 5 * v 6 * Z77 p v = (regs p v).M * z)
    (hx : x = v 7 + ((regs p v).V * (regs p v).V - (regs p v).b * (regs p v).V) * (regs p v).B -
      (v 5 * v 6 - 1) * rho + d) :
    (regs p (Function.update v 7 x)).Z = (regs p v).M * (z + d) := by
  have hZ : (regs p (Function.update v 7 x)).Z = (regs p v).h * ((regs p v).X * (regs p v).Y) *
      ((regs p v).H * (x - (regs p v).V * (regs p v).V * (regs p v).B) + (regs p v).K) -
      (regs p v).H * ((regs p v).X * (regs p v).Y * (regs p v).B + (regs p v).h * (regs p v).e) := rfl
  have hM : (regs p v).M = (regs p v).h * ((regs p v).X * (regs p v).Y) * (regs p v).H := M_def p v
  have hS := scaled_shape p v
  rw [D_def] at hS
  rw [hZ, hx, he]
  rw [hM] at hz ⊢
  rw [he] at hS
  linear_combination hz - hS

/-- The 75 output only sees the square of the carrier. -/
theorem value75_of_carrier_sq (p : Fin 4 → R) (v : Fin 10 → R) (x Z : R)
    (hsq : (regs p (Function.update v 7 x)).Z * (regs p (Function.update v 7 x)).Z = Z * Z) :
    value75 p (Function.update v 7 x) = normValue (regs p v) Z := by
  rw [value75_norm]
  have hQ : (regs p (Function.update v 7 x)).Q = (regs p v).Q := rfl
  have hM : (regs p (Function.update v 7 x)).M = (regs p v).M := rfl
  have hG : (regs p (Function.update v 7 x)).Gn = (regs p v).Gn := rfl
  have hV : (regs p (Function.update v 7 x)).V = (regs p v).V := rfl
  simp only [normValue, hQ, hM, hG, hV, hsq]

/-- Completeness map. If `e = XY ρ`, moving `n` up by `(w s - 1) ρ` turns the
76 carrier into `w s` times the 77 carrier. -/
theorem value77_shift (p : Fin 4 → R) (v : Fin 10 → R) (rho x : R)
    (he : (regs p v).e = (regs p v).X * (regs p v).Y * rho)
    (hx : x = v 7 + (v 5 * v 6 - 1) * rho) :
    (v 5 * v 6) * (v 5 * v 6) * value77 p (Function.update v 7 x) = value76 p v := by
  have h5 : Function.update v 7 x 5 = v 5 := rfl
  have h6 : Function.update v 7 x 6 = v 6 := rfl
  have hn : Function.update v 7 x 7 = x := rfl
  have hS := scaled_shape p (Function.update v 7 x)
  rw [h5, h6, hn] at hS
  have hsame : v 5 * v 6 * Z77 p (Function.update v 7 x) = Z76 p v := by
    rw [hS, Z76_def]
    change (regs p v).h * ((regs p v).X * (regs p v).Y) *
        ((regs p v).H * (x - (regs p v).b * (regs p v).V * (regs p v).B) + (regs p v).K) -
        (regs p v).H * ((regs p v).X * (regs p v).Y * (regs p v).B +
          (regs p v).h * (v 5 * v 6 * (regs p v).e)) = _
    rw [D_def, hx, he]
    ring
  have hN := norm_scaled p (Function.update v 7 x)
  rw [h5, h6] at hN
  rw [← hN, hsame, value76_norm]
  rfl

end Ring

end DiophantineConsistency.TenPositiveTrace77
