import DiophantineConsistency.BFS943.Centred87Regs

/-! # Root scale two on the 87/214 registers (package 194)

Package 194 (`194-guarded-resultants-early-projection/positive`) keeps the
87/214 free-inverse registers (package 172) and changes two things: a centre
term moves the carrier, and the norm has root scale `r = 2`,

  `P = Q (Z² - 4 M² G V²) + (4 M² G - Z²)`.

`scaledNorm r Z` is this polynomial at a register map `r` and carrier `Z`
(`G = Gn`). Identically `scaledNorm r (2 Z') = 4 normValue r Z'`
(`scaledNorm_two`), so an even carrier reduces to the 87 norm.

`regsW p v ws` is the 87 register map with the transport gate
`n - b V B - ws` (an arbitrary shift `ws`, used by the `product2` circuit);
`Z_shift` says its carrier is `Z₈₇ - M ws`. The `quotient_t` circuit uses the
centred gate `n - V (b B + g)` of `TenPositiveCentred87.regsAt` instead.
`Z_update` is the dependence of the 87 carrier on `n`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveScaled87
open DiophantineConsistency.TenPositiveTrace75 (Regs)

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 6]

/-- The root-scale-two norm polynomial `Q (Z² - 4 M² G V²) + (4 M² G - Z²)`. -/
def scaledNorm (r : Regs R) (Z : R) : R :=
  r.Q * (Z * Z - r.M * r.M * (4 * r.Gn) * (r.V * r.V)) + (r.M * r.M * (4 * r.Gn) - Z * Z)

/-- The 87 registers with the transport gate `n - b V B - ws`. -/
def regsW (p : Fin 4 → R) (v : Fin 10 → R) (ws : R) : Regs R :=
  let r := TenPositiveTrace87.regs p v
  { r with Z := r.h * r.D * (r.H * (v 7 - r.b * r.V * r.B - ws) + r.K) -
                r.H * (r.D * r.B + r.h * TenPositiveTrace87.ecl p v) }

theorem regsW_Z_def (p : Fin 4 → R) (v : Fin 10 → R) (ws : R) :
    (regsW p v ws).Z = (TenPositiveTrace87.regs p v).h * (TenPositiveTrace87.regs p v).D *
      ((TenPositiveTrace87.regs p v).H * (v 7 - (TenPositiveTrace87.regs p v).b *
        (TenPositiveTrace87.regs p v).V * (TenPositiveTrace87.regs p v).B - ws) +
        (TenPositiveTrace87.regs p v).K) -
      (TenPositiveTrace87.regs p v).H * ((TenPositiveTrace87.regs p v).D *
        (TenPositiveTrace87.regs p v).B +
        (TenPositiveTrace87.regs p v).h * TenPositiveTrace87.ecl p v) := rfl

end Generic

variable {R : Type*} [CommRing R]

theorem scaledNorm_two (r : Regs R) (Z : R) :
    scaledNorm r (2 * Z) = 4 * TenPositiveTrace76.normValue r Z := by
  simp only [scaledNorm, TenPositiveTrace76.normValue]
  ring

theorem scaledNorm_eq (r : Regs R) (Z : R) :
    scaledNorm r Z = (r.Q - 1) * Z ^ 2 - 4 * (r.M ^ 2 * r.Gn * (r.Q * r.V ^ 2 - 1)) := by
  simp only [scaledNorm]
  ring

theorem normValue_neg (r : Regs R) (Z : R) :
    TenPositiveTrace76.normValue r (-Z) = TenPositiveTrace76.normValue r Z := by
  simp only [TenPositiveTrace76.normValue]
  ring

/-- The shifted carrier is the 87 carrier minus `M ws`. -/
theorem regsW_Z_shift (p : Fin 4 → R) (v : Fin 10 → R) (ws : R) :
    (regsW p v ws).Z = (TenPositiveTrace87.regs p v).Z - (TenPositiveTrace87.regs p v).M * ws := by
  rw [regsW_Z_def, TenPositiveTrace87.Z_def, TenPositiveTrace87.M_def]
  ring

/-- Changing `n` moves the 87 carrier by `M` times the change. -/
theorem Z_update (p : Fin 4 → R) (v : Fin 10 → R) (x : R) :
    (TenPositiveTrace87.regs p (Function.update v 7 x)).Z =
      (TenPositiveTrace87.regs p v).Z + (TenPositiveTrace87.regs p v).M * (x - v 7) := by
  set v' := Function.update v 7 x with hv'
  have h7 : v' 7 = x := Function.update_self _ _ _
  have hh : (TenPositiveTrace87.regs p v').h = (TenPositiveTrace87.regs p v).h := rfl
  have hD : (TenPositiveTrace87.regs p v').D = (TenPositiveTrace87.regs p v).D := rfl
  have hH : (TenPositiveTrace87.regs p v').H = (TenPositiveTrace87.regs p v).H := rfl
  have hb : (TenPositiveTrace87.regs p v').b = (TenPositiveTrace87.regs p v).b := rfl
  have hV : (TenPositiveTrace87.regs p v').V = (TenPositiveTrace87.regs p v).V := rfl
  have hB : (TenPositiveTrace87.regs p v').B = (TenPositiveTrace87.regs p v).B := rfl
  have hK : (TenPositiveTrace87.regs p v').K = (TenPositiveTrace87.regs p v).K := rfl
  have he : TenPositiveTrace87.ecl p v' = TenPositiveTrace87.ecl p v := rfl
  rw [TenPositiveTrace87.Z_def, TenPositiveTrace87.Z_def, h7, hh, hD, hH, hb, hV, hB, hK, he,
    TenPositiveTrace87.M_def]
  ring

end DiophantineConsistency.TenPositiveScaled87
