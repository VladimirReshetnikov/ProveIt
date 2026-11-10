import DiophantineConsistency.BFS943.Trace87Regs

/-! # Centred 87/214 registers (package 179's late front)

Package 179 (`179-affine-horizons-centered-certificates/positive/late172`)
centres package 172's 87/214 free-inverse carrier: with a centre `ĝ` (a
polynomial in the registers, independent of `n`), the transport gate
`n - L B` with `L = b V` becomes `n - V (b B + ĝ)`. So

  `Z = h D [H (n - V (b B + ĝ)) + K] - H [D B + h eclear]`,

all other registers (`Q`, `M`, `Gn`, `V`, …) being those of
`TenPositiveTrace87.regs`. `regsAt p v g` is this register map at an arbitrary
centre value `g`, `valueAt` its norm polynomial. Identically
`Z = Z₈₇ - M (g V)` (`Z_shift`), and `valueAt` is the 87 norm value at the
shifted carrier (`valueAt_norm`). The two published centres are
`(A + 1) U E` (89/210, `Trace89Regs`) and `A U E` (90/206, `Trace90Regs`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveCentred87
open DiophantineConsistency.TenPositiveTrace75 (Regs)

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]
  [OfNat R 6]

/-- The centred 87 registers at centre `g`: only the carrier `Z` changes. -/
def regsAt (p : Fin 4 → R) (v : Fin 10 → R) (g : R) : Regs R :=
  let r := TenPositiveTrace87.regs p v
  { r with Z := r.h * r.D * (r.H * (v 7 - r.V * (r.b * r.B + g)) + r.K) -
                r.H * (r.D * r.B + r.h * TenPositiveTrace87.ecl p v) }

/-- The value of the centred circuit at centre `g` (its output row `N`). -/
def valueAt (p : Fin 4 → R) (v : Fin 10 → R) (g : R) : R :=
  let r := regsAt p v g
  r.Q * (r.Z * r.Z - r.M * r.M * r.Gn * (r.V * r.V)) +
    (r.M * r.M * r.Gn - r.Z * r.Z)

theorem valueAt_norm (p : Fin 4 → R) (v : Fin 10 → R) (g : R) :
    valueAt p v g = TenPositiveTrace76.normValue (TenPositiveTrace87.regs p v) (regsAt p v g).Z :=
  rfl

theorem Z_def (p : Fin 4 → R) (v : Fin 10 → R) (g : R) :
    (regsAt p v g).Z = (TenPositiveTrace87.regs p v).h * (TenPositiveTrace87.regs p v).D *
      ((TenPositiveTrace87.regs p v).H * (v 7 - (TenPositiveTrace87.regs p v).V *
        ((TenPositiveTrace87.regs p v).b * (TenPositiveTrace87.regs p v).B + g)) +
        (TenPositiveTrace87.regs p v).K) -
      (TenPositiveTrace87.regs p v).H * ((TenPositiveTrace87.regs p v).D *
        (TenPositiveTrace87.regs p v).B +
        (TenPositiveTrace87.regs p v).h * TenPositiveTrace87.ecl p v) := rfl

end Generic

variable {R : Type*} [CommRing R]

/-- The centred carrier is the 87 carrier shifted by `M (g V)`. -/
theorem Z_shift (p : Fin 4 → R) (v : Fin 10 → R) (g : R) :
    (regsAt p v g).Z = (TenPositiveTrace87.regs p v).Z -
      (TenPositiveTrace87.regs p v).M * (g * (TenPositiveTrace87.regs p v).V) := by
  rw [Z_def, TenPositiveTrace87.Z_def, TenPositiveTrace87.M_def]
  ring

/-- Moving `n` by `g V` turns an 87 value into the centred value. -/
theorem valueAt_shift (p : Fin 4 → R) (v : Fin 10 → R) (g : R) :
    valueAt p (Function.update v 7 (v 7 + g * (TenPositiveTrace87.regs p v).V)) g =
      TenPositiveTrace87.value87 p v := by
  set v' := Function.update v 7 (v 7 + g * (TenPositiveTrace87.regs p v).V) with hv'
  have hQ : (TenPositiveTrace87.regs p v').Q = (TenPositiveTrace87.regs p v).Q := rfl
  have hM : (TenPositiveTrace87.regs p v').M = (TenPositiveTrace87.regs p v).M := rfl
  have hG : (TenPositiveTrace87.regs p v').Gn = (TenPositiveTrace87.regs p v).Gn := rfl
  have hV : (TenPositiveTrace87.regs p v').V = (TenPositiveTrace87.regs p v).V := rfl
  have hZ : (regsAt p v' g).Z = (TenPositiveTrace87.regs p v).Z := by
    have h7 : v' 7 = v 7 + g * (TenPositiveTrace87.regs p v).V := Function.update_self _ _ _
    have hh : (TenPositiveTrace87.regs p v').h = (TenPositiveTrace87.regs p v).h := rfl
    have hD : (TenPositiveTrace87.regs p v').D = (TenPositiveTrace87.regs p v).D := rfl
    have hH : (TenPositiveTrace87.regs p v').H = (TenPositiveTrace87.regs p v).H := rfl
    have hb : (TenPositiveTrace87.regs p v').b = (TenPositiveTrace87.regs p v).b := rfl
    have hB : (TenPositiveTrace87.regs p v').B = (TenPositiveTrace87.regs p v).B := rfl
    have hK : (TenPositiveTrace87.regs p v').K = (TenPositiveTrace87.regs p v).K := rfl
    have he : TenPositiveTrace87.ecl p v' = TenPositiveTrace87.ecl p v := rfl
    rw [Z_def, TenPositiveTrace87.Z_def, h7, hh, hD, hH, hb, hB, hK, he, hV]
    ring
  rw [valueAt_norm, TenPositiveTrace87.value87_norm]
  simp only [TenPositiveTrace76.normValue]
  rw [hZ, hQ, hM, hG, hV]

end DiophantineConsistency.TenPositiveCentred87
