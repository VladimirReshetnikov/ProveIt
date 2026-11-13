import DiophantineConsistency.TenPositiveTrace75

/-! # The ten-positive 76-operation, degree-352 trace equation

Package 163 (`con-zfc-diophantine-forms/163-trace-radical`), compact chart
`q3`, weight `L = bV`: the circuit `equations/trace76_degree352.json`.
It has the same ten unknowns `J, F, alpha, i, T, w, s, n, eta, zeta`, the same
four ports `beta, K0, MC, MF` and the same 74 rows as the 75-operation circuit
`TenPositiveTrace75.regs`, except that the transport weight `V2 = V * V` in
`LBt` is replaced by the new row `L = cTR * V`, i.e. `L = b V` with
`b = cT - R`. (`V2` stays in the graph: it is still used by `RGV2`.)

`value76` reuses the 75 register map `regs` for every row other than the
carrier `Z`, and spells out the 76 carrier. `normValue r Z` is the output row
as a function of an arbitrary carrier value `Z`; both circuits are instances
(`value75_norm`, `value76_norm`, both `rfl`).

`value75_update` is the ring identity behind the soundness reduction: moving
`n` by `(V² - bV) B` turns the 76 carrier into the 75 carrier, so
`value75` at the moved point equals `value76`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace76
open DiophantineConsistency.TenPositiveTrace75

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4]

/-- The output row `N = Q (Z² - M² G V²) + (M² G - Z²)` at a given carrier `Z`. -/
def normValue (r : Regs R) (Z : R) : R :=
  r.Q * (Z * Z - r.M * r.M * r.Gn * (r.V * r.V)) + (r.M * r.M * r.Gn - Z * Z)

/-- The 76 carrier `Z = hD (H (n - L B) + K) - H (D B + h e)` with `L = b V`. -/
def Z76 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let L := r.b * r.V
  r.h * r.D * (r.H * (v 7 - L * r.B) + r.K) - r.H * (r.D * r.B + r.h * r.e)

/-- The value of the 76-operation circuit (its output row `N`). -/
def value76 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let L := r.b * r.V
  let Z := r.h * r.D * (r.H * (v 7 - L * r.B) + r.K) - r.H * (r.D * r.B + r.h * r.e)
  r.Q * (Z * Z - r.M * r.M * r.Gn * (r.V * r.V)) + (r.M * r.M * r.Gn - Z * Z)

theorem value75_norm (p : Fin 4 → R) (v : Fin 10 → R) :
    value75 p v = normValue (regs p v) (regs p v).Z := rfl

theorem value76_norm (p : Fin 4 → R) (v : Fin 10 → R) :
    value76 p v = normValue (regs p v) (Z76 p v) := rfl

theorem Z76_def (p : Fin 4 → R) (v : Fin 10 → R) :
    Z76 p v = (regs p v).h * (regs p v).D * ((regs p v).H *
      (v 7 - (regs p v).b * (regs p v).V * (regs p v).B) + (regs p v).K) -
      (regs p v).H * ((regs p v).D * (regs p v).B + (regs p v).h * (regs p v).e) := rfl

end Generic

section Ring
variable {R : Type*} [CommRing R]

/-- Moving `n` by `(V² - b V) B` turns the 76 carrier into the 75 carrier. -/
theorem value75_update (p : Fin 4 → R) (v : Fin 10 → R) (x : R)
    (hx : x = v 7 + ((regs p v).V * (regs p v).V - (regs p v).b * (regs p v).V) *
      (regs p v).B) :
    value75 p (Function.update v 7 x) = value76 p v := by
  have hZ : (regs p (Function.update v 7 x)).Z = Z76 p v := by
    change (regs p v).h * (regs p v).D * ((regs p v).H *
        (x - (regs p v).V * (regs p v).V * (regs p v).B) + (regs p v).K) -
        (regs p v).H * ((regs p v).D * (regs p v).B + (regs p v).h * (regs p v).e) = Z76 p v
    rw [Z76_def, hx]
    ring
  have hQ : (regs p (Function.update v 7 x)).Q = (regs p v).Q := rfl
  have hM : (regs p (Function.update v 7 x)).M = (regs p v).M := rfl
  have hG : (regs p (Function.update v 7 x)).Gn = (regs p v).Gn := rfl
  have hV : (regs p (Function.update v 7 x)).V = (regs p v).V := rfl
  rw [value75_norm, value76_norm]
  simp only [normValue, hZ, hQ, hM, hG, hV]

end Ring

end DiophantineConsistency.TenPositiveTrace76
