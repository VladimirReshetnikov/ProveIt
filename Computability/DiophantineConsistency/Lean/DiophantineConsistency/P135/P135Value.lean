import DiophantineConsistency.LinCof.LCValue

/-! # Five sibling forms of the 300/144 circuit (packages 135 and 144)

Five eleven-integer equations of the frontier are the linear-cofactor circuit `LCValue.regsK`
with the slots of package 172's 300/144 form (`k300`, `kq300`, `L300`: index modulus `E = X·Y`,
budget power `q⁸`), a different centre `Ψ` and a smaller radical weight:

| point | JSON | centre `Ψ` | weight |
|---|---|---|---|
| 352/125 | `135-cofinal-anchors-round17/scalar/free_cofactor11_none.json` | `0` | `4` |
| 340/129 | `135-cofinal-anchors-round17/scalar/free_cofactor11_simple.json` | `V·(AU·(2·A))` | `4` |
| 328/130 | `135-cofinal-anchors-round17/scalar/free_cofactor11_sharp.json` | `V·(U·(1 + Δ·2))` | `4` |
| 316/133 | `144-shared-certificates-round18/scalar/free_whole_center11_c316.json` | `V·(U·(4 + Δ·8) − r·c⁴)` | `64` |
| 308/140 | `144-shared-certificates-round18/scalar/free_whole_center11_c308.json` | `V·(U·(4 + Δ·8) − r·c⁴) + UT·((c² − 2)·(2·U))` | `64` |

(paths below `con-zfc-diophantine-forms/`). The centres are written with the operand order of
the JSON DAGs, and read only registers that do not depend on the slots, at the dummy slots `0`.
The soundness argument of the family (`LCLeaf.sound`) never reads the centre, and completeness
(`LCComplete.lc_complete300`) needs only that it does not read the unknown `n = x 9`.

This module imports neither Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P135Value
open LCValue

variable {𝔸 : Type*} [CommRing 𝔸]

/-- The centre of 340/129 (package 135, "simple"): `V · (AU · (2 · A))`. -/
def psi340 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let r := regsK p x 0 0 0 0 0
  r.V * (r.AU * (2 * r.A))

/-- The centre of 328/130 (package 135, "sharp"): `V · (U · (1 + Δ · 2))`. -/
def psi328 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let r := regsK p x 0 0 0 0 0
  r.V * (r.U * (1 + r.Delta * 2))

/-- The centre of 316/133 (package 144): `V · (U · (4 + Δ · 8) − r · c⁴)`. -/
def psi316 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let r := regsK p x 0 0 0 0 0
  r.V * (r.U * (4 + r.Delta * 8) - r.rc4)

/-- The centre of 308/140 (package 144): that of 316/133 plus `UT · ((c² − 2) · (2 · U))`. -/
def psi308 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  let r := regsK p x 0 0 0 0 0
  r.V * (r.U * (4 + r.Delta * 8) - r.rc4) + r.UT * (r.cm2 * (2 * r.U))

/-- The registers of 352/125: no centre, weight `4`. -/
abbrev regs352 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  regsK p x (k300 p x) (kq300 p x) (L300 p x) 0 4

/-- The value of 352/125. -/
abbrev value352 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  valueK p x (k300 p x) (kq300 p x) (L300 p x) 0 4

/-- The registers of 340/129: centre `psi340`, weight `4`. -/
abbrev regs340 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  regsK p x (k300 p x) (kq300 p x) (L300 p x) (psi340 p x) 4

/-- The value of 340/129. -/
abbrev value340 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  valueK p x (k300 p x) (kq300 p x) (L300 p x) (psi340 p x) 4

/-- The registers of 328/130: centre `psi328`, weight `4`. -/
abbrev regs328 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  regsK p x (k300 p x) (kq300 p x) (L300 p x) (psi328 p x) 4

/-- The value of 328/130. -/
abbrev value328 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  valueK p x (k300 p x) (kq300 p x) (L300 p x) (psi328 p x) 4

/-- The registers of 316/133: centre `psi316`, weight `64`. -/
abbrev regs316 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  regsK p x (k300 p x) (kq300 p x) (L300 p x) (psi316 p x) 64

/-- The value of 316/133. -/
abbrev value316 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  valueK p x (k300 p x) (kq300 p x) (L300 p x) (psi316 p x) 64

/-- The registers of 308/140: centre `psi308`, weight `64`. -/
abbrev regs308 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : Regs 𝔸 :=
  regsK p x (k300 p x) (kq300 p x) (L300 p x) (psi308 p x) 64

/-- The value of 308/140. -/
abbrev value308 (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 :=
  valueK p x (k300 p x) (kq300 p x) (L300 p x) (psi308 p x) 64

end DiophantineConsistency.P135Value
