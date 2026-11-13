import DiophantineConsistency.P138.P138Value
import DiophantineConsistency.ZRows.ThreeRoot

/-! # The three-root 488/118 and 464/119 polynomials of package 125, register by register

Package 125 (`con-zfc-diophantine-forms/125-unified-binomial-round15/norm`), forms
`integral_direct_paired.json` (degree 488, 118 operations) and
`integral_centered_paired.json` (degree 464, 119 operations). Their eleven unrestricted integer
unknowns, in order, are `j C z h r v w T c n s` (`x 0 … x 10`); their six fixed integers are
`beta K0 MC MF cone_A cone_B` (`p 0 … p 5`): the unknowns and the ports of package 138.

**The front is package 138's.** DAG nodes 17–78 and 104–123 compute the registers
`J … Budget, L, Dt, K, H2, H3, zc, Ac, S` of `P138Value.regsK` with the native index
`k = 1 + R + h·E` (`P138Value.kN`), up to the operand order of two products (the second term of
`Budget` and `L`), which the syntax modules close by `ring`. The front registers are not
restated here: they are read from `P138Value.regsK p x κ`.

**The back end is new.** There is no main Pell norm and no cofactor: the strong ordinate is
`I = r c²`, and the output is the norm of three square roots (`ZRowsThreeRoot.norm3`),

    N(Z; A, B, G),   A = 9 S² Df,   B = S² δ Cy,   G = 81 S² Dt Dg,
    Df = 1 + Δ I²,   Q = Δ² I²,   δ = Q − 1,   Cy = Q V² − 1,
    V = Df (c − R + 4 I T) − c,   Dg = 1 + (3 Budget − 4) Dt s².

The two forms differ only in the linear slot: `Z = n S − Ac` (direct) and
`Z = S (n + Q V) − Ac` (centered). `back p x κ` evaluates the back-end registers that do not
read the slot, `tail p x κ ζ` the radicands and the paired norm schedule at a slot value `ζ`,
row by row in the order and with the operand order of the JSON DAGs (unnamed nodes are
inlined); `outK p x κ ζ` is the output, and `valueD`, `valueC` fill the `k` slot with the
native index and the `Z` slot with `zD`, `zC`.

The register equations `*_def` hold by `rfl`; the closed forms (`*_eq`) are proved by `ring`
with the registers as atoms, never by expanding the output. This module imports neither
Foundation's theories nor Mathlib's matrices. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P125Value
open P138Value ZRowsThreeRoot

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The back-end registers that do not read the linear slot (DAG nodes 79–103 and 113). -/
structure Back (𝔸 : Type*) where
  I : 𝔸
  strong : 𝔸
  Df : 𝔸
  Q : 𝔸
  delta : 𝔸
  b0 : 𝔸
  V : 𝔸
  shift : 𝔸
  Cy : 𝔸
  D81 : 𝔸
  Dg81 : 𝔸
  P81 : 𝔸
  S2 : 𝔸

/-- The back end, row by row, over the front `P138Value.regsK p x κ`. -/
def back (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ : 𝔸) : Back 𝔸 :=
  let f := regsK p x κ
  let I := x 4 * f.c2
  let strong := I * (f.Delta * I)
  let Df := 1 + strong
  let Q := f.Delta * strong
  let delta := Q - 1
  let b0 := x 8 - f.R + x 7 * (4 * I)
  let V := Df * b0 - x 8
  let shift := Q * V
  let Cy := V * shift - 1
  let D81 := f.Budget * 243 - 324
  let Dg81 := x 10 * (x 10 * (f.Dt * D81)) + 81
  let P81 := f.Dt * Dg81
  let S2 := f.S * f.S
  { I := I, strong := strong, Df := Df, Q := Q, delta := delta, b0 := b0, V := V,
    shift := shift, Cy := Cy, D81 := D81, Dg81 := Dg81, P81 := P81, S2 := S2 }

/-- The radicands and the paired norm schedule at a slot value `ζ`. -/
structure Tail (𝔸 : Type*) where
  Z2 : 𝔸
  A : 𝔸
  B : 𝔸
  G : 𝔸
  vnorm : 𝔸
  left : 𝔸
  right : 𝔸
  ynorm : 𝔸

/-- The tail, row by row, over `back p x κ`. -/
def tail (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ ζ : 𝔸) : Tail 𝔸 :=
  let b := back p x κ
  let Z2 := ζ * ζ
  let A := b.Df * (b.S2 * 9)
  let B := b.Cy * (b.delta * b.S2)
  let G := b.P81 * b.S2
  let vnorm := Z2 + A - B - G
  let left := Z2 * A
  let right := B * G
  let ynorm := vnorm * vnorm - 4 * (left + right)
  { Z2 := Z2, A := A, B := B, G := G, vnorm := vnorm, left := left, right := right,
    ynorm := ynorm }

/-- The output `ynorm² − right · (left · 64)` at the `k` slot `κ` and the `Z` slot `ζ`. -/
def outK (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ ζ : 𝔸) : 𝔸 :=
  let t := tail p x κ ζ
  t.ynorm * t.ynorm - t.right * (t.left * 64)

/-- The direct linear slot `n S − Ac` (package 138's `Z`). -/
def zD (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ : 𝔸) : 𝔸 :=
  x 9 * (regsK p x κ).S - (regsK p x κ).Ac

/-- The centered linear slot `S (n + Q V) − Ac`. -/
def zC (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ : 𝔸) : 𝔸 :=
  (regsK p x κ).S * (x 9 + (back p x κ).shift) - (regsK p x κ).Ac

/-- The guard cofactor `Dg = 1 + (3 Budget − 4) Dt s²`. -/
def Dg (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ : 𝔸) : 𝔸 :=
  1 + (3 * (regsK p x κ).Budget - 4) * (regsK p x κ).Dt * x 10 ^ 2

/-- The value of the 118-operation direct circuit. -/
abbrev valueD (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 := outK p x (kN p x) (zD p x (kN p x))

/-- The value of the 119-operation centered circuit. -/
abbrev valueC (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) : 𝔸 := outK p x (kN p x) (zC p x (kN p x))

/-! ### Register equations (by `rfl`) -/

section Defs
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ ζ : 𝔸)
local notation "𝓡" => regsK p x κ
local notation "𝓑" => back p x κ
local notation "𝓣" => tail p x κ ζ

theorem out_def : outK p x κ ζ = (𝓣).ynorm * (𝓣).ynorm - (𝓣).right * ((𝓣).left * 64) := rfl
theorem I_def : (𝓑).I = x 4 * (𝓡).c2 := rfl
theorem strong_def : (𝓑).strong = (𝓑).I * ((𝓡).Delta * (𝓑).I) := rfl
theorem Df_def : (𝓑).Df = 1 + (𝓑).strong := rfl
theorem Q_def : (𝓑).Q = (𝓡).Delta * (𝓑).strong := rfl
theorem delta_def : (𝓑).delta = (𝓑).Q - 1 := rfl
theorem b0_def : (𝓑).b0 = x 8 - (𝓡).R + x 7 * (4 * (𝓑).I) := rfl
theorem V_def : (𝓑).V = (𝓑).Df * (𝓑).b0 - x 8 := rfl
theorem shift_def : (𝓑).shift = (𝓑).Q * (𝓑).V := rfl
theorem Cy_def : (𝓑).Cy = (𝓑).V * (𝓑).shift - 1 := rfl
theorem D81_def : (𝓑).D81 = (𝓡).Budget * 243 - 324 := rfl
theorem Dg81_def : (𝓑).Dg81 = x 10 * (x 10 * ((𝓡).Dt * (𝓑).D81)) + 81 := rfl
theorem P81_def : (𝓑).P81 = (𝓡).Dt * (𝓑).Dg81 := rfl
theorem S2_def : (𝓑).S2 = (𝓡).S * (𝓡).S := rfl
theorem Z2_def : (𝓣).Z2 = ζ * ζ := rfl
theorem radA_def : (𝓣).A = (𝓑).Df * ((𝓑).S2 * 9) := rfl
theorem radB_def : (𝓣).B = (𝓑).Cy * ((𝓑).delta * (𝓑).S2) := rfl
theorem radG_def : (𝓣).G = (𝓑).P81 * (𝓑).S2 := rfl
theorem vnorm_def : (𝓣).vnorm = (𝓣).Z2 + (𝓣).A - (𝓣).B - (𝓣).G := rfl
theorem left_def : (𝓣).left = (𝓣).Z2 * (𝓣).A := rfl
theorem right_def : (𝓣).right = (𝓣).B * (𝓣).G := rfl
theorem ynorm_def :
    (𝓣).ynorm = (𝓣).vnorm * (𝓣).vnorm - 4 * ((𝓣).left + (𝓣).right) := rfl
theorem zD_def : zD p x κ = x 9 * (𝓡).S - (𝓡).Ac := rfl
theorem zD_reg : zD p x κ = (𝓡).Z := rfl
theorem zC_def : zC p x κ = (𝓡).S * (x 9 + (𝓑).shift) - (𝓡).Ac := rfl
theorem Dg_def : Dg p x κ = 1 + (3 * (𝓡).Budget - 4) * (𝓡).Dt * x 10 ^ 2 := rfl

/-! ### Closed forms in the notation of `PROOF.md` §1 -/

theorem I_eq : (𝓑).I = x 4 * x 8 ^ 2 := by rw [I_def, c2_def]; ring

theorem strong_eq : (𝓑).strong = (𝓡).Delta * (𝓑).I ^ 2 := by rw [strong_def]; ring

theorem Df_eq : (𝓑).Df = 1 + (𝓡).Delta * (𝓑).I ^ 2 := by rw [Df_def, strong_eq]

theorem Q_eq : (𝓑).Q = (𝓡).Delta ^ 2 * (𝓑).I ^ 2 := by rw [Q_def, strong_eq]; ring

theorem Q_Df : (𝓑).Q = (𝓡).Delta * ((𝓑).Df - 1) := by rw [Q_eq, Df_eq]; ring

theorem b0_eq : (𝓑).b0 = x 8 - (𝓡).R + 4 * (𝓑).I * x 7 := by rw [b0_def]; ring

theorem V_eq : (𝓑).V = (𝓑).Df * (x 8 - (𝓡).R + 4 * (𝓑).I * x 7) - x 8 := by
  rw [V_def, b0_eq]

theorem Cy_eq : (𝓑).Cy = (𝓑).Q * (𝓑).V ^ 2 - 1 := by rw [Cy_def, shift_def]; ring

theorem D81_eq : (𝓑).D81 = 81 * (3 * (𝓡).Budget - 4) := by rw [D81_def]; ring

theorem Dg81_eq : (𝓑).Dg81 = 81 * Dg p x κ := by rw [Dg81_def, D81_eq, Dg_def]; ring

theorem P81_eq : (𝓑).P81 = 81 * ((𝓡).Dt * Dg p x κ) := by rw [P81_def, Dg81_eq]; ring

theorem radA_eq : (𝓣).A = (3 * (𝓡).S) ^ 2 * (𝓑).Df := by rw [radA_def, S2_def]; ring

theorem radB_eq : (𝓣).B = (𝓡).S ^ 2 * ((𝓑).delta * (𝓑).Cy) := by rw [radB_def, S2_def]; ring

theorem radG_eq : (𝓣).G = (9 * (𝓡).S) ^ 2 * ((𝓡).Dt * Dg p x κ) := by
  rw [radG_def, P81_eq, S2_def]; ring

/-- **The output is the three-root norm** of the slot value at the three radicands. -/
theorem out_eq : outK p x κ ζ = norm3 ζ (𝓣).A (𝓣).B (𝓣).G := by
  rw [out_def, ynorm_def, vnorm_def, left_def, right_def, Z2_def]
  unfold norm3; ring

/-- The output where `S = 0`: `ζ⁸`. -/
theorem out_S_zero (hS : (𝓡).S = 0) : outK p x κ ζ = ζ ^ 8 := by
  rw [out_eq, radA_eq, radB_eq, radG_eq, hS]
  unfold norm3; ring

/-- The output at the slot value `0`. -/
theorem out_slot_zero : outK p x κ 0 = ((𝓡).S ^ 4 *
    ((9 * (𝓑).Df - (𝓑).delta * (𝓑).Cy - 81 * ((𝓡).Dt * Dg p x κ)) ^ 2 -
      324 * ((𝓑).delta * (𝓑).Cy * ((𝓡).Dt * Dg p x κ)))) ^ 2 := by
  rw [out_eq, norm3_zero_slot, radA_eq, radB_eq, radG_eq]; ring

/-- **The canonical zero**: with roots `f`, `e`, `g` of `Df`, `δ·Cy` and `Dt·Dg`, the slot value
`S (3 f + e + 9 g)` is a zero. -/
theorem out_of_roots {f e g : 𝔸} (hf : (𝓑).Df = f ^ 2) (he : (𝓑).delta * (𝓑).Cy = e ^ 2)
    (hg : (𝓡).Dt * Dg p x κ = g ^ 2) (hζ : ζ = (𝓡).S * (3 * f + e + 9 * g)) :
    outK p x κ ζ = 0 := by
  rw [out_eq]
  refine norm3_of_roots (α := 3 * (𝓡).S * f) (β := (𝓡).S * e) (γ := 9 * (𝓡).S * g) ?_ ?_ ?_ ?_
  · rw [radA_eq, hf]; ring
  · rw [radB_eq, he]; ring
  · rw [radG_eq, hg]; ring
  · rw [hζ]; ring

theorem zD_add : zD p x κ + (𝓡).Ac = (𝓡).S * x 9 := by rw [zD_def]; ring

theorem zC_add : zC p x κ + (𝓡).Ac = (𝓡).S * (x 9 + (𝓑).shift) := by rw [zC_def]; ring

end Defs

/-! ### Only the linear slot reads `x 9` -/

section Forms
variable (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸)

theorem kN_update9 (t : 𝔸) : kN p (Function.update x 9 t) = kN p x := rfl

theorem back_update9 (κ t : 𝔸) : back p (Function.update x 9 t) κ = back p x κ := rfl

theorem outK_update9 (κ ζ t : 𝔸) : outK p (Function.update x 9 t) κ ζ = outK p x κ ζ := rfl

theorem zC_update9 (κ t : 𝔸) : zC p (Function.update x 9 t) κ =
    (regsK p x κ).S * (t + (back p x κ).shift) - (regsK p x κ).Ac := rfl

/-- **The centered form is the direct form after the shift** `n ↦ n − Q V`. -/
theorem valueC_shift :
    valueC p (Function.update x 9 (x 9 - (back p x (kN p x)).shift)) = valueD p x := by
  have h : zC p (Function.update x 9 (x 9 - (back p x (kN p x)).shift)) (kN p x) =
      zD p x (kN p x) := by
    rw [zC_update9, zD_def]; ring
  show outK p (Function.update x 9 _) (kN p (Function.update x 9 _))
    (zC p (Function.update x 9 _) (kN p (Function.update x 9 _))) = _
  rw [kN_update9, outK_update9, h]

end Forms
end Generic

#print axioms DiophantineConsistency.P125Value.out_eq
#print axioms DiophantineConsistency.P125Value.out_S_zero
#print axioms DiophantineConsistency.P125Value.out_slot_zero
#print axioms DiophantineConsistency.P125Value.out_of_roots
#print axioms DiophantineConsistency.P125Value.valueC_shift
#print axioms DiophantineConsistency.P125Value.back_update9

end DiophantineConsistency.P125Value
