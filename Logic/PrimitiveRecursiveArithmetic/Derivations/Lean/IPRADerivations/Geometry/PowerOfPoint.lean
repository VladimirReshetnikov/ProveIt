import IPRADerivations.Core.IntCancel

/-!
# Power of a point (`docs/proofs/geometry/mollweide_circle_ipra`, Section 7–8)

For a circle with centre `O` and squared radius `ρ`, the power of `P` is
`Pow(P) = |P − O|² − ρ`. On the line `L(t) = P + tV`, with `p = Pow(P)`,
`h = ⟨P − O, V⟩`, `q = |V|²`:

* `line_power` (`lem:line-power`): `Pow(L(t)) = p + 2ht + qt²`;
* `signed_power` (`thm:signed-power`): if `u ≠ w` are roots, `Pow(L(u)) = Pow(L(w)) = 0`,
  then `Pow(P) = q u w`, by cancelling `u − w` (`zt_mul_cancel_sub`);
* `tangent_power`: at a tangency (`Pow(L(τ)) = 0`, `h + qτ = 0`), `Pow(P) = q τ²`;
* `chords_secants` (`thm:chords`, `thm:secants`): for two lines through `P` with root pairs
  `(u₁, w₁)`, `(u₂, w₂)`, `q₁ u₁ w₁ = q₂ u₂ w₂`, the denominator-free product of directed
  distances; `tangent_secant` (`thm:tangent-secant`): `q₃ τ² = q₁ u w`.

Coordinates are integers (`ZT`); each theorem is the universal closure of an iPRA formula.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PowerOfPoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `Pow(X) = |X − O|² − ρ`. -/
def pow (Xx Xy Ox Oy ρ : ZT n) : ZT n := ZT.sq (Xx - Ox) + ZT.sq (Xy - Oy) - ρ

/-- `⟨P − O, V⟩` and `|V|²`. -/
def hh (Px Py Ox Oy Vx Vy : ZT n) : ZT n := (Px - Ox) * Vx + (Py - Oy) * Vy
def qq (Vx Vy : ZT n) : ZT n := ZT.sq Vx + ZT.sq Vy

theorem toZ_pow (Xx Xy Ox Oy ρ : ZT n) : ZT.toZ Γ (pow Xx Xy Ox Oy ρ) =
    (ZT.toZ Γ Xx - ZT.toZ Γ Ox) ^ 2 + (ZT.toZ Γ Xy - ZT.toZ Γ Oy) ^ 2 - ZT.toZ Γ ρ := by
  simp [pow]

theorem toZ_hh (Px Py Ox Oy Vx Vy : ZT n) : ZT.toZ Γ (hh Px Py Ox Oy Vx Vy) =
    (ZT.toZ Γ Px - ZT.toZ Γ Ox) * ZT.toZ Γ Vx + (ZT.toZ Γ Py - ZT.toZ Γ Oy) * ZT.toZ Γ Vy := by
  simp [hh]

theorem toZ_qq (Vx Vy : ZT n) : ZT.toZ Γ (qq Vx Vy) = ZT.toZ Γ Vx ^ 2 + ZT.toZ Γ Vy ^ 2 := by
  simp [qq]

section Generic

variable (Px Py Ox Oy ρ Vx Vy : ZT n)

/-- `lem:line-power`. -/
theorem line_power (t : ZT n) : Γ ⊢[PRAAx] ZT.eq (pow (Px + t * Vx) (Py + t * Vy) Ox Oy ρ)
    (pow Px Py Ox Oy ρ + ZT.natLit 2 * hh Px Py Ox Oy Vx Vy * t + qq Vx Vy * (t * t)) := by
  apply ZT.derive
  simp only [toZ_pow, toZ_hh, toZ_qq, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast; ring

variable {Px Py Ox Oy ρ Vx Vy}

/-- `thm:signed-power`: two apart roots `u, w` give `Pow(P) = q u w`. -/
theorem signed_power {u w : ZT n}
    (hu : Γ ⊢[PRAAx] ZT.eq (pow (Px + u * Vx) (Py + u * Vy) Ox Oy ρ) (ZT.natLit 0))
    (hw : Γ ⊢[PRAAx] ZT.eq (pow (Px + w * Vx) (Py + w * Vy) Ox Oy ρ) (ZT.natLit 0))
    (huw : Γ ⊢[PRAAx] neg (ZT.eq u w)) :
    Γ ⊢[PRAAx] ZT.eq (pow Px Py Ox Oy ρ) (qq Vx Vy * u * w) := by
  have e₁ := ZT.toZ_eq hu
  have e₂ := ZT.toZ_eq hw
  have l₁ := ZT.toZ_eq (line_power (Γ := Γ) Px Py Ox Oy ρ Vx Vy u)
  have l₂ := ZT.toZ_eq (line_power (Γ := Γ) Px Py Ox Oy ρ Vx Vy w)
  -- `(u − w)(2h + q(u + w)) = 0`.
  have hK := zt_mul_cancel_sub (K := ZT.natLit 2 * hh Px Py Ox Oy Vx Vy + qq Vx Vy * (u + w)) huw (by
    apply ZT.derive
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit] at e₁ e₂ l₁ l₂ ⊢
    push_cast at e₁ e₂ l₁ l₂ ⊢
    linear_combination e₁ - e₂ - l₁ + l₂)
  have k := ZT.toZ_eq hK
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e₁ l₁ k ⊢
  push_cast at e₁ l₁ k ⊢
  linear_combination e₁ - l₁ - ZT.toZ Γ u * k

/-- At a tangency, `Pow(P) = q τ²`. -/
theorem tangent_power {τ : ZT n}
    (hτ : Γ ⊢[PRAAx] ZT.eq (pow (Px + τ * Vx) (Py + τ * Vy) Ox Oy ρ) (ZT.natLit 0))
    (htan : Γ ⊢[PRAAx] ZT.eq (hh Px Py Ox Oy Vx Vy + qq Vx Vy * τ) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (pow Px Py Ox Oy ρ) (qq Vx Vy * (τ * τ)) := by
  have e₁ := ZT.toZ_eq hτ
  have l₁ := ZT.toZ_eq (line_power (Γ := Γ) Px Py Ox Oy ρ Vx Vy τ)
  have k := ZT.toZ_eq htan
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e₁ l₁ k ⊢
  push_cast at e₁ l₁ k ⊢
  linear_combination e₁ - l₁ - 2 * ZT.toZ Γ τ * k

/-- `lem:secant-factor`, (7.6): with `f(t) = p + 2ht + qt²`, `w f(u) − u f(w) = (w − u)(p − q u w)`. -/
theorem secant_factor (p h q u w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (w * (p + ZT.natLit 2 * h * u + q * (u * u)) - u * (p + ZT.natLit 2 * h * w + q * (w * w)))
      ((w - u) * (p - q * u * w)) := by
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast; ring

/-- `lem:tangent-power`, the second equality of (7.9): for the touching point `T = P + τV`,
`|P − T|² = |τV|² = q τ²`. -/
theorem tangent_length (Vx Vy τ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (qq (τ * Vx) (τ * Vy)) (qq Vx Vy * (τ * τ)) := by
  apply ZT.derive
  simp only [toZ_qq, ZT.toZ_mul]
  ring

/-! ## Lengths: the order/sign readings of `thm:power-final` -/

/-- `|u|` for an integer term, as a natural number. -/
abbrev zab (u : ZT n) : PTm n := PTm.monus u.pos u.neg + PTm.monus u.neg u.pos

theorem zab_nonneg {u : ZT n} (h : Γ ⊢[PRAAx] le u.neg u.pos) : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (zab u)) u := by
  have e := natEq (eq_add_of_le h); have z := natEq h
  show Γ ⊢[PRAAx] zab u + u.neg ≐ u.pos + ConciseIPRA.PTm.zero
  apply deriveNat; ipra_simps; linear_combination z - e

theorem zab_nonpos {u : ZT n} (h : Γ ⊢[PRAAx] le u.pos u.neg) : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (zab u)) (-u) := by
  have e := natEq (eq_add_of_le h); have z := natEq h
  show Γ ⊢[PRAAx] zab u + u.pos ≐ u.neg + ConciseIPRA.PTm.zero
  apply deriveNat; ipra_simps; linear_combination z - e

variable {u w : ZT n}
  (hu : Γ ⊢[PRAAx] ZT.eq (pow (Px + u * Vx) (Py + u * Vy) Ox Oy ρ) (ZT.natLit 0))
  (hw : Γ ⊢[PRAAx] ZT.eq (pow (Px + w * Vx) (Py + w * Vy) Ox Oy ρ) (ZT.natLit 0))
  (huw : Γ ⊢[PRAAx] neg (ZT.eq u w))
include hu hw huw

/-- `thm:power-final`, part 2: for an external point the two intersections lie on one side
(`u, w ≥ 0`), and `Pow(P) = q |u| |w|`, the product of the two secant lengths `|u| ‖V‖` and `|w| ‖V‖`. -/
theorem secant_lengths (su : Γ ⊢[PRAAx] le u.neg u.pos) (sw : Γ ⊢[PRAAx] le w.neg w.pos) :
    Γ ⊢[PRAAx] ZT.eq (pow Px Py Ox Oy ρ) (qq Vx Vy * ZT.ofNat (zab u) * ZT.ofNat (zab w)) := by
  have p := ZT.toZ_eq (signed_power hu hw huw)
  have a := ZT.toZ_eq (zab_nonneg su); have b := ZT.toZ_eq (zab_nonneg sw)
  apply ZT.derive
  simp only [ZT.toZ_mul] at p ⊢
  linear_combination p - (ZT.toZ Γ (qq Vx Vy) * ZT.toZ Γ (ZT.ofNat (zab w))) * a - (ZT.toZ Γ (qq Vx Vy) * ZT.toZ Γ u) * b

/-- Part 2 with both intersections on the other side (`u, w ≤ 0`). -/
theorem secant_lengths' (su : Γ ⊢[PRAAx] le u.pos u.neg) (sw : Γ ⊢[PRAAx] le w.pos w.neg) :
    Γ ⊢[PRAAx] ZT.eq (pow Px Py Ox Oy ρ) (qq Vx Vy * ZT.ofNat (zab u) * ZT.ofNat (zab w)) := by
  have p := ZT.toZ_eq (signed_power hu hw huw)
  have a := ZT.toZ_eq (zab_nonpos su); have b := ZT.toZ_eq (zab_nonpos sw)
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_neg] at p a b ⊢
  linear_combination p - (ZT.toZ Γ (qq Vx Vy) * ZT.toZ Γ (ZT.ofNat (zab w))) * a + (ZT.toZ Γ (qq Vx Vy) * ZT.toZ Γ u) * b

/-- `thm:power-final`, part 3: for an interior point the chord's intersections lie on opposite sides
(`u ≤ 0 ≤ w`), and `−Pow(P) = q |u| |w|`, the product of the two chord pieces. -/
theorem chord_lengths (su : Γ ⊢[PRAAx] le u.pos u.neg) (sw : Γ ⊢[PRAAx] le w.neg w.pos) :
    Γ ⊢[PRAAx] ZT.eq (pow Px Py Ox Oy ρ + qq Vx Vy * ZT.ofNat (zab u) * ZT.ofNat (zab w)) (ZT.natLit 0) := by
  have p := ZT.toZ_eq (signed_power hu hw huw)
  have a := ZT.toZ_eq (zab_nonpos su); have b := ZT.toZ_eq (zab_nonneg sw)
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_zero] at p a b ⊢
  linear_combination p + (ZT.toZ Γ (qq Vx Vy) * ZT.toZ Γ (ZT.ofNat (zab w))) * a - (ZT.toZ Γ (qq Vx Vy) * ZT.toZ Γ u) * b

end Generic

/-! ## Closed theorems -/

section Closed

/-- `P, O, ρ, V, u, w`, over eighteen natural-number variables. -/
abbrev Px : ZT 18 := .var2 0 1
abbrev Py : ZT 18 := .var2 2 3
abbrev Ox : ZT 18 := .var2 4 5
abbrev Oy : ZT 18 := .var2 6 7
abbrev ρ : ZT 18 := .var2 8 9
abbrev Vx : ZT 18 := .var2 10 11
abbrev Vy : ZT 18 := .var2 12 13
abbrev u : ZT 18 := .var2 14 15
abbrev w : ZT 18 := .var2 16 17

abbrev signedPowerFormula : Fm PTm 18 :=
  ZT.eq (pow (Px + u * Vx) (Py + u * Vy) Ox Oy ρ) (ZT.natLit 0) ⟶
    ZT.eq (pow (Px + w * Vx) (Py + w * Vy) Ox Oy ρ) (ZT.natLit 0) ⟶ neg (ZT.eq u w) ⟶
    ZT.eq (pow Px Py Ox Oy ρ) (qq Vx Vy * u * w)

theorem signed_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 18 signedPowerFormula :=
  closeAll 18 (.impI (.impI (.impI (signed_power hyp2 Prf.hyp1 Prf.hyp0))))

end Closed

section Chords

/-- `P, O, ρ`, two lines `V₁, V₂` with root pairs `(u₁, w₁)`, `(u₂, w₂)`, over twenty-six
natural-number variables. -/
abbrev cPx : ZT 26 := .var2 0 1
abbrev cPy : ZT 26 := .var2 2 3
abbrev cOx : ZT 26 := .var2 4 5
abbrev cOy : ZT 26 := .var2 6 7
abbrev cρ : ZT 26 := .var2 8 9
abbrev V₁x : ZT 26 := .var2 10 11
abbrev V₁y : ZT 26 := .var2 12 13
abbrev u₁ : ZT 26 := .var2 14 15
abbrev w₁ : ZT 26 := .var2 16 17
abbrev V₂x : ZT 26 := .var2 18 19
abbrev V₂y : ZT 26 := .var2 20 21
abbrev u₂ : ZT 26 := .var2 22 23
abbrev w₂ : ZT 26 := .var2 24 25

/-- `thm:chords`, `thm:secants`: `q₁ u₁ w₁ = q₂ u₂ w₂`. -/
abbrev chordsFormula : Fm PTm 26 :=
  ZT.eq (pow (cPx + u₁ * V₁x) (cPy + u₁ * V₁y) cOx cOy cρ) (ZT.natLit 0) ⟶
    ZT.eq (pow (cPx + w₁ * V₁x) (cPy + w₁ * V₁y) cOx cOy cρ) (ZT.natLit 0) ⟶ neg (ZT.eq u₁ w₁) ⟶
    ZT.eq (pow (cPx + u₂ * V₂x) (cPy + u₂ * V₂y) cOx cOy cρ) (ZT.natLit 0) ⟶
    ZT.eq (pow (cPx + w₂ * V₂x) (cPy + w₂ * V₂y) cOx cOy cρ) (ZT.natLit 0) ⟶ neg (ZT.eq u₂ w₂) ⟶
    ZT.eq (qq V₁x V₁y * u₁ * w₁) (qq V₂x V₂y * u₂ * w₂)

theorem chords_secants : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 26 chordsFormula := by
  refine closeAll 26 (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  have h₁ := signed_power (Px := cPx) (Py := cPy) (Ox := cOx) (Oy := cOy) (ρ := cρ) (Vx := V₁x) (Vy := V₁y)
    (u := u₁) (w := w₁) (Γ := [neg (ZT.eq u₂ w₂),
      ZT.eq (pow (cPx + w₂ * V₂x) (cPy + w₂ * V₂y) cOx cOy cρ) (ZT.natLit 0),
      ZT.eq (pow (cPx + u₂ * V₂x) (cPy + u₂ * V₂y) cOx cOy cρ) (ZT.natLit 0), neg (ZT.eq u₁ w₁),
      ZT.eq (pow (cPx + w₁ * V₁x) (cPy + w₁ * V₁y) cOx cOy cρ) (ZT.natLit 0),
      ZT.eq (pow (cPx + u₁ * V₁x) (cPy + u₁ * V₁y) cOx cOy cρ) (ZT.natLit 0)])
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
  have h₂ := signed_power (Px := cPx) (Py := cPy) (Ox := cOx) (Oy := cOy) (ρ := cρ) (Vx := V₂x) (Vy := V₂y)
    (u := u₂) (w := w₂) (Γ := [neg (ZT.eq u₂ w₂),
      ZT.eq (pow (cPx + w₂ * V₂x) (cPy + w₂ * V₂y) cOx cOy cρ) (ZT.natLit 0),
      ZT.eq (pow (cPx + u₂ * V₂x) (cPy + u₂ * V₂y) cOx cOy cρ) (ZT.natLit 0), neg (ZT.eq u₁ w₁),
      ZT.eq (pow (cPx + w₁ * V₁x) (cPy + w₁ * V₁y) cOx cOy cρ) (ZT.natLit 0),
      ZT.eq (pow (cPx + u₁ * V₁x) (cPy + u₁ * V₁y) cOx cOy cρ) (ZT.natLit 0)])
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
  apply ZT.derive
  exact (ZT.toZ_eq h₁).symm.trans (ZT.toZ_eq h₂)

end Chords

section TangentSecant

/-- `P, O, ρ`, a secant `V₁` with roots `u, w`, a tangent `V₃` touching at `τ`, over
twenty-four natural-number variables. -/
abbrev tPx : ZT 24 := .var2 0 1
abbrev tPy : ZT 24 := .var2 2 3
abbrev tOx : ZT 24 := .var2 4 5
abbrev tOy : ZT 24 := .var2 6 7
abbrev tρ : ZT 24 := .var2 8 9
abbrev S₁x : ZT 24 := .var2 10 11
abbrev S₁y : ZT 24 := .var2 12 13
abbrev su : ZT 24 := .var2 14 15
abbrev sw : ZT 24 := .var2 16 17
abbrev T₃x : ZT 24 := .var2 18 19
abbrev T₃y : ZT 24 := .var2 20 21
abbrev tτ : ZT 24 := .var2 22 23

/-- `thm:tangent-secant`: `q₃ τ² = q₁ u w`. -/
abbrev tangentSecantFormula : Fm PTm 24 :=
  ZT.eq (pow (tPx + su * S₁x) (tPy + su * S₁y) tOx tOy tρ) (ZT.natLit 0) ⟶
    ZT.eq (pow (tPx + sw * S₁x) (tPy + sw * S₁y) tOx tOy tρ) (ZT.natLit 0) ⟶ neg (ZT.eq su sw) ⟶
    ZT.eq (pow (tPx + tτ * T₃x) (tPy + tτ * T₃y) tOx tOy tρ) (ZT.natLit 0) ⟶
    ZT.eq (hh tPx tPy tOx tOy T₃x T₃y + qq T₃x T₃y * tτ) (ZT.natLit 0) ⟶
    ZT.eq (qq T₃x T₃y * (tτ * tτ)) (qq S₁x S₁y * su * sw)

theorem tangent_secant : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 24 tangentSecantFormula := by
  refine closeAll 24 (.impI (.impI (.impI (.impI (.impI ?_)))))
  have h₁ := signed_power (Px := tPx) (Py := tPy) (Ox := tOx) (Oy := tOy) (ρ := tρ) (Vx := S₁x) (Vy := S₁y)
    (u := su) (w := sw) (Γ := [ZT.eq (hh tPx tPy tOx tOy T₃x T₃y + qq T₃x T₃y * tτ) (ZT.natLit 0),
      ZT.eq (pow (tPx + tτ * T₃x) (tPy + tτ * T₃y) tOx tOy tρ) (ZT.natLit 0), neg (ZT.eq su sw),
      ZT.eq (pow (tPx + sw * S₁x) (tPy + sw * S₁y) tOx tOy tρ) (ZT.natLit 0),
      ZT.eq (pow (tPx + su * S₁x) (tPy + su * S₁y) tOx tOy tρ) (ZT.natLit 0)])
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
  have h₂ := tangent_power (Px := tPx) (Py := tPy) (Ox := tOx) (Oy := tOy) (ρ := tρ) (Vx := T₃x) (Vy := T₃y)
    (τ := tτ) (Γ := [ZT.eq (hh tPx tPy tOx tOy T₃x T₃y + qq T₃x T₃y * tτ) (ZT.natLit 0),
      ZT.eq (pow (tPx + tτ * T₃x) (tPy + tτ * T₃y) tOx tOy tρ) (ZT.natLit 0), neg (ZT.eq su sw),
      ZT.eq (pow (tPx + sw * S₁x) (tPy + sw * S₁y) tOx tOy tρ) (ZT.natLit 0),
      ZT.eq (pow (tPx + su * S₁x) (tPy + su * S₁y) tOx tOy tρ) (ZT.natLit 0)])
    (Prf.hyp (by simp)) (Prf.hyp (by simp))
  apply ZT.derive
  exact (ZT.toZ_eq h₂).symm.trans (ZT.toZ_eq h₁)

end TangentSecant

end LeanProofs.IPRA.Geometry.PowerOfPoint
