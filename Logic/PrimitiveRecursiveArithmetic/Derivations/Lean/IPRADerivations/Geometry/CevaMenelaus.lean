import IPRADerivations.Core.IntCancel
import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Geometry.HypercubeSplit

/-!
# Ceva, Menelaus and Carnot's conic theorem in barycentric coordinates

Packet: `eight_geometry_theorems_ipra`, `sections/03_core_lemmas.tex` (the binary quadratic root
product), `sections/05_ceva_menelaus.tex` and `sections/06_carnot_conic.tex`. Coordinates are
integer terms (`ZT`), the reference triangle is `A = (1,0,0)`, `B = (0,1,0)`, `C = (0,0,1)`, and a
nonzero integer `δ` is one with `|δ| ≥ 1` (`nz`).

* `zt_cancel` (reusable): `δ X = δ Y` and `δ ≠ 0` give `X = Y`;
* `ceva_det`, `ceva_witness` (Constructive Ceva): for `D = (0, d_B, d_C)`, `E = (e_A, 0, e_C)`,
  `F = (f_A, f_B, 0)` the cevian determinant is `d_B e_C f_A − d_C e_A f_B`, and under
  `d_C e_A f_B = d_B e_C f_A` the point `P = (e_A d_C, d_B e_C, d_C e_C)` lies on all three cevians;
* `menelaus_det`, `menelaus_line` (Constructive Menelaus): the determinant of `D, E, F` is
  `d_B e_C f_A + d_C e_A f_B`, and the line `D ∨ E = (d_B e_C, d_C e_A, −d_B e_A)` takes this value
  at `F`;
* `bq_identity`, `binary_quadratic`: for `h(y, z) = v y² + p yz + w z²`,
  `y₂z₂ h(y₁, z₁) − y₁z₁ h(y₂, z₂) = (y₁z₂ − y₂z₁)(v y₁y₂ − w z₁z₂)`, so two distinct roots give
  `v y₁y₂ = w z₁z₂`;
* `carnot_forward`, `carnot_converse` (Carnot's conic theorem): six points `D_i ∈ BC`, `E_i ∈ CA`,
  `F_i ∈ AB` on a conic avoiding the vertices satisfy
  `(e₁e₂)(a₁a₂)(q₁q₂) = (d₁d₂)(c₁c₂)(p₁p₂)`; conversely this condition makes the packet's explicit
  conic vanish at all six points.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CevaMenelaus

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Cancelling a nonzero integer -/

/-- `δ ≠ 0`, as `|δ| ≥ 1`. -/
abbrev nz (δ : ZT n) : Fm PTm n := le one (monus δ.pos δ.neg + monus δ.neg δ.pos)

theorem nat_cancel {k l : PTm n} (hk : Γ ⊢[PRAAx] le one k) (h : Γ ⊢[PRAAx] k * l ≐ zero) : Γ ⊢[PRAAx] l ≐ zero :=
  mul_eq_cancel_at (Common.pos_of_one_le hk) (h.eqTrans (mul_zero _).eqSymm)

theorem nz_of_le {δ : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) (h : Γ ⊢[PRAAx] le δ.pos δ.neg) :
    Γ ⊢[PRAAx] le one (monus δ.neg δ.pos) :=
  le_congr (.eqRefl _) ((congrAdd h (.eqRefl _)).eqTrans (zero_add _)) hδ

theorem nz_of_ge {δ : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) (h : Γ ⊢[PRAAx] le δ.neg δ.pos) :
    Γ ⊢[PRAAx] le one (monus δ.pos δ.neg) :=
  le_congr (.eqRefl _) ((congrAdd (.eqRefl _) h).eqTrans (add_zero _)) hδ

private theorem nonzero_of_nz {δ : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) :
    Γ ⊢[PRAAx] neg (ZT.eq δ (ZT.natLit 0)) := by
  refine .impI ?_
  have coordinates : (ZT.eq δ (ZT.natLit 0) :: Γ) ⊢[PRAAx] δ.pos ≐ δ.neg :=
    (add_zero _).eqSymm.eqTrans (Prf.hyp0.eqTrans (zero_add _))
  have magnitude := (congrAdd
    ((congrMonus coordinates (.eqRefl _)).eqTrans (monus_self _))
    ((congrMonus (.eqRefl _) coordinates).eqTrans (monus_self _))).eqTrans (add_zero _)
  exact lt_zero_absurd _ (le_congr (.eqRefl _) magnitude hδ.wk)

/-! The case-specific theorems keep the order hypotheses in their original interfaces. -/
section
set_option linter.unusedVariables false

theorem zt_cancel₁ {δ X Y : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) (h : Γ ⊢[PRAAx] ZT.eq (δ * X) (δ * Y))
    (h₁ : Γ ⊢[PRAAx] le δ.pos δ.neg) (h₂ : Γ ⊢[PRAAx] le (X.pos + Y.neg) (Y.pos + X.neg)) : Γ ⊢[PRAAx] ZT.eq X Y :=
  zt_mul_eq_cancel_left (nonzero_of_nz hδ) h

theorem zt_cancel₂ {δ X Y : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) (h : Γ ⊢[PRAAx] ZT.eq (δ * X) (δ * Y))
    (h₁ : Γ ⊢[PRAAx] le δ.pos δ.neg) (h₂ : Γ ⊢[PRAAx] le (Y.pos + X.neg) (X.pos + Y.neg)) : Γ ⊢[PRAAx] ZT.eq X Y :=
  zt_mul_eq_cancel_left (nonzero_of_nz hδ) h

theorem zt_cancel₃ {δ X Y : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) (h : Γ ⊢[PRAAx] ZT.eq (δ * X) (δ * Y))
    (h₁ : Γ ⊢[PRAAx] le δ.neg δ.pos) (h₂ : Γ ⊢[PRAAx] le (X.pos + Y.neg) (Y.pos + X.neg)) : Γ ⊢[PRAAx] ZT.eq X Y :=
  zt_mul_eq_cancel_left (nonzero_of_nz hδ) h

theorem zt_cancel₄ {δ X Y : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) (h : Γ ⊢[PRAAx] ZT.eq (δ * X) (δ * Y))
    (h₁ : Γ ⊢[PRAAx] le δ.neg δ.pos) (h₂ : Γ ⊢[PRAAx] le (Y.pos + X.neg) (X.pos + Y.neg)) : Γ ⊢[PRAAx] ZT.eq X Y :=
  zt_mul_eq_cancel_left (nonzero_of_nz hδ) h

end

/-- `δ X = δ Y` with `δ ≠ 0` gives `X = Y`. -/
theorem zt_cancel {δ X Y : ZT n} (hδ : Γ ⊢[PRAAx] nz δ) (h : Γ ⊢[PRAAx] ZT.eq (δ * X) (δ * Y)) :
    Γ ⊢[PRAAx] ZT.eq X Y :=
  zt_mul_eq_cancel_left (nonzero_of_nz hδ) h

/-! ## Vectors in coordinates -/

/-- `0` as an integer term. -/
abbrev z0 : ZT n := ZT.natLit 0

/-- `(a, b, c) · (x, y, z)`. -/
abbrev dot3 (a b c x y z : ZT n) : ZT n := a * x + b * y + c * z

/-- The `3 × 3` determinant, expanded along the first row. -/
abbrev det3 (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : ZT n) : ZT n :=
  a₁ * (b₂ * c₃ - b₃ * c₂) - a₂ * (b₁ * c₃ - b₃ * c₁) + a₃ * (b₁ * c₂ - b₂ * c₁)

/-! ## Ceva and Menelaus -/

section CM

variable (dB dC eA eC fA fB : ZT n)

/-- The determinant of the cevians `AD = (0, −d_C, d_B)`, `BE = (e_C, 0, −e_A)`, `CF = (−f_B, f_A, 0)`. -/
theorem ceva_det :
    Γ ⊢[PRAAx] ZT.eq (det3 z0 (-dC) dB eC z0 (-eA) (-fB) fA z0) (dB * eC * fA - dC * eA * fB) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]; push_cast; ring)

/-- Constructive Ceva, converse: under `d_C e_A f_B = d_B e_C f_A` the point
`P = (e_A d_C, d_B e_C, d_C e_C)` lies on `AD`, `BE` and `CF`. -/
theorem ceva_witness {dB dC eA eC fA fB : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (dC * eA * fB) (dB * eC * fA)) :
    Γ ⊢[PRAAx] ZT.eq (dot3 z0 (-dC) dB (eA * dC) (dB * eC) (dC * eC)) z0 ⋏
      (ZT.eq (dot3 eC z0 (-eA) (eA * dC) (dB * eC) (dC * eC)) z0 ⋏
        ZT.eq (dot3 (-fB) fA z0 (eA * dC) (dB * eC) (dC * eC)) z0) := by
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_mul] at e
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_)) <;>
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] <;> push_cast
  · ring
  · ring
  · linear_combination -e

/-- The determinant of `D = (0, d_B, d_C)`, `E = (e_A, 0, e_C)`, `F = (f_A, f_B, 0)`. -/
theorem menelaus_det :
    Γ ⊢[PRAAx] ZT.eq (det3 z0 eA fA dB z0 fB dC eC z0) (dB * eC * fA + dC * eA * fB) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]; push_cast; ring)

/-- Constructive Menelaus: the line `D ∨ E = (d_B e_C, d_C e_A, −d_B e_A)` passes through `D` and
`E`, and its value at `F` is `d_B e_C f_A + d_C e_A f_B`. -/
theorem menelaus_line :
    Γ ⊢[PRAAx] ZT.eq (dot3 z0 dB dC (dB * eC) (dC * eA) (-(dB * eA))) z0 ⋏
      (ZT.eq (dot3 eA z0 eC (dB * eC) (dC * eA) (-(dB * eA))) z0 ⋏
        ZT.eq (dot3 fA fB z0 (dB * eC) (dC * eA) (-(dB * eA))) (dB * eC * fA + dC * eA * fB)) := by
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_)) <;>
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] <;> push_cast <;> ring

end CM

/-! ## The binary quadratic root product -/

/-- `h(y, z) = v y² + p yz + w z²`. -/
abbrev hq (v p w y z : ZT n) : ZT n := v * y * y + p * y * z + w * z * z

theorem bq_identity (v p w y₁ z₁ y₂ z₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (y₂ * z₂ * hq v p w y₁ z₁ - y₁ * z₁ * hq v p w y₂ z₂)
      ((y₁ * z₂ - y₂ * z₁) * (v * y₁ * y₂ - w * z₁ * z₂)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]; ring)

/-- Two distinct projective roots of `h` satisfy `v y₁y₂ = w z₁z₂`. -/
theorem binary_quadratic {v p w y₁ z₁ y₂ z₂ : ZT n} (h₁ : Γ ⊢[PRAAx] ZT.eq (hq v p w y₁ z₁) z0)
    (h₂ : Γ ⊢[PRAAx] ZT.eq (hq v p w y₂ z₂) z0) (hδ : Γ ⊢[PRAAx] nz (y₁ * z₂ - y₂ * z₁)) :
    Γ ⊢[PRAAx] ZT.eq (v * y₁ * y₂) (w * z₁ * z₂) := by
  have a := ZT.toZ_eq h₁; have b := ZT.toZ_eq h₂
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at a b
  refine zt_cancel hδ (ZT.derive ?_)
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]
  push_cast at a b
  linear_combination (ZT.toZ Γ y₂ * ZT.toZ Γ z₂) * a - (ZT.toZ Γ y₁ * ZT.toZ Γ z₁) * b

/-! ## Carnot's conic theorem -/

section Carnot

variable {d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ : ZT n}

/-- The conic `u x² + v y² + w z² + s yz + t zx + r xy`. -/
abbrev conic (u v w s t r x y z : ZT n) : ZT n :=
  u * x * x + v * y * y + w * z * z + s * y * z + t * z * x + r * x * y

theorem side_D {u v w s t r y z : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r z0 y z) z0) :
    Γ ⊢[PRAAx] ZT.eq (hq v s w y z) z0 := by
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast at e ⊢
  linear_combination e

theorem side_E {u v w s t r x z : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r x z0 z) z0) :
    Γ ⊢[PRAAx] ZT.eq (hq u t w x z) z0 := by
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast at e ⊢
  linear_combination e

theorem side_F {u v w s t r x y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r x y z0) z0) :
    Γ ⊢[PRAAx] ZT.eq (hq v r u y x) z0 := by
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit]
  push_cast at e ⊢
  linear_combination e

theorem mul3_cancel {u v w X Y : ZT n} (hu : Γ ⊢[PRAAx] nz u) (hv : Γ ⊢[PRAAx] nz v) (hw : Γ ⊢[PRAAx] nz w)
    (h : Γ ⊢[PRAAx] ZT.eq (u * (v * (w * X))) (u * (v * (w * Y)))) : Γ ⊢[PRAAx] ZT.eq X Y :=
  zt_cancel hw (zt_cancel hv (zt_cancel hu h))

/-- Carnot's conic theorem, forward: if the conic with `u, v, w ≠ 0` passes through
`D_i = (0, d_i, e_i)`, `E_i = (a_i, 0, c_i)` and `F_i = (p_i, q_i, 0)`, distinct on each side, then
`(e₁e₂)(a₁a₂)(q₁q₂) = (d₁d₂)(c₁c₂)(p₁p₂)`. -/
theorem carnot_forward {u v w s t r : ZT n}
    (hD₁ : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r z0 d₁ e₁) z0) (hD₂ : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r z0 d₂ e₂) z0)
    (hE₁ : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r a₁ z0 c₁) z0) (hE₂ : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r a₂ z0 c₂) z0)
    (hF₁ : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r p₁ q₁ z0) z0) (hF₂ : Γ ⊢[PRAAx] ZT.eq (conic u v w s t r p₂ q₂ z0) z0)
    (hδD : Γ ⊢[PRAAx] nz (d₁ * e₂ - d₂ * e₁)) (hδE : Γ ⊢[PRAAx] nz (a₁ * c₂ - a₂ * c₁))
    (hδF : Γ ⊢[PRAAx] nz (q₁ * p₂ - q₂ * p₁))
    (hu : Γ ⊢[PRAAx] nz u) (hv : Γ ⊢[PRAAx] nz v) (hw : Γ ⊢[PRAAx] nz w) :
    Γ ⊢[PRAAx] ZT.eq (e₁ * e₂ * (a₁ * a₂) * (q₁ * q₂)) (d₁ * d₂ * (c₁ * c₂) * (p₁ * p₂)) := by
  have bD := binary_quadratic (side_D hD₁) (side_D hD₂) hδD
  have bE := binary_quadratic (side_E hE₁) (side_E hE₂) hδE
  have bF := binary_quadratic (side_F hF₁) (side_F hF₂) hδF
  have eD := ZT.toZ_eq bD; have eE := ZT.toZ_eq bE; have eF := ZT.toZ_eq bF
  simp only [ZT.toZ_mul] at eD eE eF
  refine mul3_cancel hu hv hw (ZT.derive ?_)
  simp only [ZT.toZ_mul]
  linear_combination -(ZT.toZ Γ u * ZT.toZ Γ a₁ * ZT.toZ Γ a₂ * ZT.toZ Γ v * ZT.toZ Γ q₁ * ZT.toZ Γ q₂) * eD +
    (ZT.toZ Γ v * ZT.toZ Γ d₁ * ZT.toZ Γ d₂ * ZT.toZ Γ v * ZT.toZ Γ q₁ * ZT.toZ Γ q₂) * eE +
    (ZT.toZ Γ v * ZT.toZ Γ d₁ * ZT.toZ Γ d₂ * ZT.toZ Γ w * ZT.toZ Γ c₁ * ZT.toZ Γ c₂) * eF

/-- The packet's conic witness, with `D_y = d₁d₂`, `D_z = e₁e₂`, `E_x = a₁a₂`, `E_z = c₁c₂`,
`F_x = p₁p₂`, `F_y = q₁q₂`. -/
abbrev cu (d₁ d₂ c₁ c₂ q₁ q₂ : ZT n) : ZT n := d₁ * d₂ * (c₁ * c₂) * (q₁ * q₂)
abbrev cv (e₁ e₂ a₁ a₂ q₁ q₂ : ZT n) : ZT n := e₁ * e₂ * (a₁ * a₂) * (q₁ * q₂)
abbrev cw (d₁ d₂ a₁ a₂ q₁ q₂ : ZT n) : ZT n := d₁ * d₂ * (a₁ * a₂) * (q₁ * q₂)
abbrev cs (d₁ e₁ d₂ e₂ a₁ a₂ q₁ q₂ : ZT n) : ZT n := -(a₁ * a₂ * (q₁ * q₂) * (e₁ * d₂ + d₁ * e₂))
abbrev ct (d₁ d₂ a₁ c₁ a₂ c₂ q₁ q₂ : ZT n) : ZT n := -(d₁ * d₂ * (q₁ * q₂) * (c₁ * a₂ + a₁ * c₂))
abbrev cr (d₁ d₂ c₁ c₂ p₁ q₁ p₂ q₂ : ZT n) : ZT n := -(d₁ * d₂ * (c₁ * c₂) * (q₁ * p₂ + p₁ * q₂))

/-- The witness conic. -/
abbrev carnotConic (d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ x y z : ZT n) : ZT n :=
  conic (cu d₁ d₂ c₁ c₂ q₁ q₂) (cv e₁ e₂ a₁ a₂ q₁ q₂) (cw d₁ d₂ a₁ a₂ q₁ q₂) (cs d₁ e₁ d₂ e₂ a₁ a₂ q₁ q₂)
    (ct d₁ d₂ a₁ c₁ a₂ c₂ q₁ q₂) (cr d₁ d₂ c₁ c₂ p₁ q₁ p₂ q₂) x y z

/-- Carnot's conic theorem, converse: under `(e₁e₂)(a₁a₂)(q₁q₂) = (d₁d₂)(c₁c₂)(p₁p₂)` the witness
conic vanishes at the six points. -/
theorem carnot_converse (h : Γ ⊢[PRAAx] ZT.eq (e₁ * e₂ * (a₁ * a₂) * (q₁ * q₂)) (d₁ * d₂ * (c₁ * c₂) * (p₁ * p₂))) :
    Γ ⊢[PRAAx] ZT.eq (carnotConic d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ z0 d₁ e₁) z0 ⋏
      (ZT.eq (carnotConic d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ z0 d₂ e₂) z0 ⋏
      (ZT.eq (carnotConic d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ a₁ z0 c₁) z0 ⋏
      (ZT.eq (carnotConic d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ a₂ z0 c₂) z0 ⋏
      (ZT.eq (carnotConic d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ p₁ q₁ z0) z0 ⋏
        ZT.eq (carnotConic d₁ e₁ d₂ e₂ a₁ c₁ a₂ c₂ p₁ q₁ p₂ q₂ p₂ q₂ z0) z0)))) := by
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_mul] at e
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (.andI (ZT.derive ?_)
    (.andI (ZT.derive ?_) (ZT.derive ?_))))) <;>
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] <;> push_cast
  · ring
  · ring
  · ring
  · ring
  · linear_combination (ZT.toZ Γ q₁ * ZT.toZ Γ q₁) * e
  · linear_combination (ZT.toZ Γ q₂ * ZT.toZ Γ q₂) * e

end Carnot

end LeanProofs.IPRA.Geometry.CevaMenelaus
