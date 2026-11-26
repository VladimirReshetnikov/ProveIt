import IPRADerivations.Core.IntOrder
import IPRADerivations.Core.OrderCertificates

/-!
# A first-order Taylor remainder for multivariate polynomial expressions

Packet: `foundations/ipra_local_global`, `paper/04_ode.tex`, Theorem `thm:ode-conservation` ("Polynomial
conservation compiler"), the remainder estimate `eq:ode-polyremainder`:
`|H(x + v) − H(x) − ∇H(x)·v| ≤ R_H ‖v‖²` for `‖x‖ ≤ B`, `‖v‖ ≤ MT`, "by the multivariate binomial
expansion ... in every remaining term retain two factors of `v` and bound the other factors by `D`".

Instead of expanding monomials, the remainder is compiled along the expression: a polynomial in `d` variables
is a (meta-level) expression `PE d` built from integer constants, coordinates, sums and products, read as
an integer term `ev e x` (`ZT`: pairs of naturals). Its directional derivative `dv e x v` is computed by the
sum and product rules. Three explicit primitive-recursive bounds are computed along the expression from the
coordinate bound `B` and a bound `D ≥ ‖v‖`:

* `bA e B` bounds the value (`val_bound`), `bL e B` the linear term per unit of `‖v‖` (`lin_bound`), and
* `bR e B D` the remainder: `remainder` (`eq:ode-polyremainder`, sup norm): if every `|x_i| ≤ B`,
  `|x_i + v_i| ≤ B`, `|v_i| ≤ N` and `N ≤ D`, then
  `|e(x + v) − e(x) − Dv e(x)| ≤ bR e B D · N²`.
  For a product, `fg(x + v) − fg(x) − (f Dg + g Df) = f r_g + Df Dg + Df r_g + r_f g(x + v)`, and the
  cubic term `Df r_g` is bounded using `N ≤ D`.

The bound calculus on integer terms, `AbsLe u b` (`|u| ≤ b`): `abs_congr`, `abs_mono`, `abs_add`,
`abs_mul` (with `2(ab − uw) = (a − u)(b + w) + (a + u)(b − w)` and cancellation of the factor `2`).

* `dv_smul`: `Dv` is linear in `v`: `Dv e(x)` at `c v` is `c · Dv e(x)` at `v`;
* `conservation_step` (the use in `thm:ode-conservation`): if the certificate `∇H(x)·F(x) = 0` holds at `x`,
  a step `v = c F(x)` changes `H` by at most `bR H B D · N²`.

The telescoping over the Euler steps is `Foundations/OdeConservation`; the represented flow is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PolynomialRemainder

open_ipra

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Absolute-value bounds on integer terms -/

/-- `|u| ≤ b`. -/
def AbsLe (u : ZT k) (b : PTm k) : Fm PTm k := zle u (ZT.ofNat b) ⋏ zle (-(ZT.ofNat b)) u

theorem abs_hi {u : ZT k} {b : PTm k} (h : Γ ⊢[PRAAx] AbsLe u b) :
    Γ ⊢[PRAAx] le (u.pos + zero) (b + u.neg) := Prf.andE₁ h

theorem abs_lo {u : ZT k} {b : PTm k} (h : Γ ⊢[PRAAx] AbsLe u b) :
    Γ ⊢[PRAAx] le (zero + u.neg) (u.pos + b) := Prf.andE₂ h

theorem abs_of {u : ZT k} {b : PTm k} (h₁ : Γ ⊢[PRAAx] le (u.pos + zero) (b + u.neg))
    (h₂ : Γ ⊢[PRAAx] le (zero + u.neg) (u.pos + b)) : Γ ⊢[PRAAx] AbsLe u b := .andI h₁ h₂

theorem abs_congr {u u' : ZT k} {b : PTm k} (e : Γ ⊢[PRAAx] ZT.eq u u') (h : Γ ⊢[PRAAx] AbsLe u b) :
    Γ ⊢[PRAAx] AbsLe u' b := by
  have ee := natEq e
  have h₁ := abs_hi h
  have h₂ := abs_lo h
  exact abs_of (by ipra_le sl h₁ using linear_combination ee) (by ipra_le sl h₂ using linear_combination -ee)

theorem abs_mono {u : ZT k} {a b : PTm k} (hab : Γ ⊢[PRAAx] le a b) (h : Γ ⊢[PRAAx] AbsLe u a) :
    Γ ⊢[PRAAx] AbsLe u b := by
  have h₁ := abs_hi h
  have h₂ := abs_lo h
  exact abs_of (by ipra_le sl h₁ + sl hab) (by ipra_le sl h₂ + sl hab)

theorem abs_zero (b : PTm k) : Γ ⊢[PRAAx] AbsLe (ZT.ofNat zero) b :=
  abs_of (by show Γ ⊢[PRAAx] le (zero + zero) (b + zero); ipra_le 𝔞 b)
    (by show Γ ⊢[PRAAx] le (zero + zero) (zero + b); ipra_le 𝔞 b)

theorem abs_add {u w : ZT k} {a b : PTm k} (hu : Γ ⊢[PRAAx] AbsLe u a) (hw : Γ ⊢[PRAAx] AbsLe w b) :
    Γ ⊢[PRAAx] AbsLe (u + w) (a + b) := by
  have u₁ := abs_hi hu; have u₂ := abs_lo hu
  have w₁ := abs_hi hw; have w₂ := abs_lo hw
  refine abs_of ?_ ?_
  · show Γ ⊢[PRAAx] le ((u.pos + w.pos) + zero) ((a + b) + (u.neg + w.neg))
    ipra_le sl u₁ + sl w₁
  · show Γ ⊢[PRAAx] le (zero + (u.neg + w.neg)) ((u.pos + w.pos) + (a + b))
    ipra_le sl u₂ + sl w₂

theorem abs_mul {u w : ZT k} {a b : PTm k} (hu : Γ ⊢[PRAAx] AbsLe u a) (hw : Γ ⊢[PRAAx] AbsLe w b) :
    Γ ⊢[PRAAx] AbsLe (u * w) (a * b) := by
  have u₁ := abs_hi hu; have u₂ := abs_lo hu
  have w₁ := abs_hi hw; have w₂ := abs_lo hw
  have eu1 := natEq (eq_add_of_le u₁); have eu2 := natEq (eq_add_of_le u₂)
  have ew1 := natEq (eq_add_of_le w₁); have ew2 := natEq (eq_add_of_le w₂)
  refine abs_of ?_ ?_
  · show Γ ⊢[PRAAx] le ((u.pos * w.pos + u.neg * w.neg) + zero) (a * b + (u.pos * w.neg + u.neg * w.pos))
    refine mul_le_cancel (d' := one) ?_
    refine le_of_eq_add (d := monus (a + u.neg) (u.pos + zero) * monus (w.pos + b) (zero + w.neg) +
      monus (u.pos + a) (zero + u.neg) * monus (b + w.neg) (w.pos + zero)) ?_
    ipra_lc 𝔞 (monus (w.pos + b) (zero + w.neg)) * eu1 + 𝔞 (monus (b + w.neg) (w.pos + zero)) * eu2 +
      (𝔞 a - 𝔞 u.neg + 𝔞 u.pos) * ew1 + (𝔞 a + 𝔞 u.neg - 𝔞 u.pos) * ew2
  · show Γ ⊢[PRAAx] le (zero + (u.pos * w.neg + u.neg * w.pos)) ((u.pos * w.pos + u.neg * w.neg) + a * b)
    refine mul_le_cancel (d' := one) ?_
    refine le_of_eq_add (d := monus (a + u.neg) (u.pos + zero) * monus (b + w.neg) (w.pos + zero) +
      monus (u.pos + a) (zero + u.neg) * monus (w.pos + b) (zero + w.neg)) ?_
    ipra_lc 𝔞 (monus (b + w.neg) (w.pos + zero)) * eu1 + 𝔞 (monus (w.pos + b) (zero + w.neg)) * eu2 +
      (𝔞 a + 𝔞 u.neg - 𝔞 u.pos) * ew1 + (𝔞 a - 𝔞 u.neg + 𝔞 u.pos) * ew2

/-! ## Polynomial expressions -/

/-- Polynomial expressions in `d` variables with integer constants `p − q`. -/
inductive PE (d : ℕ) where
  | const (p q : ℕ)
  | var (i : Fin d)
  | add (f g : PE d)
  | mul (f g : PE d)

variable {d : ℕ}

/-- The value at `x`. -/
def ev : PE d → (Fin d → ZT k) → ZT k
  | .const p q, _ => ⟨num p, num q⟩
  | .var i, x => x i
  | .add f g, x => ev f x + ev g x
  | .mul f g, x => ev f x * ev g x

/-- The directional derivative `∇e(x) · v`, by the sum and product rules. -/
def dv : PE d → (Fin d → ZT k) → (Fin d → ZT k) → ZT k
  | .const _ _, _, _ => ZT.ofNat zero
  | .var i, _, v => v i
  | .add f g, x, v => dv f x v + dv g x v
  | .mul f g, x, v => ev f x * dv g x v + ev g x * dv f x v

/-- The value bound on `|x_i| ≤ B`. -/
def bA : PE d → PTm k → PTm k
  | .const p q, _ => num p + num q
  | .var _, B => B
  | .add f g, B => bA f B + bA g B
  | .mul f g, B => bA f B * bA g B

/-- The bound of the linear term per unit of `|v_i|`. -/
def bL : PE d → PTm k → PTm k
  | .const _ _, _ => zero
  | .var _, _ => one
  | .add f g, B => bL f B + bL g B
  | .mul f g, B => bA f B * bL g B + bA g B * bL f B

/-- The remainder constant, with `D` a bound of `|v_i|`. -/
def bR : PE d → PTm k → PTm k → PTm k
  | .const _ _, _, _ => zero
  | .var _, _, _ => zero
  | .add f g, B, D => bR f B D + bR g B D
  | .mul f g, B, D => bA f B * bR g B D + bL f B * bL g B + bL f B * bR g B D * D + bR f B D * bA g B

/-- The remainder `e(x + v) − e(x) − ∇e(x)·v`. -/
def rem (e : PE d) (x v : Fin d → ZT k) : ZT k := ev e (fun i => x i + v i) - ev e x - dv e x v

variable {x v : Fin d → ZT k} {B N D : PTm k}

theorem val_bound (hx : ∀ i, Γ ⊢[PRAAx] AbsLe (x i) B) (e : PE d) : Γ ⊢[PRAAx] AbsLe (ev e x) (bA e B) := by
  induction e with
  | const p q =>
    exact abs_of (by show Γ ⊢[PRAAx] le (num p + zero) ((num p + num q) + num q); ipra_le 𝔞 (num q) + 𝔞 (num q))
      (by show Γ ⊢[PRAAx] le (zero + num q) (num p + (num p + num q)); ipra_le 𝔞 (num p) + 𝔞 (num p))
  | var i => exact hx i
  | add f g ihf ihg => exact abs_add ihf ihg
  | mul f g ihf ihg => exact abs_mul ihf ihg

theorem lin_bound (hx : ∀ i, Γ ⊢[PRAAx] AbsLe (x i) B) (hv : ∀ i, Γ ⊢[PRAAx] AbsLe (v i) N) (e : PE d) :
    Γ ⊢[PRAAx] AbsLe (dv e x v) (bL e B * N) := by
  induction e with
  | const p q => exact abs_zero _
  | var i => exact abs_mono (by show Γ ⊢[PRAAx] le N (one * N); ipra_le 0) (hv i)
  | add f g ihf ihg =>
    exact abs_mono (by show Γ ⊢[PRAAx] le (bL f B * N + bL g B * N) ((bL f B + bL g B) * N); ipra_le 0)
      (abs_add ihf ihg)
  | mul f g ihf ihg =>
    exact abs_mono (by
        show Γ ⊢[PRAAx] le (bA f B * (bL g B * N) + bA g B * (bL f B * N))
          ((bA f B * bL g B + bA g B * bL f B) * N)
        ipra_le 0)
      (abs_add (abs_mul (val_bound hx f) ihg) (abs_mul (val_bound hx g) ihf))

/-- `eq:ode-polyremainder`: `|e(x + v) − e(x) − ∇e(x)·v| ≤ bR e B D · N²`. -/
theorem remainder (hx : ∀ i, Γ ⊢[PRAAx] AbsLe (x i) B) (hxv : ∀ i, Γ ⊢[PRAAx] AbsLe (x i + v i) B)
    (hv : ∀ i, Γ ⊢[PRAAx] AbsLe (v i) N) (hND : Γ ⊢[PRAAx] le N D) (e : PE d) :
    Γ ⊢[PRAAx] AbsLe (rem e x v) (bR e B D * (N * N)) := by
  induction e with
  | const p q =>
    refine abs_congr (ZT.derive ?_) (abs_zero _)
    simp only [rem, ev, dv, ZT.toZ_sub, ZT.toZ_ofNat, Q.mk_zero, map_zero]
    ring
  | var i =>
    refine abs_congr (ZT.derive ?_) (abs_zero _)
    simp only [rem, ev, dv, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_ofNat, Q.mk_zero, map_zero]
    ring
  | add f g ihf ihg =>
    refine abs_mono (by
        show Γ ⊢[PRAAx] le (bR f B D * (N * N) + bR g B D * (N * N)) ((bR f B D + bR g B D) * (N * N))
        ipra_le 0) (abs_congr (ZT.derive ?_) (abs_add ihf ihg))
    simp only [rem, ev, dv, ZT.toZ_sub, ZT.toZ_add]
    ring
  | mul f g ihf ihg =>
    have a1 := abs_mul (val_bound hx f) ihg
    have a2 := abs_mul (lin_bound hx hv f) (lin_bound hx hv g)
    have a3 := abs_mul (lin_bound hx hv f) ihg
    have a4 := abs_mul ihf (val_bound hxv g)
    refine abs_mono ?_ (abs_congr (ZT.derive ?_) (abs_add (abs_add (abs_add a1 a2) a3) a4))
    · show Γ ⊢[PRAAx] le (bA f B * (bR g B D * (N * N)) + bL f B * N * (bL g B * N) +
          bL f B * N * (bR g B D * (N * N)) + bR f B D * (N * N) * bA g B)
        ((bA f B * bR g B D + bL f B * bL g B + bL f B * bR g B D * D + bR f B D * bA g B) * (N * N))
      ipra_le 𝔞 (bL f B) * 𝔞 (bR g B D) * 𝔞 N * 𝔞 N * sl hND
    · simp only [rem, ev, dv, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_mul]
      ring

/-- `∇e(x)` is linear in the direction: at `c v` it is `c` times its value at `v`. -/
theorem dv_smul (c : ZT k) (e : PE d) :
    ZT.toZ Γ (dv e x (fun i => c * v i)) = ZT.toZ Γ c * ZT.toZ Γ (dv e x v) := by
  induction e with
  | const p q =>
    simp only [dv, ZT.toZ_ofNat, Q.mk_zero, map_zero]
    ring
  | var i => simp only [dv, ZT.toZ_mul]
  | add f g ihf ihg => simp only [dv, ZT.toZ_add, ihf, ihg]; ring
  | mul f g ihf ihg => simp only [dv, ZT.toZ_add, ZT.toZ_mul, ihf, ihg]; ring

/-- The conservation step of `thm:ode-conservation`: if `∇H(x)·F(x) = 0`, a step `v = c F(x)` with the
bounds of `remainder` changes `H` by at most `bR H B D · N²`. -/
theorem conservation_step {F : Fin d → ZT k} {c : ZT k} (H : PE d)
    (hcert : Γ ⊢[PRAAx] ZT.eq (dv H x F) (ZT.ofNat zero))
    (hx : ∀ i, Γ ⊢[PRAAx] AbsLe (x i) B) (hxv : ∀ i, Γ ⊢[PRAAx] AbsLe (x i + c * F i) B)
    (hv : ∀ i, Γ ⊢[PRAAx] AbsLe (c * F i) N) (hND : Γ ⊢[PRAAx] le N D) :
    Γ ⊢[PRAAx] AbsLe (ev H (fun i => x i + c * F i) - ev H x) (bR H B D * (N * N)) := by
  have r := remainder (v := fun i => c * F i) hx hxv hv hND H
  refine abs_congr (ZT.derive ?_) r
  have e0 := ZT.toZ_eq hcert
  have sm := dv_smul (Γ := Γ) (x := x) (v := F) c H
  simp only [rem, ZT.toZ_sub] at e0 ⊢
  rw [sm]
  simp only [ZT.toZ_ofNat] at e0
  simp only [Q.mk_zero, map_zero] at e0
  rw [e0]
  ring

end LeanProofs.IPRA.Analysis.PolynomialRemainder
