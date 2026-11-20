import IPRADerivations.DiophantineNumberTheory.ConicNonzero

/-!
# The inverse of the conic parametrization

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:conic-param`, the construction of
the inverse and the recovery of every parameter. For a transformed conic point `(u, v, w)` with
`u L(v, w) + R(v, w) = 0`:

* `inverse_L_ne_zero`: "If `(v, w) ≠ (0, 0)`, then `L(v, w) ≠ 0`: otherwise this equation would also give
  `R(v, w) = 0`, contrary to the two identities above" (via `ConicNonzero.no_common_zero`);
* `inverse_scaling`: "`F(v, w) = (−R(v, w), v L(v, w), w L(v, w)) = L(v, w)(u, v, w)`", so the inverse parameter
  is `[v : w]`;
* `recover_regular`: when `L(s, t) ≠ 0` the last two coordinates `(s L, t L)` of `F(s, t)` give back `[s : t]`
  (cross products agree);
* `recover_tangent`: when `L(s, t) = 0`, `(s, t)` is proportional to `(−m, ℓ)` (`s ℓ = t (−m)`);
* `tangent_t_ne_zero`: "if `ℓ ≠ 0`, the equation `ℓ s = −m t` ... forces `t ≠ 0`" (for `(s, t) ≠ 0`);
* `tangent_emm_ne_zero`, `tangent_t_zero`: "if `ℓ = 0`, then `m ≠ 0`, `t = 0`" (from `r ≠ 0`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.ConicIdentities (Form)
open LeanProofs.IPRA.DiophantineNumberTheory.ZTCancel (zt_no_zero_div)
open LeanProofs.IPRA.DiophantineNumberTheory.ConicNonzero (no_common_zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `L` in terms of the atoms `ℓ`, `m`. -/
theorem toZ_L' (Q : Form n) (p0 p1 p2 V W : ZT n) :
    ZT.toZ Γ (Q.L p0 p1 p2 V W) = ZT.toZ Γ (Q.ell p0 p1 p2) * ZT.toZ Γ V + ZT.toZ Γ (Q.emm p0 p1 p2) * ZT.toZ Γ W := by
  simp [Form.L]

/-- On the transformed conic `u L(v, w) + R(v, w) = 0`, a nonzero `(v, w)` has `L(v, w) ≠ 0`. -/
theorem inverse_L_ne_zero (Q : Form n) {p0 p1 p2 u v w : ZT n}
    (hr : Γ ⊢[PRAAx] neg (ZT.eq (Q.r p0 p1 p2) (ZT.natLit 0)))
    (hu : Γ ⊢[PRAAx] ZT.eq (u * Q.L p0 p1 p2 v w + Q.R v w) (ZT.natLit 0))
    (hvw : Γ ⊢[PRAAx] neg (ZT.eq v (ZT.natLit 0) ⋏ ZT.eq w (ZT.natLit 0))) :
    Γ ⊢[PRAAx] neg (ZT.eq (Q.L p0 p1 p2 v w) (ZT.natLit 0)) := by
  refine .impI ?_
  have h0 : (ZT.eq (Q.L p0 p1 p2 v w) (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq (Q.L p0 p1 p2 v w) (ZT.natLit 0) := Prf.hyp0
  have hR : (ZT.eq (Q.L p0 p1 p2 v w) (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq (Q.R v w) (ZT.natLit 0) := by
    have eu := ZT.toZ_eq (hu.wk : (ZT.eq (Q.L p0 p1 p2 v w) (ZT.natLit 0) :: Γ) ⊢[PRAAx] _)
    have e0 := ZT.toZ_eq h0
    refine ZT.derive ?_
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at eu e0 ⊢
    rw [e0] at eu
    linear_combination eu
  exact Prf.impE hvw.wk (no_common_zero Q hr.wk h0 hR)

/-- `F(v, w) = L(v, w) (u, v, w)` on the transformed conic. -/
theorem inverse_scaling (Q : Form n) {p0 p1 p2 u v w : ZT n}
    (hu : Γ ⊢[PRAAx] ZT.eq (u * Q.L p0 p1 p2 v w + Q.R v w) (ZT.natLit 0)) :
    (Γ ⊢[PRAAx] ZT.eq (-Q.R v w) (Q.L p0 p1 p2 v w * u)) ∧
    (Γ ⊢[PRAAx] ZT.eq (v * Q.L p0 p1 p2 v w) (Q.L p0 p1 p2 v w * v)) ∧
    (Γ ⊢[PRAAx] ZT.eq (w * Q.L p0 p1 p2 v w) (Q.L p0 p1 p2 v w * w)) := by
  have eu := ZT.toZ_eq hu
  refine ⟨ZT.derive ?_, ZT.derive ?_, ZT.derive ?_⟩
  · simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, ZT.toZ_neg] at eu ⊢
    linear_combination -eu
  · simp only [ZT.toZ_mul]; ring
  · simp only [ZT.toZ_mul]; ring

/-- The last two coordinates of `F(s, t)` give back `[s : t]`: `(s L) t = (t L) s`. -/
theorem recover_regular (Q : Form n) (p0 p1 p2 s t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (s * Q.L p0 p1 p2 s t * t) (t * Q.L p0 p1 p2 s t * s) :=
  ZT.derive (by simp only [ZT.toZ_mul]; ring)

/-- When `L(s, t) = 0`, `[s : t] = [−m : ℓ]`: `s ℓ = t (−m)`. -/
theorem recover_tangent (Q : Form n) {p0 p1 p2 s t : ZT n}
    (hL : Γ ⊢[PRAAx] ZT.eq (Q.L p0 p1 p2 s t) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (s * Q.ell p0 p1 p2) (t * -Q.emm p0 p1 p2) := by
  have e := ZT.toZ_eq hL
  refine ZT.derive ?_
  simp only [toZ_L', ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] at e ⊢
  linear_combination e

/-- If `ℓ ≠ 0`, `L(s, t) = 0` and `(s, t) ≠ 0`, then `t ≠ 0`. -/
theorem tangent_t_ne_zero (Q : Form n) {p0 p1 p2 s t : ZT n}
    (hl : Γ ⊢[PRAAx] neg (ZT.eq (Q.ell p0 p1 p2) (ZT.natLit 0)))
    (hL : Γ ⊢[PRAAx] ZT.eq (Q.L p0 p1 p2 s t) (ZT.natLit 0))
    (hst : Γ ⊢[PRAAx] neg (ZT.eq s (ZT.natLit 0) ⋏ ZT.eq t (ZT.natLit 0))) :
    Γ ⊢[PRAAx] neg (ZT.eq t (ZT.natLit 0)) := by
  refine .impI ?_
  have ht : (ZT.eq t (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq t (ZT.natLit 0) := Prf.hyp0
  have hs : (ZT.eq t (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq s (ZT.natLit 0) := by
    refine zt_no_zero_div hl.wk ?_
    have e := ZT.toZ_eq (hL.wk : (ZT.eq t (ZT.natLit 0) :: Γ) ⊢[PRAAx] _)
    have et := ZT.toZ_eq ht
    refine ZT.derive ?_
    simp only [toZ_L', ZT.toZ_mul, ZT.toZ_natLit] at e et ⊢
    rw [et] at e
    linear_combination e
  exact Prf.impE hst.wk (.andI hs ht)

/-- If `ℓ = 0` and `r ≠ 0`, then `m ≠ 0`. -/
theorem tangent_emm_ne_zero (Q : Form n) {p0 p1 p2 : ZT n}
    (hr : Γ ⊢[PRAAx] neg (ZT.eq (Q.r p0 p1 p2) (ZT.natLit 0)))
    (hl : Γ ⊢[PRAAx] ZT.eq (Q.ell p0 p1 p2) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] neg (ZT.eq (Q.emm p0 p1 p2) (ZT.natLit 0)) := by
  refine .impI ?_
  have el := ZT.toZ_eq (hl.wk : (ZT.eq (Q.emm p0 p1 p2) (ZT.natLit 0) :: Γ) ⊢[PRAAx] _)
  have em := ZT.toZ_eq (Prf.hyp0 : (ZT.eq (Q.emm p0 p1 p2) (ZT.natLit 0) :: Γ) ⊢[PRAAx] _)
  have z : (ZT.eq (Q.emm p0 p1 p2) (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq (Q.r p0 p1 p2) (ZT.natLit 0) := by
    refine ZT.derive ?_
    rw [Form.toZ_r, el, em]
    simp only [ZT.toZ_natLit]; push_cast; ring
  exact Prf.impE hr.wk z

/-- If `ℓ = 0`, `r ≠ 0` and `L(s, t) = 0`, then `t = 0` (so `[s : t] = [1 : 0] = [−m : ℓ]`). -/
theorem tangent_t_zero (Q : Form n) {p0 p1 p2 s t : ZT n}
    (hr : Γ ⊢[PRAAx] neg (ZT.eq (Q.r p0 p1 p2) (ZT.natLit 0)))
    (hl : Γ ⊢[PRAAx] ZT.eq (Q.ell p0 p1 p2) (ZT.natLit 0))
    (hL : Γ ⊢[PRAAx] ZT.eq (Q.L p0 p1 p2 s t) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq t (ZT.natLit 0) := by
  refine zt_no_zero_div (tangent_emm_ne_zero Q hr hl) ?_
  have e := ZT.toZ_eq hL
  have el := ZT.toZ_eq hl
  refine ZT.derive ?_
  simp only [toZ_L', ZT.toZ_mul, ZT.toZ_natLit] at e el ⊢
  rw [el] at e
  linear_combination e

end LeanProofs.IPRA.DiophantineNumberTheory.ConicInverse
