import IPRADerivations.Analysis.PolynomialRemainder

/-!
# Value and Lipschitz bounds of multivariate polynomials on a box

Packet: `foundations/ipra_local_global`, `paper/04_ode.tex`, Lemma `lem:ode-polybound` ("Finite polynomial
bounds"): if `‖x‖, ‖y‖ ≤ B`, then `‖F(x)‖ ≤ M` and `‖F(x) − F(y)‖ ≤ L ‖x − y‖`. "Replace the factors at `x`
by the factors at `y` one at a time. The resulting telescoping identity has `|α|` terms".

For a polynomial expression `e : PE d` (`Analysis/PolynomialRemainder`), in the sup norm, componentwise for
the vector field `F`:

* `val_bound` (of `PolynomialRemainder`): `|e(x)| ≤ bA e B`, the constant `M`;
* `lip_bound`: if `|x_i|, |y_i| ≤ B` and `|x_i − y_i| ≤ N`, then `|e(x) − e(y)| ≤ bL e B · N`: the
  telescoping is compiled along the expression, `f(x) g(x) − f(y) g(y) = f(x) (g(x) − g(y)) + g(y) (f(x) − f(y))`,
  so the Lipschitz constant `L` is the same structural bound `bL` as the linear term of the Taylor remainder;
* `poly_bounds`: both bounds together (`lem:ode-polybound`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.MultivariatePolyBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k d : ℕ} {Γ : List (Fm PTm k)} {x y : Fin d → ZT k} {B N : PTm k}

/-- `|e(x) − e(y)| ≤ bL e B · N` on the box. -/
theorem lip_bound (hx : ∀ i, Γ ⊢[PRAAx] AbsLe (x i) B) (hy : ∀ i, Γ ⊢[PRAAx] AbsLe (y i) B)
    (hxy : ∀ i, Γ ⊢[PRAAx] AbsLe (x i - y i) N) (e : PE d) :
    Γ ⊢[PRAAx] AbsLe (ev e x - ev e y) (bL e B * N) := by
  induction e with
  | const p q =>
    refine abs_congr (ZT.derive ?_) (abs_zero _)
    simp only [ev, ZT.toZ_sub, ZT.toZ_ofNat, Q.mk_zero, map_zero]
    ring
  | var i => exact abs_mono (by show Γ ⊢[PRAAx] le N (one * N); ipra_le 0) (hxy i)
  | add f g ihf ihg =>
    refine abs_mono (by
        show Γ ⊢[PRAAx] le (bL f B * N + bL g B * N) ((bL f B + bL g B) * N)
        ipra_le 0) (abs_congr (ZT.derive ?_) (abs_add ihf ihg))
    simp only [ev, ZT.toZ_sub, ZT.toZ_add]
    ring
  | mul f g ihf ihg =>
    refine abs_mono (by
        show Γ ⊢[PRAAx] le (bA f B * (bL g B * N) + bA g B * (bL f B * N))
          ((bA f B * bL g B + bA g B * bL f B) * N)
        ipra_le 0)
      (abs_congr (ZT.derive ?_) (abs_add (abs_mul (val_bound hx f) ihg) (abs_mul (val_bound hy g) ihf)))
    simp only [ev, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_mul]
    ring

/-- `lem:ode-polybound`, componentwise for `F : Fin d' → PE d`: `|F_j(x)| ≤ bA (F_j) B` and
`|F_j(x) − F_j(y)| ≤ bL (F_j) B · N`. -/
theorem poly_bounds {d' : ℕ} (F : Fin d' → PE d) (hx : ∀ i, Γ ⊢[PRAAx] AbsLe (x i) B)
    (hy : ∀ i, Γ ⊢[PRAAx] AbsLe (y i) B) (hxy : ∀ i, Γ ⊢[PRAAx] AbsLe (x i - y i) N) (j : Fin d') :
    Γ ⊢[PRAAx] AbsLe (ev (F j) x) (bA (F j) B) ⋏ AbsLe (ev (F j) x - ev (F j) y) (bL (F j) B * N) :=
  .andI (val_bound hx (F j)) (lip_bound hx hy hxy (F j))

end LeanProofs.IPRA.Analysis.MultivariatePolyBounds
