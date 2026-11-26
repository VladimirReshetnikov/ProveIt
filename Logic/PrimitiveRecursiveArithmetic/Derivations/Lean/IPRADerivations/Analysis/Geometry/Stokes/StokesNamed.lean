import IPRADerivations.Analysis.Geometry.Stokes.StokesCube

/-!
# Constructive Stokes: the finite theorem with its named error bound

Packet: `analysis/constructive_stokes_ipra_2026-11-21`, `report/03_cube.tex`, `thm:finite`:
`|V_{n,p} − B_{n,p}| ≤ k 2^{-t} + k (2N + 1) 2^{-p}` with `N = 2^n`, from the coordinate remainder certificate
`eq:derivative-cert`, `|F_i(x + h e_i, p) − F_i(x, p) − h G_i(x, p)| ≤ h 2^{-t} + (2 + h) 2^{-p}`.

`StokesCube.finite_stokes` is this theorem for arbitrary cell bounds. Here the bound is the one of the
certificate. With `h = 1/N`, put every sampled value on the scale `S = N · 2^{t+p}`. The certificate then reads

    R_a ≤ C,      C = 2^p + (2N + 1) · 2^t,

a bound that depends only on the base of the grid, and the conclusion `∑_i (B_i − V_i) ≤ ∑_i N^d · C` is, after
division by `S · N^{d−1}` (the scale times the face weight `h^{d−1}`), the paper's
`d · 2^{-t} + d (2N + 1) 2^{-p}`: indeed `d N^d C = S N^{d−1} · (d 2^{-t} + d (2N + 1) 2^{-p})`.

* `finite_stokes_const`: `thm:finite` for a cell bound `C(base)` common to all coordinates, with the right side
  `∑_i N^d · C`;
* `namedC`: the bound `2^p + (2N + 1) · 2^t`, with `t` and `p` terms in the base;
* **`finite_stokes_named`**: `thm:finite` with this bound. Its hypothesis `H` is the certificate
  `eq:derivative-cert` at the cells of the grid, on the scale `S`.

The opposite inequality is the same statement with the positive and negative parts exchanged, as in
`StokesCube`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.StokesNamed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.GridSumsContext
open LeanProofs.IPRA.Foundations.GridSumsOrder
open LeanProofs.IPRA.Foundations.TermSums (fsum fsum_congr)
open LeanProofs.IPRA.Analysis.StokesCube (err_const finite_stokes)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `thm:finite` with a cell bound `C(base)` common to all coordinates: the error is `∑_i N^d · C`. -/
theorem finite_stokes_const {P : ListFacts} (d : ℕ) (hP : Steps P 0 d) (Fp Fn Dp Dn : Fin d → PTm 1)
    (C : PTm 1)
    (H : ∀ (c : Fin d) (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m), P d m Δ y →
      (Δ ⊢[PRAAx] le (Syn.subst ![y] ((comp (Fp c) (upd (d - 1 - c.val) (var 0)) + Fn c) + Dn c))
        (Syn.subst ![y] (((comp (Fn c) (upd (d - 1 - c.val) (var 0)) + Fp c) + Dp c) +
          comp C (tl d (var 0))))))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] le
      (fsum d (fun c => (Syn.subst ![x] (gs 0 c.val (faceN (Fp c) c.val (d - 1 - c.val))) +
          Syn.subst ![x] (gs 0 c.val (face0 (Fn c) c.val (d - 1 - c.val)))) +
        Syn.subst ![x] (gs 0 d (Dn c))))
      (fsum d (fun c => ((Syn.subst ![x] (gs 0 c.val (faceN (Fn c) c.val (d - 1 - c.val))) +
          Syn.subst ![x] (gs 0 c.val (face0 (Fp c) c.val (d - 1 - c.val)))) +
        Syn.subst ![x] (gs 0 d (Dp c))) + gpow (fstT x) d * Syn.subst ![x] C)) :=
  le_congr (.eqRefl _) (fsum_congr (fun _ => congrAdd (.eqRefl _) (err_const d C Δ x)))
    (finite_stokes d hP Fp Fn Dp Dn (fun _ => comp C (tl d (var 0))) H Δ x hx)

/-- The cell bound of the certificate on the scale `N · 2^{t+p}`: `2^p + (2N + 1) · 2^t`, where `N` is the first
component of the base (variable `0`) and `t`, `p` are terms in the base. -/
abbrev namedC (t p : PTm 1) : PTm 1 := pw two p + (two * fstT (var 0) + one) * pw two t

/-- **`thm:finite`** with the bound of the certificate: `∑_i (B_i − V_i) ≤ ∑_i N^d · (2^p + (2N + 1) 2^t)`. -/
theorem finite_stokes_named {P : ListFacts} (d : ℕ) (hP : Steps P 0 d) (Fp Fn Dp Dn : Fin d → PTm 1)
    (t p : PTm 1)
    (H : ∀ (c : Fin d) (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m), P d m Δ y →
      (Δ ⊢[PRAAx] le (Syn.subst ![y] ((comp (Fp c) (upd (d - 1 - c.val) (var 0)) + Fn c) + Dn c))
        (Syn.subst ![y] (((comp (Fn c) (upd (d - 1 - c.val) (var 0)) + Fp c) + Dp c) +
          comp (namedC t p) (tl d (var 0))))))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] le
      (fsum d (fun c => (Syn.subst ![x] (gs 0 c.val (faceN (Fp c) c.val (d - 1 - c.val))) +
          Syn.subst ![x] (gs 0 c.val (face0 (Fn c) c.val (d - 1 - c.val)))) +
        Syn.subst ![x] (gs 0 d (Dn c))))
      (fsum d (fun c => ((Syn.subst ![x] (gs 0 c.val (faceN (Fn c) c.val (d - 1 - c.val))) +
          Syn.subst ![x] (gs 0 c.val (face0 (Fp c) c.val (d - 1 - c.val)))) +
        Syn.subst ![x] (gs 0 d (Dp c))) + gpow (fstT x) d * Syn.subst ![x] (namedC t p))) :=
  finite_stokes_const d hP Fp Fn Dp Dn (namedC t p) H Δ x hx

end LeanProofs.IPRA.Analysis.StokesNamed
