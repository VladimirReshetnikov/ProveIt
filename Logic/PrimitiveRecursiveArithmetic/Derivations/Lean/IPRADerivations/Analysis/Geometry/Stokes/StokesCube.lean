import IPRADerivations.Foundations.GridSumsOrder
import IPRADerivations.Core.OrderCertificates

/-!
# Constructive Stokes: the finite theorem on a cube, in every dimension

Packet: `analysis/constructive_stokes_ipra_2026-11-21`, `report/03_cube.tex`: `lem:telescoping`
("Exact telescoping", `T_{n,p} = B_{n,p}`) and `thm:finite` ("Finite Stokes with evaluation errors").

The dimension `d` is a parameter of the Lean statements; each instance is one derivation of iPRA. A grid
point is a packed list over the base `⟨N, p⟩` (`Foundations/GridSums`), and every sampled quantity is a
term in the list. Signed quantities are pairs of natural-number terms (positive and negative part), and
all denominators (`h = 1/N`, `2^{-t}`, `2^{-p}`) are cleared by the choice of the tables, so the statements
are inequalities between natural-number terms.

For one coordinate, at outer depth `j` with `k` coordinates inside it (`d = j + (k + 1)`), let
`F = F⁺ − F⁻` be the sampled coefficient, `D = D⁺ − D⁻` the mesh-weighted derivative `h G`, and `E` a bound
for the cell residual `R_a = F(a + e) − F(a) − D(a)`.

* `stokes_alg`: the cancellation behind the theorem, as an inequality certificate;
* `stokes_coordinate`: if `R_a ≤ E_a` at the cells `a` of the grid (hypothesis `H`, used only where the
  facts `P` hold), then

      [∑_{upper face} F − ∑_{lower face} F] − ∑_a D(a) ≤ ∑_a E(a),

  with the faces of `GridSums.faceN`, `face0`. The exact telescoping of the paper is
  `GridSums.grid_telescope`; the sum of the cell inequalities is `GridSumsOrder.gs_le_gen`. The opposite
  inequality is the same statement with `(F⁺, D⁺)` and `(F⁻, D⁻)` exchanged, so the two instances give
  `|B_i − V_i| ≤ ∑ E`;
* `stokes_coordinate_const`: with a cell bound `E = C(base)` that does not depend on the cell, the right
  side is `N^d · C` (`GridSumsOrder.gs_const`): the `N^d` summands of the paper's count;
* `finite_stokes`: the sum over the `d` coordinates (a finite sum indexed in the metatheory):
  `∑_i (B_i − V_i) ≤ ∑_i ∑_a E_i(a)`, the inequality `|B − V| ≤ k N^k ε` of `thm:finite` before the
  denominators are named.

Not derived: the derivation of the cell residual bound from the certificate `eq:derivative-cert` of a
differentiable coefficient (the analytic input), the precision schedule and the rates (`thm:rates`), and the
curved and chain versions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.StokesCube

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.GridSumsContext
open LeanProofs.IPRA.Foundations.GridSumsOrder
open LeanProofs.IPRA.Foundations.TermSums (fsum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The cancellation: from the summed cell inequalities and the two telescoping identities. -/
theorem stokes_alg {SL SR Au Bu A B Dp Dn E f0p fNp f0n fNn : PTm n}
    (hL : Γ ⊢[PRAAx] le SL SR) (eL : Γ ⊢[PRAAx] SL ≐ (Au + B) + Dn)
    (eR : Γ ⊢[PRAAx] SR ≐ ((Bu + A) + Dp) + E)
    (tp : Γ ⊢[PRAAx] Au + f0p ≐ fNp + A) (tn : Γ ⊢[PRAAx] Bu + f0n ≐ fNn + B) :
    Γ ⊢[PRAAx] le ((fNp + f0n) + Dn) (((fNn + f0p) + Dp) + E) := by
  have a := natEq eL; have b := natEq eR; have c := natEq tp; have d := natEq tn
  ipra_le sl hL with c - d + a - b

/-- Finite Stokes along one coordinate of the grid (outer depth `j`, `k` coordinates inside):
`[∑_{upper face} F − ∑_{lower face} F] − ∑ D ≤ ∑ E` when the cell residuals are at most `E`. -/
theorem stokes_coordinate {P : ListFacts} (j k : ℕ) (hP : Steps P 0 (j + (k + 1)))
    {Fp Fn Dp Dn E : PTm 1}
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m), P (j + (k + 1)) m Δ y →
      (Δ ⊢[PRAAx] le (Syn.subst ![y] ((comp Fp (upd k (var 0)) + Fn) + Dn))
        (Syn.subst ![y] (((comp Fn (upd k (var 0)) + Fp) + Dp) + E))))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] le
      ((Syn.subst ![x] (gs 0 j (faceN Fp j k)) + Syn.subst ![x] (gs 0 j (face0 Fn j k))) +
        Syn.subst ![x] (gs 0 (j + (k + 1)) Dn))
      (((Syn.subst ![x] (gs 0 j (faceN Fn j k)) + Syn.subst ![x] (gs 0 j (face0 Fp j k))) +
        Syn.subst ![x] (gs 0 (j + (k + 1)) Dp)) + Syn.subst ![x] (gs 0 (j + (k + 1)) E)) := by
  have hL := gs_le_gen hP H (j + (k + 1)) 0 (by omega) le_rfl m Δ x hx
  have eL := (gs_add (comp Fp (upd k (var 0)) + Fn) Dn 0 (j + (k + 1)) m Δ x).eqTrans
    (congrAdd (gs_add (comp Fp (upd k (var 0))) Fn 0 (j + (k + 1)) m Δ x) (.eqRefl _))
  have eR := (gs_add ((comp Fn (upd k (var 0)) + Fp) + Dp) E 0 (j + (k + 1)) m Δ x).eqTrans
    (congrAdd ((gs_add (comp Fn (upd k (var 0)) + Fp) Dp 0 (j + (k + 1)) m Δ x).eqTrans
      (congrAdd (gs_add (comp Fn (upd k (var 0))) Fp 0 (j + (k + 1)) m Δ x) (.eqRefl _))) (.eqRefl _))
  exact stokes_alg hL eL eR (grid_telescope Fp j k Δ x) (grid_telescope Fn j k Δ x)

/-- The grid sum of a cell bound read from the base is `N^d` times the bound. -/
theorem err_const (d : ℕ) (C : PTm 1) {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs 0 d (comp C (tl d (var 0)))) ≐ gpow (fstT x) d * Syn.subst ![x] C :=
  gs_const C d (F := comp C (tl d (var 0))) (fun m' Δ' y => by
    have hs : Syn.subst ![y] (tl d (var 0) : PTm 1) = tl d y := by simp
    rw [subst_comp, hs]
    exact .eqRefl _) 0 m Δ x

/-- Finite Stokes along one coordinate with a cell bound `C(base)` that does not depend on the cell:
`[∑_{upper face} F − ∑_{lower face} F] − ∑ D ≤ N^d · C`. -/
theorem stokes_coordinate_const {P : ListFacts} (j k : ℕ) (hP : Steps P 0 (j + (k + 1)))
    {Fp Fn Dp Dn : PTm 1} (C : PTm 1)
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m), P (j + (k + 1)) m Δ y →
      (Δ ⊢[PRAAx] le (Syn.subst ![y] ((comp Fp (upd k (var 0)) + Fn) + Dn))
        (Syn.subst ![y] (((comp Fn (upd k (var 0)) + Fp) + Dp) + comp C (tl (j + (k + 1)) (var 0))))))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] le
      ((Syn.subst ![x] (gs 0 j (faceN Fp j k)) + Syn.subst ![x] (gs 0 j (face0 Fn j k))) +
        Syn.subst ![x] (gs 0 (j + (k + 1)) Dn))
      (((Syn.subst ![x] (gs 0 j (faceN Fn j k)) + Syn.subst ![x] (gs 0 j (face0 Fp j k))) +
        Syn.subst ![x] (gs 0 (j + (k + 1)) Dp)) + gpow (fstT x) (j + (k + 1)) * Syn.subst ![x] C) :=
  le_congr (.eqRefl _) (congrAdd (.eqRefl _) (err_const (j + (k + 1)) C Δ x))
    (stokes_coordinate j k hP H Δ x hx)

/-- `thm:finite`, summed over the `d` coordinates: coordinate `c` has outer depth `c` and `d − 1 − c`
coordinates inside it. -/
theorem finite_stokes {P : ListFacts} (d : ℕ) (hP : Steps P 0 d) (Fp Fn Dp Dn E : Fin d → PTm 1)
    (H : ∀ (c : Fin d) (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m), P d m Δ y →
      (Δ ⊢[PRAAx] le (Syn.subst ![y] ((comp (Fp c) (upd (d - 1 - c.val) (var 0)) + Fn c) + Dn c))
        (Syn.subst ![y] (((comp (Fn c) (upd (d - 1 - c.val) (var 0)) + Fp c) + Dp c) + E c))))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] le
      (fsum d (fun c => (Syn.subst ![x] (gs 0 c.val (faceN (Fp c) c.val (d - 1 - c.val))) +
          Syn.subst ![x] (gs 0 c.val (face0 (Fn c) c.val (d - 1 - c.val)))) +
        Syn.subst ![x] (gs 0 d (Dn c))))
      (fsum d (fun c => ((Syn.subst ![x] (gs 0 c.val (faceN (Fn c) c.val (d - 1 - c.val))) +
          Syn.subst ![x] (gs 0 c.val (face0 (Fp c) c.val (d - 1 - c.val)))) +
        Syn.subst ![x] (gs 0 d (Dp c))) + Syn.subst ![x] (gs 0 d (E c)))) := by
  refine fsum_le (fun c => ?_)
  have hd : c.val + (d - 1 - c.val + 1) = d := by have := c.isLt; omega
  have hP' : Steps P 0 (c.val + (d - 1 - c.val + 1)) := by rw [hd]; exact hP
  have h := stokes_coordinate (P := P) c.val (d - 1 - c.val) hP'
    (fun m' Δ' y hy => H c m' Δ' y (by rw [hd] at hy; exact hy)) Δ x hx
  rw [hd] at h
  exact h

end LeanProofs.IPRA.Analysis.StokesCube
