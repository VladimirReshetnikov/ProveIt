import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.CertificateTactics

/-!
# An approximate Brouwer fixed point on the interval, with a primitive recursive witness

Packet: `topology/approximate_brouwer_ipra`, `brouwer.tex`, Theorem `thm:main` and Lemma `lem:finite` in
dimension one, complete and uniform in the mesh and in the map. The grid is `{0, …, N}` (the points `i/N` of
`[0, 1]`), with `N` an object-level term; the samples are a body `g(i, x)` (the value `N · A(i/N)` at a fixed
stage, `x` a parameter) with `g(N, x) ≤ N`; the scan is the bounded search for the first grid point with
`g(i) ≤ i`:

* `cross g`: the search body `(i + 1) ∸ g(i, x)`, nonzero exactly when `g(i, x) ≤ i`;
* `W g N x`: the first such grid point, a primitive recursive term;
* `crossing`: `W ≤ N` and `g(W) ≤ W` (the scan succeeds because `g(N) ≤ N`);
* `crossing_below`: `j < g(j)` at every earlier grid point (the one-dimensional Sperner cell `[W − 1, W]`
  carries both labels);
* `brouwer_interval`: if the samples at adjacent grid points satisfy `g(i) ≤ g(i + 1) + E` (the oscillation
  bound supplied by the modulus), then `W ≤ g(W) + E`;
* `approx_fixed_point`: together, `g(W) ≤ W ≤ g(W) + E`: the grid point `W/N` has residual at most `E/N`.
-/

namespace LeanProofs.IPRA.Topology.BrouwerInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_intro ex_elim ex_least)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (g : PTm 2)

/-- The search body `(i + 1) ∸ g(i, x)`: nonzero exactly when `g(i, x) ≤ i`. -/
def cross : PTm 2 := monus (succ (var 0)) g

theorem inst2_cross (i x : PTm n) : inst2 (cross g) i x = monus (succ i) (inst2 g i x) := by
  simp [inst2, cross]

/-- The first grid point `i ≤ N` with `g(i, x) ≤ i`. -/
abbrev W (N x : PTm n) : PTm n := wit (cross g) (succ N) x

/-- The scan succeeds: `W ≤ N` and `g(W) ≤ W`. -/
theorem crossing (N x : PTm n) (hN : Γ ⊢[PRAAx] le (inst2 g N x) N) :
    Γ ⊢[PRAAx] le (W g N x) N ⋏ le (inst2 g (W g N x) x) (W g N x) := by
  have hf : Γ ⊢[PRAAx] neg (inst2 (cross g) N x ≐ zero) := by
    rw [inst2_cross]
    refine .impI ?_
    have h : ((monus (succ N) (inst2 g N x) ≐ zero) :: Γ) ⊢[PRAAx] le (succ N) (inst2 g N x) := Prf.hyp0
    exact not_succ_le_self N _ (le_trans h hN.wk)
  have hex := ex_intro (cross g) hf (le_refl (succ N))
  have w := ex_elim (cross g) hex
  have a₁ : Γ ⊢[PRAAx] le (succ (W g N x)) (succ N) := Prf.andE₁ w
  have a₂ := Prf.andE₂ w
  rw [inst2_cross] at a₂
  refine .andI ?_ ?_
  · ipra_le sl a₁
  · refine .orE (lt_or_le (W g N x) (inst2 g (W g N x) x)) ?_ Prf.hyp0
    exact .botE _ (.impE a₂.wk Prf.hyp0)

/-- Before the crossing the samples lie above the diagonal: `j < g(j)` for `j < W`. -/
theorem crossing_below {N x j : PTm n} (hj : Γ ⊢[PRAAx] lt j (W g N x)) :
    Γ ⊢[PRAAx] lt j (inst2 g j x) := by
  have z := ex_least (cross g) hj
  rw [inst2_cross] at z
  exact z

/-- With the oscillation bound `g(i) ≤ g(i + 1) + E` on every cell, `W ≤ g(W) + E`. -/
theorem brouwer_interval (N x E : PTm n) (hN : Γ ⊢[PRAAx] le (inst2 g N x) N)
    (hosc : ∀ i : PTm n, Γ ⊢[PRAAx] lt i N ⟶ le (inst2 g i x) (inst2 g (succ i) x + E)) :
    Γ ⊢[PRAAx] le (W g N x) (inst2 g (W g N x) x + E) := by
  have hWN := Prf.andE₁ (crossing g N x hN)
  refine .orE (lt_or_le zero (W g N x)) ?_ ?_
  · have hW : (lt zero (W g N x) :: Γ) ⊢[PRAAx] le (succ zero) (W g N x) := Prf.hyp0
    have e := natEq (eq_add_of_le hW)
    have hjW : (lt zero (W g N x) :: Γ) ⊢[PRAAx] lt (monus (W g N x) (succ zero)) (W g N x) := by
      show (lt zero (W g N x) :: Γ) ⊢[PRAAx] le (succ (monus (W g N x) (succ zero))) (W g N x)
      ipra_le 0 with e
    have hgj : (lt zero (W g N x) :: Γ) ⊢[PRAAx]
        le (succ (monus (W g N x) (succ zero))) (inst2 g (monus (W g N x) (succ zero)) x) :=
      crossing_below g hjW
    have hjN : (lt zero (W g N x) :: Γ) ⊢[PRAAx] lt (monus (W g N x) (succ zero)) N := by
      show (lt zero (W g N x) :: Γ) ⊢[PRAAx] le (succ (monus (W g N x) (succ zero))) N
      have h' := hWN.wk (ψ := lt zero (W g N x))
      ipra_le sl h' with e
    have ho := Prf.impE (hosc (monus (W g N x) (succ zero))).wk hjN
    have ec : (lt zero (W g N x) :: Γ) ⊢[PRAAx] succ (monus (W g N x) (succ zero)) ≐ W g N x := by
      ipra_lc -e
    have eg := natEq (congrInst2 g ec (.eqRefl x))
    ipra_le sl ho + sl hgj with eg + e
  · have h0 : (le (W g N x) zero :: Γ) ⊢[PRAAx] le (W g N x) zero := Prf.hyp0
    ipra_le sl h0 + 𝔟 (inst2 g (W g N x) x) + 𝔟 E

/-- The approximate fixed point: the grid point `W ≤ N` satisfies `g(W) ≤ W ≤ g(W) + E`. -/
theorem approx_fixed_point (N x E : PTm n) (hN : Γ ⊢[PRAAx] le (inst2 g N x) N)
    (hosc : ∀ i : PTm n, Γ ⊢[PRAAx] lt i N ⟶ le (inst2 g i x) (inst2 g (succ i) x + E)) :
    Γ ⊢[PRAAx] (le (W g N x) N ⋏ le (inst2 g (W g N x) x) (W g N x)) ⋏
      le (W g N x) (inst2 g (W g N x) x + E) :=
  .andI (crossing g N x hN) (brouwer_interval g N x E hN hosc)

end LeanProofs.IPRA.Topology.BrouwerInterval
