import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Pairing

/-!
# Regular names from a motion budget

Packet: `foundations/ipra_pfig_framework_2026-11-15`, `paper/sections/08_shrinking_names.tex`: Theorem
`thm:adjacent-coherence` supplies `d(x_p, x_{p+1}) ≤ δ_p + ε_p`, and Theorem `thm:regular-name` ("Regular name
from a motion budget") concludes that if the tail sums satisfy `∑_{j=p}^{q−1} (δ_j + ε_j) ≤ 2^{-p}` for all
`q ≥ p`, then `(x_p)_p` is a regular Cauchy name, i.e. `d(x_p, x_q) ≤ 2^{-p}`.

With the base index `p` folded into the parameter `x`: `D(k)` is the distance between the terms of index `p`
and `p + k`, and `s(k)` is the motion bound of the step from `p + k` to `p + k + 1`. The triangle inequality
enters as `D(k + 1) ≤ D(k) + s(k)`.

* `telescope`: if `D(0) = 0` and `D(k + 1) ≤ D(k) + s(k)` for all `k`, then `D(k) ≤ ∑_{i<k} s(i)` for every
  `k`;
* `regular_of_budget` (`thm:regular-name`): if moreover `∑_{i<k} s(i) ≤ B`, then `D(k) ≤ B`.

The geometric special case `s(k) ≤ C/2^k` is `OdeRefinement.geometric_cauchy`.

The same telescoping proves Theorem `thm:shrinking` ("Shrinking-cloud name extraction") of
`ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`, `ipra_kifcr_framework_2026-11-16` and
`ipra_kifcs_framework_2026-11-16`, whose step bound is the three-term estimate
`d(a_q, a_{q+1}) ≤ d(a_q, u) + d(u, v) + d(v, a_{q+1}) ≤ δ_q + μ_q + δ_{q+1}` for one valid edge `(u, v)`
between consecutive clouds:

* `three_term`: the arithmetic of that estimate;
* `adjacent_of_edge`: if there is a pair `w = ⟨u, v⟩` satisfying the triangle inequality and the three
  bounds (diameter of the cloud of `a`, edge length, diameter of the next cloud), then
  `d(a, a') ≤ δ + μ + δ'`. The edge is eliminated in the object theory: it is used only existentially, and
  the output keeps choosing its own representatives.

With `s(k) = δ + μ + δ'` at level `p + k` and the tail certificate as budget, `regular_of_budget` gives the
regular name `r_k = a_{T(k)}`. The construction of the clouds from shrinking viability and the bound of
PFIG `thm:adjacent-coherence` are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TelescopingNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Telescope

variable {D s : PTm 2} {x : PTm n}

theorem tel_base (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero) :
    Γ ⊢[PRAAx] le (inst2 D zero x) (ap2 (sumF s) zero x) := by
  have z := natEq h0; have z' := natEq (sum_zero (Γ := Γ) s x)
  ipra_le 0 using rw [z, z']; ring

theorem tel_step {k : PTm n} (hstep : Γ ⊢[PRAAx] le (inst2 D (succ k) x) (inst2 D k x + inst2 s k x))
    (ih : Γ ⊢[PRAAx] le (inst2 D k x) (ap2 (sumF s) k x)) :
    Γ ⊢[PRAAx] le (inst2 D (succ k) x) (ap2 (sumF s) (succ k) x) := by
  have es := natEq (sum_succ' (Γ := Γ) s k x)
  ipra_le sl hstep + sl ih using rw [es]; ring

theorem tel_all (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero)
    (hstep : Γ ⊢[PRAAx] Fm.all (le (inst2 D (succ (var 0)) (Syn.shift x))
      (inst2 D (var 0) (Syn.shift x) + inst2 s (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (inst2 D (var 0) (Syn.shift x)) (ap2 (sumF s) (var 0) (Syn.shift x))) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tel_base h0
  · simp only [subst_le, subst_ap2, subst_inst2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tel_step hstep.allOpen.wk Prf.hyp0

/-- The triangle inequality telescopes: `D(k) ≤ ∑_{i<k} s(i)`. -/
theorem telescope (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero)
    (hstep : Γ ⊢[PRAAx] Fm.all (le (inst2 D (succ (var 0)) (Syn.shift x))
      (inst2 D (var 0) (Syn.shift x) + inst2 s (var 0) (Syn.shift x))))
    (k : PTm n) : Γ ⊢[PRAAx] le (inst2 D k x) (ap2 (sumF s) k x) := by
  have a := Prf.allE k (tel_all h0 hstep)
  simp only [subst_le, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

/-- `thm:regular-name`: a motion budget `∑_{i<k} s(i) ≤ B` bounds the distance, `D(k) ≤ B`. -/
theorem regular_of_budget (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero)
    (hstep : Γ ⊢[PRAAx] Fm.all (le (inst2 D (succ (var 0)) (Syn.shift x))
      (inst2 D (var 0) (Syn.shift x) + inst2 s (var 0) (Syn.shift x))))
    {k B : PTm n} (hb : Γ ⊢[PRAAx] le (ap2 (sumF s) k x) B) : Γ ⊢[PRAAx] le (inst2 D k x) B :=
  le_trans (telescope h0 hstep k) hb

end Telescope

/-! ## The step bound from an edge between consecutive clouds -/

/-- `D ≤ d₁ + d₂ + d₃` with `d₁ ≤ δ`, `d₂ ≤ μ`, `d₃ ≤ δ'` gives `D ≤ δ + μ + δ'`. -/
theorem three_term {D d₁ d₂ d₃ δ μ δ' : PTm n} (ht : Γ ⊢[PRAAx] le D (d₁ + d₂ + d₃))
    (h₁ : Γ ⊢[PRAAx] le d₁ δ) (h₂ : Γ ⊢[PRAAx] le d₂ μ) (h₃ : Γ ⊢[PRAAx] le d₃ δ') :
    Γ ⊢[PRAAx] le D (δ + μ + δ') := by
  ipra_le sl ht + sl h₁ + sl h₂ + sl h₃

/-- The pair `w = ⟨u, v⟩` (variable `0`) is an edge witnessing the three-term estimate for `D = d(a, a')`. -/
abbrev EdgeAt (dist : PTm 2) (a a' D δ μ δ' : PTm n) : Fm PTm (n + 1) :=
  le (Syn.shift D)
      (inst2 dist (Syn.shift a) (fstT (var 0)) + inst2 dist (fstT (var 0)) (sndT (var 0)) +
        inst2 dist (sndT (var 0)) (Syn.shift a')) ⋏
    (le (inst2 dist (Syn.shift a) (fstT (var 0))) (Syn.shift δ) ⋏
      (le (inst2 dist (fstT (var 0)) (sndT (var 0))) (Syn.shift μ) ⋏
        le (inst2 dist (sndT (var 0)) (Syn.shift a')) (Syn.shift δ')))

/-- An edge between consecutive clouds, given existentially, bounds the distance of the representatives. -/
theorem adjacent_of_edge {dist : PTm 2} {a a' D δ μ δ' : PTm n}
    (he : Γ ⊢[PRAAx] Fm.ex (EdgeAt dist a a' D δ μ δ')) : Γ ⊢[PRAAx] le D (δ + μ + δ') := by
  refine .exE he ?_
  have w : (EdgeAt dist a a' D δ μ δ' :: Γ.map Fm.shift) ⊢[PRAAx] EdgeAt dist a a' D δ μ δ' := Prf.hyp0
  have r := three_term (Prf.andE₁ w) (Prf.andE₁ (Prf.andE₂ w)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ w)))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ w)))
  simp only [Fm.shift, subst_le, PTm.subst_add]
  exact r

end LeanProofs.IPRA.Foundations.TelescopingNames
