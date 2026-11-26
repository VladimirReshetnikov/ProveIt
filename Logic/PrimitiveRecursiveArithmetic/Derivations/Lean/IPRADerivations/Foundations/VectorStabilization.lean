import IPRADerivations.Foundations.VectorRank
import IPRADerivations.Foundations.FiniteStabilization
import IPRADerivations.Core.Header

/-!
# Finite stabilization for vector-valued states

The vector form of the finite stabilization theorem
(`FINER-iPRA-framework-2026-11-16`, `thm:demand-stabilization`; `darc_ipra_framework_2026-11-16`,
`thm:demand-stabilization`; `ipra_kifcr_framework_2026-11-16` and `ipra_kifcs_framework_2026-11-16`,
`thm:capped-closure`, the fixed-point clause; `scope_ipra_framework_2026-11-16_2`, "Capped demand
stabilization", the prefixed-point clause).

A state `s` is one number coding a vector of length `m(s)`; `cmp(i, s)` is its `i`-th coordinate and
`rk(s) = ∑_{i<m(s)} cmp(i, s)` its rank. The update is a unary term `f`. The new coordinates are the body
`cF(i, s) = cmp(i, f(s))`. Three rules describe the situation (at arbitrary terms and contexts):

* `hm`: the length is preserved, `m(f(s)) = m(s)`;
* `hinfl` (inflation): `cmp(i, s) ≤ cmp(i, f(s))` for `i < m(s)`;
* `hext` (extensionality of the coding): if `cmp(i, s) = cmp(i, f(s))` for all `i < m(s)`, then `f(s) = s`.

Then:

* `vector_step`: `f(s) = s ∨ rk(s) < rk(f(s))`, from `VectorRank.rank_dichotomy`;
* `vector_stab`: for every `t`, `x^{t+1} = x^t` or `t + 1 ≤ rk(x^{t+1})`;
* `vector_stable`: if `rk(x^{H+1}) ≤ H` (for instance `H` the sum of the capacities), then `x^{H+1} = x^H`
  and `f(x^H) = x^H`.

No particular coding of vectors is fixed; the three rules are what a coding has to provide.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.VectorStabilization

open_ipra
open LeanProofs.IPRA.Foundations.IterationFusion (app1 subst_app1 iter iter_succ)
open LeanProofs.IPRA.Foundations.FiniteStabilization (Stab stab stable_at)
open LeanProofs.IPRA.Foundations.VectorRank (rank_dichotomy)

/-- The new coordinates: `cF(i, s) = cmp(i, f(s))`. -/
def cF (f : PTm 1) (cmp : PTm 2) : PTm 2 := Syn.subst ![var 0, app1 f (var 1)] cmp

theorem inst2_cF (f : PTm 1) (cmp : PTm 2) {k : ℕ} (i s : PTm k) :
    inst2 (cF f cmp) i s = inst2 cmp i (app1 f s) := by
  simp only [cF, inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- The rank `rk(s) = ∑_{i<m(s)} cmp(i, s)` as a unary term. -/
def rk (cmp : PTm 2) (mB : PTm 1) : PTm 1 := ap2 (sumF cmp) mB (var 0)

theorem app1_rk (cmp : PTm 2) (mB : PTm 1) {k : ℕ} (s : PTm k) :
    app1 (rk cmp mB) s = ap2 (sumF cmp) (app1 mB s) s := by
  simp [app1, rk]

theorem shift_app1 (f : PTm 1) {k : ℕ} (s : PTm k) : Syn.shift (app1 f s) = app1 f (Syn.shift s) := by
  simp [Syn.shift]

section Vector

variable {f mB : PTm 1} {cmp : PTm 2}

/-- The step hypothesis of finite stabilization for vector states. -/
theorem vector_step
    (hm : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k), Θ ⊢[PRAAx] app1 mB (app1 f s) ≐ app1 mB s)
    (hinfl : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k), Θ ⊢[PRAAx]
      Fm.all (lt (var 0) (Syn.shift (app1 mB s)) ⟶
        le (inst2 cmp (var 0) (Syn.shift s)) (inst2 (cF f cmp) (var 0) (Syn.shift s))))
    (hext : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k),
      (Θ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (app1 mB s)) ⟶
        (inst2 cmp (var 0) (Syn.shift s) ≐ inst2 (cF f cmp) (var 0) (Syn.shift s)))) →
      (Θ ⊢[PRAAx] app1 f s ≐ s))
    {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k) :
    Γ ⊢[PRAAx] (app1 f s ≐ s) ⋎ lt (app1 (rk cmp mB) s) (app1 (rk cmp mB) (app1 f s)) := by
  refine .orE (rank_dichotomy (a := cmp) (b := cF f cmp) (m := app1 mB s) (x := s) (hinfl s)) ?_ ?_
  · exact .orI₁ (hext s Prf.hyp0)
  · refine .orI₂ ?_
    rw [app1_rk, app1_rk]
    have hc := sum_congr_bounded
      (Γ := lt (ap2 (sumF cmp) (app1 mB s) s) (ap2 (sumF (cF f cmp)) (app1 mB s) s) :: Γ)
      (cF f cmp) cmp s (app1 f s) (app1 mB s) (.allI (.impI (by
        rw [inst2_cF, shift_app1 f s]
        exact Prf.eqRefl (inst2 cmp (var 0) (app1 f (Syn.shift s))))))
    exact lt_congr (.eqRefl _) (hc.eqTrans (congrAp2 (sumF cmp) (hm s).eqSymm (.eqRefl _))) Prf.hyp0

/-- For every `t`: stalled, or the rank is at least the clock. -/
theorem vector_stab
    (hm : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k), Θ ⊢[PRAAx] app1 mB (app1 f s) ≐ app1 mB s)
    (hinfl : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k), Θ ⊢[PRAAx]
      Fm.all (lt (var 0) (Syn.shift (app1 mB s)) ⟶
        le (inst2 cmp (var 0) (Syn.shift s)) (inst2 (cF f cmp) (var 0) (Syn.shift s))))
    (hext : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k),
      (Θ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (app1 mB s)) ⟶
        (inst2 cmp (var 0) (Syn.shift s) ≐ inst2 (cF f cmp) (var 0) (Syn.shift s)))) →
      (Θ ⊢[PRAAx] app1 f s ≐ s))
    {k : ℕ} {Γ : List (Fm PTm k)} (t x : PTm k) : Γ ⊢[PRAAx] Stab f (rk cmp mB) t x :=
  stab (fun s => vector_step hm hinfl hext s) t x

/-- `thm:demand-stabilization` for vectors: a rank bound at time `H + 1` gives `x^{H+1} = x^H` and
`f(x^H) = x^H`. -/
theorem vector_stable
    (hm : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k), Θ ⊢[PRAAx] app1 mB (app1 f s) ≐ app1 mB s)
    (hinfl : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k), Θ ⊢[PRAAx]
      Fm.all (lt (var 0) (Syn.shift (app1 mB s)) ⟶
        le (inst2 cmp (var 0) (Syn.shift s)) (inst2 (cF f cmp) (var 0) (Syn.shift s))))
    (hext : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (s : PTm k),
      (Θ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (app1 mB s)) ⟶
        (inst2 cmp (var 0) (Syn.shift s) ≐ inst2 (cF f cmp) (var 0) (Syn.shift s)))) →
      (Θ ⊢[PRAAx] app1 f s ≐ s))
    {k : ℕ} {Γ : List (Fm PTm k)} {x H : PTm k}
    (hbound : Γ ⊢[PRAAx] le (app1 (rk cmp mB) (iter f (succ H) x)) H) :
    Γ ⊢[PRAAx] (iter f (succ H) x ≐ iter f H x) ⋏ (app1 f (iter f H x) ≐ iter f H x) := by
  have st := stable_at (fun s => vector_step hm hinfl hext s) hbound
  exact .andI st ((iter_succ f H x).eqSymm.eqTrans st)

end Vector

end LeanProofs.IPRA.Foundations.VectorStabilization
