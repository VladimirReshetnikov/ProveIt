import IPRADerivations.Analysis.Optimization.WeightedAMGM
import IPRADerivations.AnalyticNumberTheory.PhiLower

/-!
# Products of pointwise inequalities and the log-convexity of the Euler approximants

Packet: `analysis/bohr_mollerup_ipra_2026-11-15`, Lemma "each Euler approximant is rationally
log-convex": for `z = ((s − j) x + j y)/s`, `E_n(z)^s ≤ E_n(x)^{s−j} E_n(y)^j`, proved by "for every
`h = 0, …, n`, weighted AM–GM gives `(z + h)^s ≥ (x + h)^{s−j} (y + h)^j`. Multiplying these finitely many
inequalities makes the denominator on the left at least the corresponding denominator on the right".

* `prod_mono`: for natural bodies `f ≤ g` below `N`, `∏_{i<N} f ≤ ∏_{i<N} g` (a reusable lemma; guarded
  quantifier-free induction with `le_mul_mono`);
* `amB`, `amR`: the two sides of the weighted AM–GM inequality of `Analysis/WeightedAMGM` as bodies in
  the index `h`, `s^s u_h^{a} v_h^{b}` and `(a u_h + b v_h)^s` with `a = a₀ + 1`, `s = a + b`;
* `euler_log_convex`: `∏_{h<N} s^s u_h^{a} v_h^{b} ≤ ∏_{h<N} (a u_h + b v_h)^s`. With `u_h = x + h`,
  `v_h = y + h` (numerators over a common denominator) and `a u_h + b v_h = s (z + h)` this is the
  denominator comparison `∏ (x + h)^{s−j} (y + h)^j ≤ ∏ (z + h)^s` of the lemma, cleared of `s^{sN}`.

The numerator factors `n! n^x` (real powers) and the quotient are the reading of the lemma; they are
not formalized. The finite AM–GM lemma of the packet is `Foundations/FiniteAMGM` and the two-point
weighted corollary is `amgm` of `Analysis/WeightedAMGM`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.EulerLogConvex

open_ipra
open LeanProofs.IPRA.Analysis.WeightedAMGM (amgm)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Pointwise smaller natural bodies have smaller products. -/
theorem prod_mono (f g : PTm 2) (x N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (prodF f) N x) (ap2 (prodF g) N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (ap2 (prodF f) (var 0) (Syn.shift x)) (ap2 (prodF g) (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · have e : (le (var 0) (Syn.shift N) ⟶
            le (ap2 (prodF f) (var 0) (Syn.shift x)) (ap2 (prodF g) (var 0) (Syn.shift x))).subst
            (Syn.inst zero) = (le zero N ⟶ le (ap2 (prodF f) zero x) (ap2 (prodF g) zero x)) := by
        simp
      rw [e]
      exact .impI (le_congr (prod_zero f x).eqSymm (prod_zero g x).eqSymm (le_refl _))
    · have e : (le (var 0) (Syn.shift N) ⟶
            le (ap2 (prodF f) (var 0) (Syn.shift x)) (ap2 (prodF g) (var 0) (Syn.shift x))).subst
            (Syn.repl (succ (var 0))) =
          (le (succ (var 0)) (Syn.shift N) ⟶
            le (ap2 (prodF f) (succ (var 0)) (Syn.shift x)) (ap2 (prodF g) (succ (var 0)) (Syn.shift x))) := by
        simp
      rw [e]
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            le (ap2 (prodF f) (var 0) (Syn.shift x)) (ap2 (prodF g) (var 0) (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      have h₁ := Prf.impE Prf.hyp1 hle
      have h₂ : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            le (ap2 (prodF f) (var 0) (Syn.shift x)) (ap2 (prodF g) (var 0) (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x)) :=
        Prf.impE h.allOpen.wk.wk Prf.hyp0
      exact le_congr (prod_succ f _ _).eqSymm (prod_succ g _ _).eqSymm (le_mul_mono h₁ h₂)
  have a := Prf.allE N hall
  have e : (le (var 0) (Syn.shift N) ⟶
        le (ap2 (prodF f) (var 0) (Syn.shift x)) (ap2 (prodF g) (var 0) (Syn.shift x))).subst
        (Syn.inst N) = (le N N ⟶ le (ap2 (prodF f) N x) (ap2 (prodF g) N x)) := by
    simp
  rw [e] at a
  exact Prf.impE a (le_refl N)

section LogConvex

variable (a₀ b u v : PTm 2)

/-- `s^s u^{a} v^{b}` with `a = a₀ + 1`, `s = a + b`. -/
def amB : PTm 2 := pw (succ (a₀ + b)) (succ (a₀ + b)) * (pw u (succ a₀) * pw v b)
/-- `(a u + b v)^s`. -/
def amR : PTm 2 := pw (succ a₀ * u + b * v) (succ (a₀ + b))

theorem inst2_amB (i x : PTm n) :
    inst2 (amB a₀ b u v) i x =
      pw (succ (inst2 a₀ i x + inst2 b i x)) (succ (inst2 a₀ i x + inst2 b i x)) *
        (pw (inst2 u i x) (succ (inst2 a₀ i x)) * pw (inst2 v i x) (inst2 b i x)) := by
  simp [inst2, amB]

theorem inst2_amR (i x : PTm n) :
    inst2 (amR a₀ b u v) i x =
      pw (succ (inst2 a₀ i x) * inst2 u i x + inst2 b i x * inst2 v i x)
        (succ (inst2 a₀ i x + inst2 b i x)) := by
  simp [inst2, amR]

/-- The Euler approximants: `∏_{h<N} s^s u_h^{a} v_h^{b} ≤ ∏_{h<N} (a u_h + b v_h)^s`. -/
theorem euler_log_convex (N x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (prodF (amB a₀ b u v)) N x) (ap2 (prodF (amR a₀ b u v)) N x) := by
  refine prod_mono _ _ x N (.allI (.impI ?_))
  rw [inst2_amB, inst2_amR]
  exact amgm _ _ _ _

end LogConvex

end LeanProofs.IPRA.Analysis.EulerLogConvex
