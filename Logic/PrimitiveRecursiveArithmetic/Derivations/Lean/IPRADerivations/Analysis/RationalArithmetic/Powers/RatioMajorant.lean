import IPRADerivations.Analysis.SpecialFunctions.Hypergeometric.HypergeometricTerm
import IPRADerivations.Core.OrderCertificates

/-!
# The coefficient recurrence of a hypergeometric term and the geometric tail of a ratio majorant

Packet: `analysis/meijer_g_ipra_2026-11-16`: the ratio recurrence `eq:hypergeom` (to which `thm:ode`
reduces in the series presentation), the ratio majorant `eq:ratio-majorant` and the geometric tail
`eq:geometric-tail` behind Theorem `thm:hyp-conv` ("Primitive-recursive convergence").

* `coefficient_recurrence`: for the cleared term `t_k = hn A w k / hd B k` of
  `Analysis/HypergeometricTerm` (one upper parameter `A`, one lower parameter `B`),
  `(k + 1)(B + k) · hn(k + 1) · hd(k) = (A + k) w · hn(k) · hd(k + 1)`, i.e.
  `(k + 1)(B + k) t_{k+1} = (A + k) w t_k`: the coefficient form of the differential equation.
* `ratio_tail` (`eq:geometric-tail`): for terms `t(k, x)` over a common denominator with ratio at most
  `ρ = p/(p + d)`, `(p + d) t(k + 1) ≤ p t(k)` for all `k`: for every `N`,
  `d ∑_{i<N} t(i) + (p + d) t(N) ≤ (p + d) t(0)`, i.e. `∑_{i<N} t(i) ≤ (t(0) − t(N)) / (1 − ρ)`. Applied to
  the terms from the index found by the search of `thm:hyp-conv`, this is the truncation modulus.
* `half_tail`: the case `ρ = 1/2` of `thm:hyp-conv` (a): `∑_{i<N} t(i) + 2 t(N) ≤ 2 t(0)`.

The search for the threshold index, the polynomial ratio inequality itself and the analytic statements of
the packet are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RatioMajorant

open_ipra
open LeanProofs.IPRA.Analysis.HypergeometricTerm (hn hd hn_succ hd_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(k + 1)(B + k) t_{k+1} = (A + k) w t_k`, cleared of the denominators of `t_k = hn/hd`. -/
theorem coefficient_recurrence (A B w k : PTm n) :
    Γ ⊢[PRAAx] succ k * (B + k) * (hn A w (succ k) * hd B k) ≐
      (A + k) * w * (hn A w k * hd B (succ k)) := by
  have en := natEq (hn_succ (Γ := Γ) A w k)
  have ed := natEq (hd_succ (Γ := Γ) B k)
  apply deriveNat; ipra_simps
  rw [en, ed]; ring

/-! ## The geometric tail -/

section Tail

variable {t : PTm 2} {x p d : PTm n}

theorem tail_base :
    Γ ⊢[PRAAx] le (d * ap2 (sumF t) zero x + (p + d) * inst2 t zero x) ((p + d) * inst2 t zero x) := by
  have z := natEq (sum_zero (Γ := Γ) t x)
  ipra_le 0 using rw [z]; ring

theorem tail_step {k : PTm n}
    (hr : Γ ⊢[PRAAx] le ((p + d) * inst2 t (succ k) x) (p * inst2 t k x))
    (ih : Γ ⊢[PRAAx] le (d * ap2 (sumF t) k x + (p + d) * inst2 t k x) ((p + d) * inst2 t zero x)) :
    Γ ⊢[PRAAx] le (d * ap2 (sumF t) (succ k) x + (p + d) * inst2 t (succ k) x)
      ((p + d) * inst2 t zero x) := by
  have es := natEq (sum_succ' (Γ := Γ) t k x)
  ipra_le sl ih + sl hr using rw [es]; ring

theorem tail_all
    (hr : Γ ⊢[PRAAx] Fm.all (le ((Syn.shift p + Syn.shift d) * inst2 t (succ (var 0)) (Syn.shift x))
      (Syn.shift p * inst2 t (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (Syn.shift d * ap2 (sumF t) (var 0) (Syn.shift x) +
        (Syn.shift p + Syn.shift d) * inst2 t (var 0) (Syn.shift x))
      ((Syn.shift p + Syn.shift d) * inst2 t zero (Syn.shift x))) := by
  ipra_qfind (le_QF _ _) [subst_le, subst_ap2, subst_inst2]
  · exact tail_base
  · exact tail_step hr.allOpen.wk Prf.hyp0

/-- `eq:geometric-tail`: with ratio at most `p/(p + d)`,
`d ∑_{i<N} t(i) + (p + d) t(N) ≤ (p + d) t(0)` for every `N`. -/
theorem ratio_tail
    (hr : Γ ⊢[PRAAx] Fm.all (le ((Syn.shift p + Syn.shift d) * inst2 t (succ (var 0)) (Syn.shift x))
      (Syn.shift p * inst2 t (var 0) (Syn.shift x))))
    (N : PTm n) :
    Γ ⊢[PRAAx] le (d * ap2 (sumF t) N x + (p + d) * inst2 t N x) ((p + d) * inst2 t zero x) := by
  have a := Prf.allE N (tail_all hr)
  simp only [subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

end Tail

/-- The case `ρ = 1/2`: if `2 t(k + 1) ≤ t(k)` for all `k`, then `∑_{i<N} t(i) + 2 t(N) ≤ 2 t(0)`. -/
theorem half_tail {t : PTm 2} {x : PTm n}
    (hr : Γ ⊢[PRAAx] Fm.all (le ((succ zero + succ zero) * inst2 t (succ (var 0)) (Syn.shift x))
      (succ zero * inst2 t (var 0) (Syn.shift x))))
    (N : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF t) N x + (inst2 t N x + inst2 t N x)) (inst2 t zero x + inst2 t zero x) := by
  have h := ratio_tail (p := succ zero) (d := succ zero) (t := t) (x := x)
    (by simpa [Syn.shift] using hr) N
  ipra_le sl h

end LeanProofs.IPRA.Analysis.RatioMajorant
