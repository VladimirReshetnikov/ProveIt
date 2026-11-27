import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Header

/-!
# The local defect of an Euler polygon by midpoint telescoping

Packet: `foundations/ipra_local_global`, `paper/04_ode.tex`, Theorem `thm:ode-existence` ("Constructed
controlled flow"), the estimate `eq:ode-localdefect`:
`‖U_n(r) − U_n(q) − (r − q) F(U_n(q))‖ ≤ LM (v²/2 + h v)`, `v = |r − q|`. "Split the interval between `q`
and `r` at its finitely many mesh points. On each resulting subinterval the slope difference is constant.
Evaluate the affine upper bound at that subinterval's rational midpoint and multiply by its length ... the
midpoint-times-length sum of `s − q` is exactly `(r − q)²/2`, by the difference-of-squares identity on each
subinterval."

The subdivision points are `q + u(i)` with `u` nondecreasing (cleared numerators, `u(0)` the start); the
error on cell `i` is `e(i)`, and the affine bound `A + B (s − q)` (`A = LM h`, `B = LM`) evaluated at the
midpoint times the length gives the cell hypothesis, cleared by `2`:

  `2 e(i) ≤ 2A (u(i+1) − u(i)) + B (u(i+1) + u(i)) (u(i+1) − u(i))`.

* `DInv`, `defect_step`, `defect_sum`: for `k ≤ K`,
  `2 ∑_{i<k} e(i) + 2A u(0) + B u(0)² ≤ 2A u(k) + B u(k)²`: the lengths telescope to `u(k) − u(0)` and the
  midpoint sums to `u(k)² − u(0)²` (difference of squares), by quantifier-free induction on the cells;
* `local_defect` (`eq:ode-localdefect`): with `u(0) = 0` and `u(K) = v`, `2 ∑ e ≤ 2A v + B v²`, i.e.
  `∑ e ≤ LM (h v + v²/2)`.

The polygon slopes, the polynomial bound `lem:ode-polybound` behind the affine estimate and the choice of
`n = p + c` are not derived here.
-/

namespace LeanProofs.IPRA.Foundations.OdeLocalDefect

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The invariant `2 ∑_{i<k} e(i) + 2A u(0) + B u(0)² ≤ 2A u(k) + B u(k)²`. -/
abbrev DInv (u e : PTm 2) (x A B k : PTm n) : Fm PTm n :=
  le (two * ap2 (sumF e) k x + two * A * inst2 u zero x + B * (inst2 u zero x * inst2 u zero x))
    (two * A * inst2 u k x + B * (inst2 u k x * inst2 u k x))

/-- The cell hypothesis at `k`. -/
abbrev Cell (u e : PTm 2) (x A B k : PTm n) : Fm PTm n :=
  le (two * inst2 e k x)
    (two * A * monus (inst2 u (succ k) x) (inst2 u k x) +
      B * ((inst2 u (succ k) x + inst2 u k x) * monus (inst2 u (succ k) x) (inst2 u k x)))

theorem defect_step {u e : PTm 2} {x A B k : PTm n}
    (hm : Γ ⊢[PRAAx] le (inst2 u k x) (inst2 u (succ k) x)) (hc : Γ ⊢[PRAAx] Cell u e x A B k)
    (ih : Γ ⊢[PRAAx] DInv u e x A B k) : Γ ⊢[PRAAx] DInv u e x A B (succ k) := by
  have es := natEq (sum_succ' (Γ := Γ) e k x)
  have ed := natEq (eq_add_of_le hm)
  ipra_le sl ih + sl hc using
    rw [es]
    linear_combination (2 * 𝔟 A + 𝔟 B * (𝔟 (inst2 u (succ k) x) + 𝔟 (inst2 u k x))) * ed

/-- `2 ∑_{i<K} e(i) + 2A u(0) + B u(0)² ≤ 2A u(K) + B u(K)²` for a nondecreasing subdivision. -/
theorem defect_sum (u e : PTm 2) {x A B K : PTm n}
    (hm : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift K) ⟶
      le (inst2 u (Syn.var 0) (Syn.shift x)) (inst2 u (succ (Syn.var 0)) (Syn.shift x))))
    (hc : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift K) ⟶
      Cell u e (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.var 0))) :
    Γ ⊢[PRAAx] DInv u e x A B K := by
  let P := DInv u e (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.var 0)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst K) := by
    refine qfIndUpTo K (le_QF _ _) ?_ ?_
    · simp only [P, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      have z := natEq (sum_zero (Γ := Γ) e x)
      ipra_le 0 using rw [z]; ring
    · simp only [P, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
        PTm.subst_monus, Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      exact .impI (defect_step (.impE hm.allOpen.wk.wk Prf.hyp0)
        (.impE hc.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P] using atBound

/-- `eq:ode-localdefect`: from the start `u(0) = 0` to `u(K) = v`, `2 ∑ e ≤ 2A v + B v²`. -/
theorem local_defect (u e : PTm 2) {x A B K v : PTm n}
    (hm : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift K) ⟶
      le (inst2 u (Syn.var 0) (Syn.shift x)) (inst2 u (succ (Syn.var 0)) (Syn.shift x))))
    (hc : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift K) ⟶
      Cell u e (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.var 0)))
    (h0 : Γ ⊢[PRAAx] inst2 u zero x ≐ zero) (hv : Γ ⊢[PRAAx] inst2 u K x ≐ v) :
    Γ ⊢[PRAAx] le (two * ap2 (sumF e) K x) (two * A * v + B * (v * v)) := by
  have d := defect_sum u e hm hc
  have e0 := natEq h0
  have ev := natEq hv
  ipra_le sl d using
    rw [e0, ev]; ring

end LeanProofs.IPRA.Foundations.OdeLocalDefect
