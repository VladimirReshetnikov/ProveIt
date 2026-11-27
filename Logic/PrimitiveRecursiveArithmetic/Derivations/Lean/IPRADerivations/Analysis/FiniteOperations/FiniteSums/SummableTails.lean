import IPRADerivations.Foundations.GapDecision

/-!
# Coherence from a summable adjacent-error bound

Packet `foundations/fiber_ipra_2026-11-16`, Section 7.2, the general
summable-tail theorem. A signed sequence is given by two fixed binary primitive
recursive symbols and an arbitrary runtime parameter. Its adjacent errors have a natural majorant `e(k)`.
Finite induction bounds every discrepancy by the corresponding finite sum.
A supplied primitive recursive tail certificate then bounds discrepancies
uniformly in the later endpoint.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.SummableTails

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri subst_zabs)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The signed sequence `p(k, x) - q(k, x)` at a runtime parameter. -/
def value (p q : PR 2) (k x : PTm n) : ZT n := ⟨ap2 p k x, ap2 q k x⟩

/-- The discrepancy from the starting index to the endpoint. -/
def difference (p q : PR 2) (N r x : PTm n) : ZT n :=
  value p q (N + r) x - value p q N x

/-- The discrepancy of one adjacent pair. -/
def adjacent (p q : PR 2) (k x : PTm n) : ZT n :=
  value p q (succ k) x - value p q k x

/-- Variables `0 = i`, `1 = N`, `2 = x`. -/
def tailBody (e : PR 2) : PTm 3 := ap2 e (var 1 + var 0) (var 2)

/-- The finite sum `∑_{i<r} e(N + i, x)`. -/
def intervalSum (e : PR 2) (N r x : PTm n) : PTm n :=
  ap3 (sum2F (tailBody e)) r N x

ipra_subst value [ZT.subst]

ipra_subst difference

ipra_subst adjacent

ipra_subst intervalSum

private theorem value_congr (p q : PR 2) (x : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (value p q a x) = ZT.toZ Γ (value p q b x) := by
  have hq := natEq (congrAp2 q h (.eqRefl x))
  simpa only [value, ZT.toZ] using congrArg₂ HSub.hSub (natEq (congrAp2 p h (.eqRefl x))) hq

private theorem difference_zero (p q : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] zabs (difference p q N zero x) ≐ zero := by
  have hN := value_congr p q x (add_zero (Γ := Γ) N)
  have hd : ZT.toZ Γ (difference p q N zero x) = ZT.toZ Γ (ZT.natLit 0) := by
    simp only [difference, ZT.toZ_sub, hN, ZT.toZ_natLit]
    ring
  refine (zabs_congr hd).eqTrans ?_
  exact (congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _)

theorem intervalSum_zero (e : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] intervalSum e N zero x ≐ zero := sum2_zero _ _ _

theorem intervalSum_succ (e : PR 2) (N r x : PTm n) :
    Γ ⊢[PRAAx] intervalSum e N (succ r) x ≐ intervalSum e N r x + ap2 e (N + r) x := by
  simpa [tailBody, intervalSum, inst3] using sum2_succ (Γ := Γ) (tailBody e) r N x

/-- The finite triangle estimate for one more adjacent pair. -/
theorem discrepancy_step (p q e : PR 2) (x : PTm n) {N r : PTm n}
    (ih : Γ ⊢[PRAAx] le (zabs (difference p q N r x)) (intervalSum e N r x))
    (motion : Γ ⊢[PRAAx] le (zabs (adjacent p q (N + r) x)) (ap2 e (N + r) x)) :
    Γ ⊢[PRAAx] le (zabs (difference p q N (succ r) x)) (intervalSum e N (succ r) x) := by
  have hN := value_congr p q x (add_succ (Γ := Γ) N r)
  have hd : ZT.toZ Γ (difference p q N (succ r) x) =
      ZT.toZ Γ (difference p q N r x) + ZT.toZ Γ (adjacent p q (N + r) x) := by
    simp only [difference, adjacent, ZT.toZ_sub, hN]
    ring
  exact le_trans (zabs_tri hd)
    (le_congr (.eqRefl _) (intervalSum_succ e N r x).eqSymm (add_le_add₂ ih motion))

/-- The adjacent discrepancy contract at the supplied runtime parameter. -/
def motion (p q e : PR 2) (x : PTm n) : Fm PTm n :=
  .all (le (zabs (adjacent p q (var 0) (Syn.shift x))) (ap2 e (var 0) (Syn.shift x)))

@[simp] theorem subst_motion {m : ℕ} (σ : Fin n → PTm m)
    (p q e : PR 2) (x : PTm n) :
    (motion p q e x).subst σ = motion p q e (Syn.subst σ x) := by
  simp only [motion, Fm.subst_all, subst_le, subst_zabs, subst_adjacent, subst_ap2,
    Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

@[simp] theorem shift_motion (p q e : PR 2) (x : PTm n) :
    Fm.shift (motion p q e x) = motion p q e (Syn.shift x) := subst_motion _ _ _ _ _

/-- Finite telescoping under the adjacent contract. Starting index and runtime
parameter remain arbitrary during the quantifier-free induction. -/
theorem discrepancy (p q e : PR 2) (N r x : PTm n) (h : Γ ⊢[PRAAx] motion p q e x) :
    Γ ⊢[PRAAx] le (zabs (difference p q N r x)) (intervalSum e N r x) := by
  have all : Γ ⊢[PRAAx] .all
      (le (zabs (difference p q (Syn.shift N) (var 0) (Syn.shift x)))
        (intervalSum e (Syn.shift N) (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_ <;>
      simp only [subst_le, subst_zabs, subst_difference, subst_intervalSum, Syn.subst_var,
        Syn.inst_zero, Syn.repl_zero, Syn.subst_inst_shift, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
    · exact le_congr (difference_zero p q N x).eqSymm
        (intervalSum_zero e N x).eqSymm (le_refl zero)
    · apply discrepancy_step p q e (Syn.shift x) Prf.hyp0
      have shifted : Γ.map Fm.shift ⊢[PRAAx] (motion p q e (Syn.shift x) : Fm PTm (n + 1)) := by
        simpa only [shift_motion] using h.shift
      have pair := Prf.allE (Syn.shift N + var 0) shifted
      simpa only [motion, subst_le, subst_zabs, subst_adjacent, subst_ap2,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using pair.wk
  ipra_simpa_inst [subst_le, subst_zabs, subst_difference, subst_intervalSum] using Prf.allE r all

/-- A finite-sum tail certificate, uniform in the starting index and length,
with the runtime parameter kept fixed beneath both binders. -/
def tail (e T : PR 2) (x : PTm n) : Fm PTm n :=
  .all (.all (le (intervalSum e (var 1) (var 0) (Syn.shift (Syn.shift x)))
    (ap2 T (var 1) (Syn.shift (Syn.shift x)))))

/-- Summable majorants give a uniform discrepancy bound at every endpoint. -/
theorem tail_bound (p q e T : PR 2) (N r x : PTm n)
    (hm : Γ ⊢[PRAAx] motion p q e x) (ht : Γ ⊢[PRAAx] tail e T x) :
    Γ ⊢[PRAAx] le (zabs (difference p q N r x)) (ap2 T N x) := by
  have hs := Prf.allE r (Prf.allE N ht)
  have hb : Γ ⊢[PRAAx] le (intervalSum e N r x) (ap2 T N x) := by
    simpa [tail, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using hs
  exact le_trans (discrepancy p q e N r x hm) hb

/-- The source form with ordered endpoints and canonical length `M ∸ N`. -/
theorem tail_between (p q e T : PR 2) (x : PTm n) {N M : PTm n}
    (hm : Γ ⊢[PRAAx] motion p q e x) (ht : Γ ⊢[PRAAx] tail e T x)
    (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (zabs (value p q M x - value p q N x)) (ap2 T N x) := by
  have endpoint := value_congr p q x (eq_add_of_le order)
  have same : ZT.toZ Γ (difference p q N (PTm.monus M N) x) =
      ZT.toZ Γ (value p q M x - value p q N x) := by
    simp only [difference, ZT.toZ_sub, ← endpoint]
  exact le_congr (zabs_congr same) (.eqRefl _) (tail_bound p q e T N _ x hm ht)

/-- Variables `0 = N`, `1 = r`, `2 = x`. -/
abbrev telescopingFormula (p q e : PR 2) : Fm PTm 3 :=
  motion p q e (var 2) ⟶ le (zabs (difference p q (var 0) (var 1) (var 2)))
    (intervalSum e (var 0) (var 1) (var 2))

theorem finite_telescoping (p q e : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (telescopingFormula p q e) :=
  closeUniv 3 (.impI (discrepancy p q e _ _ _ Prf.hyp0))

/-- The contracts remain explicit in the universally closed tail theorem. -/
abbrev tailFormula (p q e T : PR 2) : Fm PTm 3 :=
  motion p q e (var 2) ⟶ tail e T (var 2) ⟶
    le (zabs (difference p q (var 0) (var 1) (var 2))) (ap2 T (var 0) (var 2))

theorem summable_tail (p q e T : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (tailFormula p q e T) :=
  closeUniv 3 (.impI (.impI (tail_bound p q e T _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Variables `0 = N`, `1 = M`, `2 = x`. -/
abbrev endpointsFormula (p q e T : PR 2) : Fm PTm 3 :=
  motion p q e (var 2) ⟶ tail e T (var 2) ⟶ le (var 0) (var 1) ⟶
    le (zabs (value p q (var 1) (var 2) - value p q (var 0) (var 2)))
      (ap2 T (var 0) (var 2))

theorem summable_tail_endpoints (p q e T : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (endpointsFormula p q e T) :=
  closeUniv 3 (.impI (.impI (.impI
    (tail_between p q e T _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

#print axioms finite_telescoping
#print axioms summable_tail
#print axioms summable_tail_endpoints

end LeanProofs.IPRA.Analysis.SummableTails
