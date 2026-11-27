import IPRADerivations.Foundations.GapDecision

/-!
# Coherence of dyadic names from adjacent motion

Packet `foundations/fiber_ipra_2026-11-16`, Theorem `thm:dyadic`.
A signed sequence has two fixed binary primitive recursive symbols for its
parts, with the precision index and one runtime parameter as arguments.
If `|2 a(k) - a(k+1)| ≤ 1`, its scaled discrepancy after `r` steps is
strictly smaller than `2^r`. The sharper integer statement is
`|2^r a(N,x) - a(N+r,x)| + 1 ≤ 2^r`. The following packet corollary,
"Independent certificates become coherent", is proved from a local
existence contract and an adjacent-pair certificate soundness contract.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.DyadicCauchy

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri subst_zabs)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A fixed primitive recursive signed sequence. -/
def value (p q : PR 2) (k x : PTm n) : ZT n := ⟨ap2 p k x, ap2 q k x⟩

/-- The signed discrepancy after clearing the dyadic denominators. -/
def difference (p q : PR 2) (N r x : PTm n) : ZT n :=
  ZT.ofNat (pw two r) * value p q N x - value p q (N + r) x

/-- The signed discrepancy for one adjacent pair. -/
def adjacent (p q : PR 2) (k x : PTm n) : ZT n :=
  ZT.ofNat two * value p q k x - value p q (succ k) x

ipra_subst value [ZT.subst]

ipra_subst difference

ipra_subst adjacent

private theorem value_congr (p q : PR 2) (x : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (value p q a x) = ZT.toZ Γ (value p q b x) := by
  have hq := natEq (congrAp2 q h (.eqRefl x))
  simpa only [value, ZT.toZ] using congrArg₂ HSub.hSub (natEq (congrAp2 p h (.eqRefl x))) hq

private theorem abs_scale (c : PTm n) (u : ZT n) :
    Γ ⊢[PRAAx] zabs (ZT.ofNat c * u) ≐ c * zabs u :=
  Foundations.GapDecision.zabs_scale c u

private theorem difference_zero (p q : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] zabs (difference p q N zero x) ≐ zero := by
  have hN := value_congr p q x (add_zero (Γ := Γ) N)
  have hd : ZT.toZ Γ (difference p q N zero x) = ZT.toZ Γ (ZT.natLit 0) := by
    simp only [difference, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, natEq (pw_zero (Γ := Γ) two), hN,
      ZT.toZ_natLit]
    simp [Q.mk_one, map_one]
  refine (zabs_congr hd).eqTrans ?_
  exact (congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _)

/-- One quantifier-free induction step, with the adjacent bound in context. -/
theorem discrepancy_step (p q : PR 2) (x : PTm n) {N r : PTm n}
    (ih : Γ ⊢[PRAAx] le (succ (zabs (difference p q N r x))) (pw two r))
    (motion : Γ ⊢[PRAAx] le (zabs (adjacent p q (N + r) x)) one) :
    Γ ⊢[PRAAx] le (succ (zabs (difference p q N (succ r) x))) (pw two (succ r)) := by
  have hP := natEq (pw_succ (Γ := Γ) two r)
  simp only [Q.mk_mul, map_mul] at hP
  have hN := value_congr p q x (add_succ (Γ := Γ) N r)
  have hd : ZT.toZ Γ (difference p q N (succ r) x) =
      ZT.toZ Γ (ZT.ofNat two * difference p q N r x) +
        ZT.toZ Γ (adjacent p q (N + r) x) := by
    simp only [difference, adjacent, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, hP, hN]
    ring
  have triangle := zabs_tri hd
  have scale := abs_scale (Γ := Γ) two (difference p q N r x)
  have bound : Γ ⊢[PRAAx] le (zabs (difference p q N (succ r) x))
      (two * zabs (difference p q N r x) + one) :=
    le_trans (le_congr (.eqRefl _) (congrAdd scale (.eqRefl _)) triangle)
      (add_le_add₂ (le_refl _) motion)
  have raised := le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
    (add_le_add_right one bound)
  have doubled := le_mul_mono (le_refl two) ih
  exact le_trans raised (le_congr (by ipra_ring)
    ((mul_comm _ _).eqTrans (pw_succ two r).eqSymm) doubled)

/-- All adjacent pairs at the supplied runtime parameter meet the unit bound. -/
def motion (p q : PR 2) (x : PTm n) : Fm PTm n :=
  .all (le (zabs (adjacent p q (var 0) (Syn.shift x))) one)

@[simp] theorem subst_motion {m : ℕ} (σ : Fin n → PTm m)
    (p q : PR 2) (x : PTm n) :
    (motion p q x).subst σ = motion p q (Syn.subst σ x) := by
  simp only [motion, Fm.subst_all, subst_le, subst_zabs, subst_adjacent,
    Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

@[simp] theorem shift_motion (p q : PR 2) (x : PTm n) :
    Fm.shift (motion p q x) = motion p q (Syn.shift x) := subst_motion _ _ _ _

/-- The sharp discrepancy bound at any starting index. -/
theorem discrepancy (p q : PR 2) (N r x : PTm n) (h : Γ ⊢[PRAAx] motion p q x) :
    Γ ⊢[PRAAx] le (succ (zabs (difference p q N r x))) (pw two r) := by
  have all : Γ ⊢[PRAAx] .all
      (le (succ (zabs (difference p q (Syn.shift N) (var 0) (Syn.shift x)))) (pw two (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_ <;>
      simp only [subst_le, ConciseIPRA.PTm.subst_succ, subst_zabs, subst_difference, subst_ap2,
        Syn.subst_var, Syn.inst_zero, Syn.repl_zero, Syn.subst_inst_shift, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero]
    · exact le_congr (congrSucc (difference_zero p q N x)).eqSymm
        (pw_zero two).eqSymm (le_refl one)
    · apply discrepancy_step p q (Syn.shift x) Prf.hyp0
      have shifted : Γ.map Fm.shift ⊢[PRAAx] (motion p q (Syn.shift x) : Fm PTm (n + 1)) := by
        simpa only [shift_motion] using h.shift
      have pair := Prf.allE (Syn.shift N + var 0) shifted
      simpa only [motion, subst_le, subst_zabs, subst_adjacent, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using pair.wk
  simpa only [subst_le, ConciseIPRA.PTm.subst_succ, subst_zabs,
    subst_difference, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] using Prf.allE r all

/-- The source form with endpoints `N ≤ M` and the canonical length `M ∸ N`. -/
theorem discrepancy_between (p q : PR 2) (x : PTm n) {N M : PTm n}
    (h : Γ ⊢[PRAAx] motion p q x) (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le
      (succ (zabs (ZT.ofNat (pw two (PTm.monus M N)) * value p q N x - value p q M x)))
      (pw two (PTm.monus M N)) := by
  have endpoint := value_congr p q x (eq_add_of_le order)
  have same : ZT.toZ Γ (difference p q N (PTm.monus M N) x) =
      ZT.toZ Γ (ZT.ofNat (pw two (PTm.monus M N)) * value p q N x - value p q M x) := by
    simp only [difference, ZT.toZ_sub, ← endpoint]
  exact le_congr (congrSucc (zabs_congr same)) (.eqRefl _) (discrepancy p q N _ x h)

/-- The dyadic Cauchy estimate at variables `N`, `r`, and runtime parameter `x`. -/
abbrev cauchyFormula (p q : PR 2) : Fm PTm 3 :=
  motion p q (var 2) ⟶
    le (succ (zabs (difference p q (var 0) (var 1) (var 2)))) (pw two (var 1))

theorem dyadic_cauchy (p q : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (cauchyFormula p q) :=
  closeUniv 3 (.impI (discrepancy p q _ _ _ Prf.hyp0))

/-- The source endpoint form, at `N`, `M`, and runtime parameter `x`. -/
abbrev endpointsFormula (p q : PR 2) : Fm PTm 3 :=
  motion p q (var 2) ⟶ le (var 0) (var 1) ⟶
    le (succ (zabs
      (ZT.ofNat (pw two (PTm.monus (var 1) (var 0))) * value p q (var 0) (var 2) -
        value p q (var 1) (var 2))))
      (pw two (PTm.monus (var 1) (var 0)))

theorem dyadic_endpoints (p q : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (endpointsFormula p q) :=
  closeUniv 3 (.impI (.impI (discrepancy_between p q _ Prf.hyp1 Prf.hyp0)))

/-- Instantiate a local certificate predicate at its precision, witness and parameter. -/
def certificate (C : Fm PTm 3) (k w x : PTm n) : Fm PTm n :=
  C.subst ![k, w, x]

/-- At each precision some local certificate exists. -/
def certificateCoverage (C : Fm PTm 3) (x : PTm n) : Fm PTm n :=
  .all (.ex (certificate C (var 1) (var 0) (Syn.shift (Syn.shift x))))

/-- Every certified adjacent pair has the required unit motion. -/
def certificateSoundness (C : Fm PTm 3) (p q : PR 2) (x : PTm n) : Fm PTm n :=
  .all (.all (certificate C (var 1) (var 0) (Syn.shift (Syn.shift x)) ⟶
    le (zabs (adjacent p q (var 1) (Syn.shift (Syn.shift x)))) one))

/-- Seal each local certificate while proving the public adjacent-motion contract. -/
theorem motion_of_certificates (C : Fm PTm 3) (p q : PR 2) (x : PTm n)
    (coverage : Γ ⊢[PRAAx] certificateCoverage C x)
    (soundness : Γ ⊢[PRAAx] certificateSoundness C p q x) :
    Γ ⊢[PRAAx] motion p q x := by
  apply Prf.allI
  refine .exE coverage.allOpen ?_
  have localBound := Prf.impE soundness.allOpen.allOpen.wk Prf.hyp0
  simpa only [Fm.shift, subst_le, subst_zabs, subst_adjacent,
    Syn.subst_var, Syn.shift_var, Fin.succ_zero_eq_one, Syn.shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using localBound

/-- Independent local certificates yield the sharp Cauchy bound. -/
theorem certified_discrepancy (C : Fm PTm 3) (p q : PR 2) (N r x : PTm n)
    (coverage : Γ ⊢[PRAAx] certificateCoverage C x)
    (soundness : Γ ⊢[PRAAx] certificateSoundness C p q x) :
    Γ ⊢[PRAAx] le (succ (zabs (difference p q N r x))) (pw two r) :=
  discrepancy p q N r x (motion_of_certificates C p q x coverage soundness)

/-- The source endpoint form of certificate coherence, at any `N ≤ M`. -/
theorem certified_between (C : Fm PTm 3) (p q : PR 2) (x : PTm n) {N M : PTm n}
    (coverage : Γ ⊢[PRAAx] certificateCoverage C x)
    (soundness : Γ ⊢[PRAAx] certificateSoundness C p q x)
    (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le
      (succ (zabs (ZT.ofNat (pw two (PTm.monus M N)) * value p q N x - value p q M x)))
      (pw two (PTm.monus M N)) :=
  discrepancy_between p q x (motion_of_certificates C p q x coverage soundness) order

/-- The certificate coherence corollary at indices `N`, `r` and parameter `x`. -/
abbrev certifiedCauchyFormula (C : Fm PTm 3) (p q : PR 2) : Fm PTm 3 :=
  certificateCoverage C (var 2) ⟶ certificateSoundness C p q (var 2) ⟶
    le (succ (zabs (difference p q (var 0) (var 1) (var 2)))) (pw two (var 1))

theorem certificates_coherent (C : Fm PTm 3) (p q : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (certifiedCauchyFormula C p q) :=
  closeUniv 3 (.impI (.impI (certified_discrepancy C p q _ _ _ Prf.hyp1 Prf.hyp0)))

/-- The same corollary with the source's ordered endpoint indices. -/
abbrev certifiedEndpointsFormula (C : Fm PTm 3) (p q : PR 2) : Fm PTm 3 :=
  certificateCoverage C (var 2) ⟶ certificateSoundness C p q (var 2) ⟶
    le (var 0) (var 1) ⟶
      le (succ (zabs
        (ZT.ofNat (pw two (PTm.monus (var 1) (var 0))) * value p q (var 0) (var 2) -
          value p q (var 1) (var 2))))
        (pw two (PTm.monus (var 1) (var 0)))

theorem certificates_coherent_endpoints (C : Fm PTm 3) (p q : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (certifiedEndpointsFormula C p q) :=
  closeUniv 3 (.impI (.impI (.impI
    (certified_between C p q _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

#print axioms dyadic_cauchy
#print axioms dyadic_endpoints
#print axioms certificates_coherent
#print axioms certificates_coherent_endpoints

end LeanProofs.IPRA.Analysis.DyadicCauchy
