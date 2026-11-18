import IPRADerivations.Foundations.ApproximateWitness
import IPRADerivations.Core.OrderCertificates

/-!
# Gap stabilization of approximate minimizers

Packets:

* `foundations/scope_ipra_framework_2026-11-16`, `sections/10_observers.tex`, Theorem "Finite gap
  stabilization": if the exact scores `s_L` have a minimizer `L_*` with `s_L ≥ s_{L_*} + g` for `L ≠ L_*`,
  and approximations `ã_L` satisfy `|ã_L − s_L| ≤ e` with `2e < g`, then the least minimizer of the
  approximate scores is exactly `L_*`;
* `foundations/ipra_pfig_framework_2026-11-15`, `thm:branch-stability` ("Guarded branch stabilization"), the
  same statement;
* `foundations/scoped_certificate_realization_ipra_2026-11-16`, `paper/sections/10_observer.tex`, the lemma
  "Gap stabilization": labels at mutual distance at least `g`, observations within `e` of labels `i` and
  `j` and within `δ` of each other, and `2e + δ < g`, give `i = j`.

Scores, errors and gaps are natural numerators over a common denominator supplied by the application. The
selector is `ApproximateWitness.argmin`, the least index attaining the minimum on `0, …, K`.

* `gap_stable`: under the two-sided error bounds and the gap hypothesis for all labels `L ≤ K` (object-level
  bounded universal hypotheses), `argmin ã K x = L_*`;
* `metric_gap`: the label lemma, with the distances as numbers and the triangle inequality
  `d(ℓ_i, ℓ_j) ≤ d(o, ℓ_i) + d(o, o') + d(o', ℓ_j)` as a hypothesis.

Both use the decidability of equality (`eq_or_ne`) in place of the papers' argument by contradiction.

* `gap_decision_zero`, `gap_decision_large` (`foundations/ipra_cfp_contract_compiler_2026-11-15`,
  `paper/sections/07_branching.tex`, "Gap-decision theorem"): for magnitudes `X = |x|`, `A = |a|` with
  `|X − A| < δ/4`, written `4X < 4A + δ` and `4A < 4X + δ`, and the finite evidence `X = 0 ∨ δ ≤ X`, the
  rational test `2A < δ` decides the alternative: `2A < δ` gives `X = 0`, and `δ ≤ 2A` gives `δ ≤ X`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.GapStabilization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.ApproximateWitness (argmin argmin_spec argmin_minimal)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The arithmetic core: a label other than `L_*` cannot be an approximate minimizer. -/
theorem gap_absurd {sm ss am as e g : PTm n} (hgap : Γ ⊢[PRAAx] le (ss + g) sm)
    (hup : Γ ⊢[PRAAx] le sm (am + e)) (hmin : Γ ⊢[PRAAx] le am as) (hlo : Γ ⊢[PRAAx] le as (ss + e))
    (h2e : Γ ⊢[PRAAx] lt (e + e) g) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have h2e' : Γ ⊢[PRAAx] le (succ (e + e)) g := h2e
  have h₁ : Γ ⊢[PRAAx] le (ss + g) (ss + (e + e)) := by
    ipra_le sl hgap + sl hup + sl hmin + sl hlo
  have h₂ : Γ ⊢[PRAAx] lt (ss + (e + e)) (ss + g) := by
    show Γ ⊢[PRAAx] le (succ (ss + (e + e))) (ss + g)
    ipra_le sl h2e'
  exact le_lt_absurd φ h₁ h₂

section Gap

variable {s a : PTm 2} {K x Ls e g : PTm n}

/-- "Finite gap stabilization": the least minimizer of the approximate scores is the exact minimizer. -/
theorem gap_stable (hLs : Γ ⊢[PRAAx] le Ls K)
    (hup : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift K) ⟶
      le (inst2 s (var 0) (Syn.shift x)) (inst2 a (var 0) (Syn.shift x) + Syn.shift e)))
    (hlo : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift K) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 s (var 0) (Syn.shift x) + Syn.shift e)))
    (hgap : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift K) ⟶ (neg (var 0 ≐ Syn.shift Ls) ⟶
      le (inst2 s (Syn.shift Ls) (Syn.shift x) + Syn.shift g) (inst2 s (var 0) (Syn.shift x)))))
    (h2e : Γ ⊢[PRAAx] lt (e + e) g) : Γ ⊢[PRAAx] argmin a K x ≐ Ls := by
  have hm : Γ ⊢[PRAAx] le (argmin a K x) K := Prf.andE₁ (argmin_spec a K x)
  have hmin : Γ ⊢[PRAAx] le (inst2 a (argmin a K x) x) (inst2 a Ls x) := argmin_minimal a hLs
  have u := Prf.allE (argmin a K x) hup
  simp only [Fm.subst_imp, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at u
  have l := Prf.allE Ls hlo
  simp only [Fm.subst_imp, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at l
  have gp := Prf.allE (argmin a K x) hgap
  simp only [Fm.subst_imp, Fm.subst_eq, subst_neg, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at gp
  have u' := Prf.impE u hm
  have l' := Prf.impE l hLs
  have gp' := Prf.impE gp hm
  refine .orE (eq_or_ne (argmin a K x) Ls) Prf.hyp0 ?_
  exact gap_absurd (Prf.impE gp'.wk Prf.hyp0) u'.wk hmin.wk l'.wk h2e.wk _

end Gap

/-- "Gap stabilization" for labels: with `D = d(ℓ_i, ℓ_j)`, `a = d(o, ℓ_i)`, `b = d(o', ℓ_j)`,
`c = d(o, o')`: if distinct labels are at distance at least `g`, `a, b ≤ e`, `c ≤ δ`, the triangle
inequality `D ≤ a + c + b` holds and `2e + δ < g`, then `i = j`. -/
theorem metric_gap {i j D a b c e δ g : PTm n} (hsep : Γ ⊢[PRAAx] neg (i ≐ j) ⟶ le g D)
    (htri : Γ ⊢[PRAAx] le D (a + c + b)) (ha : Γ ⊢[PRAAx] le a e) (hb : Γ ⊢[PRAAx] le b e)
    (hc : Γ ⊢[PRAAx] le c δ) (hg : Γ ⊢[PRAAx] lt (e + e + δ) g) : Γ ⊢[PRAAx] i ≐ j := by
  refine .orE (eq_or_ne i j) Prf.hyp0 ?_
  have hD : (neg (i ≐ j) :: Γ) ⊢[PRAAx] le g D := .impE hsep.wk Prf.hyp0
  have h₁ : (neg (i ≐ j) :: Γ) ⊢[PRAAx] le g (e + e + δ) := by
    ipra_le sl hD + sl htri.wk + sl ha.wk + sl hb.wk + sl hc.wk
  exact le_lt_absurd _ h₁ hg.wk

/-! ## The gap decision -/

section Decision

variable {X A δ : PTm n}

/-- If the test `2A < δ` succeeds, the alternative `δ ≤ X` is impossible, so `X = 0`. -/
theorem gap_decision_zero (hev : Γ ⊢[PRAAx] (X ≐ zero) ⋎ le δ X)
    (h₁ : Γ ⊢[PRAAx] lt (X + X + X + X) (A + A + A + A + δ)) (ht : Γ ⊢[PRAAx] lt (A + A) δ) :
    Γ ⊢[PRAAx] X ≐ zero := by
  refine .orE hev Prf.hyp0 ?_
  have hd : (le δ X :: Γ) ⊢[PRAAx] le δ X := Prf.hyp0
  have h₁' : (le δ X :: Γ) ⊢[PRAAx] le (succ (X + X + X + X)) (A + A + A + A + δ) := h₁.wk
  have ht' : (le δ X :: Γ) ⊢[PRAAx] le (succ (A + A)) δ := ht.wk
  have bad : (le δ X :: Γ) ⊢[PRAAx] le (succ (succ (succ δ))) zero := by
    ipra_le 4 * sl hd + sl h₁' + 2 * sl ht'
  exact le_lt_absurd _ bad (zero_lt_succ _)

/-- If the test fails, `δ ≤ 2A`, the alternative `X = 0` is impossible, so `δ ≤ X`. -/
theorem gap_decision_large (hev : Γ ⊢[PRAAx] (X ≐ zero) ⋎ le δ X)
    (h₂ : Γ ⊢[PRAAx] lt (A + A + A + A) (X + X + X + X + δ)) (ht : Γ ⊢[PRAAx] le δ (A + A)) :
    Γ ⊢[PRAAx] le δ X := by
  refine .orE hev ?_ Prf.hyp0
  have h0 : ((X ≐ zero) :: Γ) ⊢[PRAAx] X ≐ zero := Prf.hyp0
  have e := natEq h0
  have h₂' : ((X ≐ zero) :: Γ) ⊢[PRAAx] le (succ (A + A + A + A)) (X + X + X + X + δ) := h₂.wk
  have ht' : ((X ≐ zero) :: Γ) ⊢[PRAAx] le δ (A + A) := ht.wk
  have bad : ((X ≐ zero) :: Γ) ⊢[PRAAx] le (succ (A + A)) zero := by
    ipra_le sl h₂' + sl ht' using linear_combination -4 * e
  exact le_lt_absurd _ bad (zero_lt_succ _)

end Decision

end LeanProofs.IPRA.Foundations.GapStabilization
