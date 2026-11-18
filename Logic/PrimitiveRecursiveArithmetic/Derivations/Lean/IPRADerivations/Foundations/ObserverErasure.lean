import IPRADerivations.Foundations.LeastBoundedWitness
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Foundations.IterationFusion

/-!
# Erasing the choice of a certificate behind a stable observer

The certificates of a query are the `a < N` with `f(a, x) = 0`; an observer is a term `O(a, x)`. If all
accepted certificates have the same observation, or observations within `δ` of each other, the observation
of the least accepted certificate `a_* = μ` (`Core/Search`) is a canonical primitive recursive output, and the
hidden witness does not appear in the exported statement.

Packets (`docs/proofs/foundations`):

* `ipra_kifc_framework_2026-11-15` and `ipra_kifc_framework_2026-11-16`, `thm:stable-exact` ("Exact
  stable-observer elimination") and `thm:stable-approx` ("Approximate choice erasure", first statement);
* `ocipra_framework_2026-11-15`, `thm:stable-exact`, `thm:stable-approx` (first statement), for a bounded
  certificate search;
* `FINER-iPRA-framework-2026-11-16`, `thm:choice-erasure` (i) and (iii);
* `STRIVE-iPRA-framework-2026-11-16`, Theorem "Exact observation erasure" (an observation is realized, and
  any two are equal);
* `scope_ipra_framework_2026-11-16`, Theorem "Metric observer elimination" (the canonical center `O(μ)`).

Statements, for a totality premise `∃ a < N. f(a, x) = 0`:

* `Stable f O x`: `∀ a b. f(a, x) = 0 → f(b, x) = 0 → O(a, x) = O(b, x)`; `stable_at` instantiates it;
* `selected_valid`: `f(a_*, x) = 0` and `a_* < N`;
* `exact_erasure`: `f(a, x) = 0` gives `O(a_*, x) = O(a, x)`;
* `exact_erasure_imp`: the same under a precondition `H`, as `H → f(a, x) = 0 → O(a_*, x) = O(a, x)`, from
  `H → ∃ a < N. f(a, x) = 0` and `H → Stable`;
* `Diam f O x δ`: `∀ a b. f(a, x) = 0 → f(b, x) = 0 → O(a, x) ≤ O(b, x) + δ` (numerators over a common
  denominator; the hypothesis is symmetric in `a`, `b`);
* `metric_erasure`: `f(a, x) = 0` gives `O(a_*, x) ≤ O(a, x) + δ` and `O(a, x) ≤ O(a_*, x) + δ`;
* `sealed_consumer`: a conclusion `C` derived from the canonical witness, `a_* < N → f(a_*, x) = 0 → C`,
  follows from the bounded existential alone: `(∃ a < N. f(a, x) = 0) → C`.

* `QStable f O E x`: `∀ a b. f(a, x) = 0 → f(b, x) = 0 → E(O(a, x), O(b, x))` for a relation `E` on
  observations; `quotient_erasure` (FINER `thm:choice-erasure` (ii)): `f(a, x) = 0` gives
  `E(O(a_*, x), O(a, x))`. No property of `E` is used.

The composition with a downstream modulus and the regular-name statements are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ObserverErasure

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Search (mu)
open LeanProofs.IPRA.Foundations.LeastBoundedWitness (ExW lt_of_exists)
open LeanProofs.IPRA.Foundations.IterationFusion (rel subst_rel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Exact pairwise stability of the observer on accepted certificates. -/
def Stable (f O : PTm 2) (x : PTm n) : Fm PTm n :=
  .all (.all ((inst2 f (var 1) (Syn.shift (Syn.shift x)) ≐ zero) ⟶
    ((inst2 f (var 0) (Syn.shift (Syn.shift x)) ≐ zero) ⟶
      (inst2 O (var 1) (Syn.shift (Syn.shift x)) ≐ inst2 O (var 0) (Syn.shift (Syn.shift x))))))

/-- Pairwise stability up to `δ`. -/
def Diam (f O : PTm 2) (x δ : PTm n) : Fm PTm n :=
  .all (.all ((inst2 f (var 1) (Syn.shift (Syn.shift x)) ≐ zero) ⟶
    ((inst2 f (var 0) (Syn.shift (Syn.shift x)) ≐ zero) ⟶
      le (inst2 O (var 1) (Syn.shift (Syn.shift x)))
        (inst2 O (var 0) (Syn.shift (Syn.shift x)) + Syn.shift (Syn.shift δ)))))

/-- Pairwise stability of the observer up to a relation `E` on observations. -/
def QStable (f O : PTm 2) (E : Fm PTm 2) (x : PTm n) : Fm PTm n :=
  .all (.all ((inst2 f (var 1) (Syn.shift (Syn.shift x)) ≐ zero) ⟶
    ((inst2 f (var 0) (Syn.shift (Syn.shift x)) ≐ zero) ⟶
      rel E (inst2 O (var 1) (Syn.shift (Syn.shift x))) (inst2 O (var 0) (Syn.shift (Syn.shift x))))))

section Erasure

variable {f O : PTm 2} {N x : PTm n}

theorem stable_at (h : Γ ⊢[PRAAx] Stable f O x) {a b : PTm n} (ha : Γ ⊢[PRAAx] inst2 f a x ≐ zero)
    (hb : Γ ⊢[PRAAx] inst2 f b x ≐ zero) : Γ ⊢[PRAAx] inst2 O a x ≐ inst2 O b x := by
  have i := Prf.allE b (Prf.allE a h)
  have body : Γ ⊢[PRAAx] (inst2 f a x ≐ zero) ⟶ ((inst2 f b x ≐ zero) ⟶ (inst2 O a x ≐ inst2 O b x)) := by
    simpa [Stable, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using i
  exact Prf.impE (Prf.impE body ha) hb

theorem diam_at {δ : PTm n} (h : Γ ⊢[PRAAx] Diam f O x δ) {a b : PTm n}
    (ha : Γ ⊢[PRAAx] inst2 f a x ≐ zero) (hb : Γ ⊢[PRAAx] inst2 f b x ≐ zero) :
    Γ ⊢[PRAAx] le (inst2 O a x) (inst2 O b x + δ) := by
  have i := Prf.allE b (Prf.allE a h)
  have body : Γ ⊢[PRAAx] (inst2 f a x ≐ zero) ⟶
      ((inst2 f b x ≐ zero) ⟶ le (inst2 O a x) (inst2 O b x + δ)) := by
    simpa [Diam, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using i
  exact Prf.impE (Prf.impE body ha) hb

/-- The least certificate is accepted and below the bound. -/
theorem selected_valid (hex : Γ ⊢[PRAAx] ExW f N x) :
    Γ ⊢[PRAAx] lt (mu f N x) N ⋏ (inst2 f (mu f N x) x ≐ zero) :=
  lt_of_exists hex

/-- "Exact stable-observer elimination": every accepted certificate has the observation of the least
one. -/
theorem exact_erasure (hex : Γ ⊢[PRAAx] ExW f N x) (hst : Γ ⊢[PRAAx] Stable f O x) {a : PTm n}
    (ha : Γ ⊢[PRAAx] inst2 f a x ≐ zero) : Γ ⊢[PRAAx] inst2 O (mu f N x) x ≐ inst2 O a x :=
  stable_at hst (Prf.andE₂ (lt_of_exists hex)) ha

/-- The same under a precondition `H`. -/
theorem exact_erasure_imp {H : Fm PTm n} (htot : Γ ⊢[PRAAx] H ⟶ ExW f N x)
    (hst : Γ ⊢[PRAAx] H ⟶ Stable f O x) (a : PTm n) :
    Γ ⊢[PRAAx] H ⟶ ((inst2 f a x ≐ zero) ⟶ (inst2 O (mu f N x) x ≐ inst2 O a x)) := by
  refine .impI (.impI ?_)
  have hH : ((inst2 f a x ≐ zero) :: H :: Γ) ⊢[PRAAx] H := Prf.hyp1
  have ha : ((inst2 f a x ≐ zero) :: H :: Γ) ⊢[PRAAx] inst2 f a x ≐ zero := Prf.hyp0
  exact exact_erasure (Prf.impE htot.wk.wk hH) (Prf.impE hst.wk.wk hH) ha

/-- "Approximate choice erasure": every accepted observation is within `δ` of the observation of the least
certificate. -/
theorem metric_erasure {δ : PTm n} (hex : Γ ⊢[PRAAx] ExW f N x) (hd : Γ ⊢[PRAAx] Diam f O x δ)
    {a : PTm n} (ha : Γ ⊢[PRAAx] inst2 f a x ≐ zero) :
    Γ ⊢[PRAAx] le (inst2 O (mu f N x) x) (inst2 O a x + δ) ⋏ le (inst2 O a x) (inst2 O (mu f N x) x + δ) :=
  .andI (diam_at hd (Prf.andE₂ (lt_of_exists hex)) ha) (diam_at hd ha (Prf.andE₂ (lt_of_exists hex)))

/-- A conclusion derived from the canonical witness follows from the bounded existential alone. -/
theorem sealed_consumer {C : Fm PTm n}
    (h : Γ ⊢[PRAAx] lt (mu f N x) N ⟶ ((inst2 f (mu f N x) x ≐ zero) ⟶ C)) :
    Γ ⊢[PRAAx] ExW f N x ⟶ C := by
  refine .impI ?_
  have hex : (ExW f N x :: Γ) ⊢[PRAAx] ExW f N x := Prf.hyp0
  have v := lt_of_exists hex
  exact Prf.impE (Prf.impE h.wk (Prf.andE₁ v)) (Prf.andE₂ v)

theorem qstable_at {E : Fm PTm 2} (h : Γ ⊢[PRAAx] QStable f O E x) {a b : PTm n}
    (ha : Γ ⊢[PRAAx] inst2 f a x ≐ zero) (hb : Γ ⊢[PRAAx] inst2 f b x ≐ zero) :
    Γ ⊢[PRAAx] rel E (inst2 O a x) (inst2 O b x) := by
  have i := Prf.allE b (Prf.allE a h)
  have body : Γ ⊢[PRAAx] (inst2 f a x ≐ zero) ⟶
      ((inst2 f b x ≐ zero) ⟶ rel E (inst2 O a x) (inst2 O b x)) := by
    simpa [QStable, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using i
  exact Prf.impE (Prf.impE body ha) hb

/-- FINER `thm:choice-erasure` (ii): every accepted observation is `E`-related to the observation of the
least certificate. -/
theorem quotient_erasure {E : Fm PTm 2} (hex : Γ ⊢[PRAAx] ExW f N x) (hq : Γ ⊢[PRAAx] QStable f O E x)
    {a : PTm n} (ha : Γ ⊢[PRAAx] inst2 f a x ≐ zero) :
    Γ ⊢[PRAAx] rel E (inst2 O (mu f N x) x) (inst2 O a x) :=
  qstable_at hq (Prf.andE₂ (lt_of_exists hex)) ha

end Erasure

end LeanProofs.IPRA.Foundations.ObserverErasure
