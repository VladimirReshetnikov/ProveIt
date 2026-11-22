import Mathlib.Data.Nat.Choose.Basic
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Foundations.IntersectionEnumeration

/-!
# Finite Ramsey: the counting steps

Packet: `combinatorics/ramsey_ipra`, `ramsey.tex`, the counting behind the reservoir lemma and the graph
bounds, as iPRA derivations about natural terms (class counts as terms; the finitely many classes are indexed
in the metatheory, and the selected class is an object-level finite disjunction `disjFin`):

* `thinning` ("Finite thinning"): "If more than `qk` candidates receive one of `q` labels, at least one label
  occurs more than `k` times": from `q k < ∑ c_i` the disjunction `⋁_i k < c_i`, by a case split on each
  count;
* `reservoir_step` (the reservoir lemma, `eq:stable`): with `S_L(j+1) = L (S_L(j) + 1)`, a reservoir of size
  `> S_L(j+1)` split into `L` profile classes has a class of size `> S_L(j) + 1`;
* `chain_step` (the smaller bound `eq:U`): `D_i = 1 + Q_i D_{i+1}` and `D_{i+1} ≤ c P` give
  `D_i ≤ (c + 1) Q_i P`, the step of `D_0 ≤ (m + 1) ∏ Q_i`;
* `neighbor_split` ("Pascal's bound"): among `A + D − 1` neighbours "Either at least `A` are red neighbors,
  or at least `D` are blue neighbors";
* `pascal_bound`: `R(a,b) ≤ R(a−1,b) + R(a,b−1) ≤ C(a+b−2, a−1)` by Pascal's identity;
* `three_color_pivot` (`R(3,3,3) ≤ 17`): "one pivot has at least six neighbors joined to it in a common
  color, since `16 > 3·5`".
-/

namespace LeanProofs.IPRA.Combinatorics.RamseyBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (disjFin disjFin_intro disjFin_imp)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The sum of a finite family of terms (the number of candidates, by class). -/
def sumT : {q : ℕ} → (Fin q → PTm n) → PTm n
  | 0, _ => zero
  | _ + 1, c => c 0 + sumT fun i => c i.succ

/-- Finite thinning: more than `q k` candidates in `q` classes give a class with more than `k`. -/
theorem thinning : {q : ℕ} → {Γ : List (Fm PTm n)} → (c : Fin q → PTm n) → (k : PTm n) →
    (Γ ⊢[PRAAx] le (succ (num q * k)) (sumT c)) → (Γ ⊢[PRAAx] disjFin fun i => lt k (c i))
  | 0, Γ, _, k, h => by
    refine not_succ_le_self zero _ ?_
    have h' : Γ ⊢[PRAAx] le (succ (num 0 * k)) zero := h
    ipra_le sl h' using push_cast; ring
  | 1, Γ, c, k, h => by
    have h' : Γ ⊢[PRAAx] le (succ (num 1 * k)) (c 0 + zero) := h
    show Γ ⊢[PRAAx] le (succ k) (c 0)
    ipra_le sl h' using push_cast; ring
  | q + 2, Γ, c, k, h => by
    show Γ ⊢[PRAAx] lt k (c 0) ⋎ disjFin fun i : Fin (q + 1) => lt k (c i.succ)
    refine .orE (lt_or_le k (c 0)) (.orI₁ Prf.hyp0) (.orI₂ ?_)
    have h0 : (le (c 0) k :: Γ) ⊢[PRAAx] le (c 0) k := Prf.hyp0
    have h' : (le (c 0) k :: Γ) ⊢[PRAAx] le (succ (num (q + 2) * k)) (c 0 + sumT fun i => c i.succ) := h.wk
    refine thinning (fun i => c i.succ) k ?_
    ipra_le sl h' + sl h0 using push_cast; ring

/-- The reservoir step: more than `L (S + 1)` candidates in `L` profile classes give a class with more than
`S + 1` members (its first element is the next pivot, and more than `S` remain). -/
theorem reservoir_step {L : ℕ} (c : Fin L → PTm n) (S : PTm n)
    (h : Γ ⊢[PRAAx] le (succ (num L * succ S)) (sumT c)) : Γ ⊢[PRAAx] disjFin fun i => lt (succ S) (c i) :=
  thinning c (succ S) h

/-- The resource recurrence of the smaller bound: `D' ≤ 1 + Q D`, `D ≤ c P`, `1 ≤ Q`, `1 ≤ P` give
`D' ≤ (c + 1) Q P`. -/
theorem chain_step {D D' Q P c : PTm n} (hD' : Γ ⊢[PRAAx] le D' (succ (Q * D))) (h : Γ ⊢[PRAAx] le D (c * P))
    (hQ : Γ ⊢[PRAAx] le (succ zero) Q) (hP : Γ ⊢[PRAAx] le (succ zero) P) :
    Γ ⊢[PRAAx] le D' (succ c * (Q * P)) := by
  ipra_le sl hD' + 𝔟 Q * sl h + (sl hQ * sl hP + sl hQ + sl hP)

/-- Among `A + D − 1` neighbours, at least `A` are red or at least `D` are blue. -/
theorem neighbor_split {A D r b : PTm n} (h : Γ ⊢[PRAAx] le (A + D) (succ (r + b))) :
    Γ ⊢[PRAAx] le A r ⋎ le D b := by
  refine .orE (lt_or_le r A) (.orI₂ ?_) (.orI₁ Prf.hyp0)
  have hlt : (lt r A :: Γ) ⊢[PRAAx] le (succ r) A := Prf.hyp0
  have h' : (lt r A :: Γ) ⊢[PRAAx] le (A + D) (succ (r + b)) := h.wk
  ipra_le sl h' + sl hlt

/-- Pascal's bound: `R(a+2, b+2) ≤ R(a+1, b+2) + R(a+2, b+1) ≤ C(a+b+2, a+1)`. -/
theorem pascal_bound (a b : ℕ) {R RA RD : PTm n} (h : Γ ⊢[PRAAx] le R (RA + RD))
    (hA : Γ ⊢[PRAAx] le RA (num ((a + b + 1).choose a)))
    (hD : Γ ⊢[PRAAx] le RD (num ((a + b + 1).choose (a + 1)))) :
    Γ ⊢[PRAAx] le R (num ((a + b + 2).choose (a + 1))) := by
  have e : (a + b + 2).choose (a + 1) = (a + b + 1).choose a + (a + b + 1).choose (a + 1) :=
    Nat.choose_succ_succ (a + b + 1) a
  rw [e]
  ipra_le sl h + sl hA + sl hD using push_cast; ring

/-- `R(3,3,3) ≤ 17`: sixteen neighbours in three colours give at least six of one colour. -/
theorem three_color_pivot (c : Fin 3 → PTm n) (h : Γ ⊢[PRAAx] le (num 16) (sumT c)) :
    Γ ⊢[PRAAx] disjFin fun i => lt (num 5) (c i) := by
  refine thinning c (num 5) ?_
  ipra_le sl h using push_cast; ring

end LeanProofs.IPRA.Combinatorics.RamseyBounds
