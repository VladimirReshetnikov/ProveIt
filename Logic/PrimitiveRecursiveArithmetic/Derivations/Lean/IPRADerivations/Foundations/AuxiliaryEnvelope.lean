import IPRADerivations.Probability.Lotus
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.SumOrder

/-!
# The cardinality bounds of the auxiliary envelope (`ipra_resources_and_elimination_2026-11-15`, `thm:elim-envelope`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, Section 5.

`thm:elim-envelope`: under the pointwise assumption (E11), "A coarse bound on the number of
points is `d e B(e, H)`" (E12). Proof: "There are at most `B(e, H)` candidates and each
successful candidate has degree at most `e`, so its list has at most `de` entries."

The comparison after the theorem: "suppose only that every finite list of target points can be
covered by at most `M` auxiliary equations of degree at most `e` ... Assign every list entry to
its first covering equation. Each group has at most `de` points by Theorem `thm:elim-bezout`,
hence every distinct target list has length at most `M d e`. This is a valid finite cardinality
argument."

The completeness half of `thm:elim-envelope` (eliminating the bounded existential without a
selector) is `Foundations/ExhaustiveWitness.exhaustive_complete`, with the candidates indexed
below the box size. This module derives the two counting statements:

* `sum_le_const`: if `f(c) ≤ L` for all `c < N`, then `∑_{c<N} f(c) ≤ N · L`;
* `envelope_card` (E12): if every candidate list has length at most `d · e`, the concatenation
  over `B` candidates has length at most `B · (d · e)`;
* `cnt σ N k x`: the number of positions `i < N` assigned to the class `k`;
* `fibre_count`: if every position is assigned a class below `M` and every class receives at
  most `L` positions, then `N ≤ M · L` (the positions are counted class by class:
  `Probability/Lotus.pushforward_total` with unit weights);
* `cover_card`: with `L = d · e`, the list length is at most `M · (d · e)`.

Not derived: `thm:elim-bezout` itself (each group has at most `d e` points) and the
enumeration of the coefficient box `𝓑(e, H)` as a list.
-/

namespace LeanProofs.IPRA.Foundations.AuxiliaryEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Lotus (vB pvB inst2_pvB pushforward_total)
open LeanProofs.IPRA.Probability.Variance (sum_one sum_const_of)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## A sum of bounded terms -/

/-- The constant body that returns its parameter. -/
def kB : PTm 2 := var 1

theorem inst2_kB (i L : PTm n) : inst2 kB i L = L := by simp [inst2, kB]

/-- `f(c) ≤ L` for all `c < N` gives `∑_{c<N} f(c) ≤ N · L`. -/
theorem sum_le_const (f : PTm 2) {N L x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (Syn.shift L))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (N * L) := by
  have c : Γ ⊢[PRAAx] ap2 (sumF kB) N L ≐ N * L :=
    sum_const_of kB N L L (.allI (.impI (by rw [inst2_kB]; exact .eqRefl _)))
  refine le_congr (.eqRefl _) c (sum_le_params f kB x L N ?_)
  simpa only [inst2_kB] using h

/-- (E12): `B` candidate lists of length at most `d · e` have total length at most
`B · (d · e)`. -/
theorem envelope_card (len : PTm 2) {B d e x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (inst2 len (var 0) (Syn.shift x)) (Syn.shift (d * e)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF len) B x) (B * (d * e)) :=
  sum_le_const len h

/-! ## Counting class by class -/

section Fibre

variable (σ : PTm 2)

/-- The number of positions `i < N` with `σ(i, x) = k`. -/
abbrev cnt (N k x : PTm n) : PTm n := ap2 (sumF (vB (one : PTm 2) σ)) N (pairT k x)

theorem shift_pair (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem pair_congr {a a' c c' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hc : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] pairT a c ≐ pairT a' c' :=
  congrAdd (congrMul (congrAdd ha hc) (congrAdd ha hc)) ha

/-- If every position has a class below `M` and every class has at most `L` positions among
the first `N`, then `N ≤ M · L`. -/
theorem fibre_count {M L x : PTm n} (N : PTm n)
    (hr : Γ ⊢[PRAAx] Permutation.rangeAll σ M x)
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (cnt σ (Syn.shift N) (var 0) (Syn.shift x)) (Syn.shift L))) :
    Γ ⊢[PRAAx] le N (M * L) := by
  refine le_congr ((pushforward_total (one : PTm 2) σ hr N).eqTrans (sum_one N x)) (.eqRefl _)
    (sum_le_const (pvB (one : PTm 2) σ) (.allI (.impI ?_)))
  rw [inst2_pvB, shift_pair]
  exact le_congr
    (congrAp2 _ (fst_pair _ _).eqSymm (pair_congr (.eqRefl _) (snd_pair _ _).eqSymm))
    (.eqRefl _) (.impE hc.allOpen.wk Prf.hyp0)

/-- The comparison after `thm:elim-envelope`: a list covered by `M` classes of at most `d · e`
entries has length at most `M · (d · e)`. -/
theorem cover_card {M d e x : PTm n} (N : PTm n)
    (hr : Γ ⊢[PRAAx] Permutation.rangeAll σ M x)
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (cnt σ (Syn.shift N) (var 0) (Syn.shift x)) (Syn.shift (d * e)))) :
    Γ ⊢[PRAAx] le N (M * (d * e)) :=
  fibre_count σ N hr hc

end Fibre

end LeanProofs.IPRA.Foundations.AuxiliaryEnvelope
