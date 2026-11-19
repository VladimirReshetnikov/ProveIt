import IPRADerivations.Foundations.RationalRootScan
import IPRADerivations.AnalyticNumberTheory.Valuation

/-!
# The rational-root list with its substitution test as a term (`ipra_presentations_to_witnesses`, `lem:norm-rational-roots`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:norm-rational-roots`: "Define
`Roots_ℚ(H)` by scanning all pairs ... and retaining `p/q` exactly when `H(p/q) = 0`. ...
Soundness follows from the final exact substitution test." (Also `lem:elim-rational-roots` of
`ipra_resources_and_elimination_2026-11-15`: "retain coprime pairs whose exact substitution
into `P` is zero".)

`Foundations/RationalRootScan` proves soundness, completeness and the absence of repetitions
for an arbitrary retention test, and lists the test "as a primitive recursive program on
coefficient codes" as not derived. Here it is constructed, in the natural-number form of
`Foundations/RationalRootDegree` (coefficient lists `a`, `b` for the two signs, degree `d`,
parameter `x`): the cleared polynomial `Σ_{i ≤ d} c_i p^i q^{d ∸ i}` is already a term in the
code `n` of the pair and in `⟨d, x⟩`.

* `side c`: `Σ_{i ≤ d} c_i p^i q^{d ∸ i}` with `p = fst n`, `q = snd n`, as a term in
  `n` and `⟨d, x⟩`; `side_gen`, `side_at`: its value;
* `rootK a b`: the bit of `side a = side b`, the exact substitution test of the cleared
  equation; `rootK_at`;
* `root_test_of_eq`, `eq_of_root_test`: the test is nonzero exactly when the cleared equation
  holds at the decoded pair;
* `roots_sound`: every listed code decodes to a pair satisfying the cleared equation;
* `roots_listed`: every reduced root with nonzero numerator (and `c_0`, `c_d ≠ 0`) is listed,
  at the index given by its rank, in the scan of radius `B(H)`.

So `r ↦ sel (rootK a b) r (box B(H)) ⟨d, x⟩`, `r < rank (rootK a b) (box B(H)) ⟨d, x⟩`, is a
term-defined list with derived soundness and completeness and without repeated codes
(`scan_nodup`). The coprimality filter is not included: the list contains every pair of the box
satisfying the cleared equation, and each rational root occurs in reduced form among them
(`reduced_unique` identifies reduced representatives). Not derived: clearing the denominators
of a rational polynomial.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RationalRootList

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RationalRootDegree (Bez P tB)
open LeanProofs.IPRA.Foundations.RationalRootScan (absd height box scan_sound roots_complete)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel)
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

theorem pair_congr {s s' t t' : PTm k} (hs : Γ ⊢[PRAAx] s ≐ s') (ht : Γ ⊢[PRAAx] t ≐ t') :
    Γ ⊢[PRAAx] pairT s t ≐ pairT s' t' :=
  congrAdd (congrMul (congrAdd hs ht) (congrAdd hs ht)) hs

/-- The cleared polynomial of the coefficient list `c` at the pair coded by variable `0`, with
variable `1 = ⟨d, x⟩`. -/
def side (c : PTm 2) : PTm 2 :=
  ap2 (sumF (tB c)) (succ (fstT (var 1)))
    (pairT (fstT (var 0)) (pairT (sndT (var 0)) (pairT (fstT (var 1)) (sndT (var 1)))))

theorem side_gen (c : PTm 2) (n d x : PTm k) :
    Γ ⊢[PRAAx] inst2 (side c) n (pairT d x) ≐ P c (succ d) (fstT n) (sndT n) d x := by
  have e : inst2 (side c) n (pairT d x) =
      ap2 (sumF (tB c)) (succ (fstT (pairT d x)))
        (pairT (fstT n) (pairT (sndT n) (pairT (fstT (pairT d x)) (sndT (pairT d x))))) := by
    simp [inst2, side]
  rw [e]
  exact congrAp2 (sumF (tB c)) (congrSucc (fst_pair d x))
    (pair_congr (.eqRefl _) (pair_congr (.eqRefl _) (pair_congr (fst_pair d x) (snd_pair d x))))

theorem side_at (c : PTm 2) (p q d x : PTm k) :
    Γ ⊢[PRAAx] inst2 (side c) (pairT p q) (pairT d x) ≐ P c (succ d) p q d x :=
  (side_gen c (pairT p q) d x).eqTrans
    (congrAp2 (sumF (tB c)) (.eqRefl _)
      (pair_congr (fst_pair p q) (pair_congr (snd_pair p q) (.eqRefl _))))

variable (a b : PTm 2)

/-- The exact substitution test of the cleared equation. -/
def rootK : PTm 2 := eqb (side a) (side b)

theorem rootK_at (n y : PTm k) :
    inst2 (rootK a b) n y = eqb (inst2 (side a) n y) (inst2 (side b) n y) := by
  simp [inst2, rootK]

/-- A pair satisfying the cleared equation passes the test. -/
theorem root_test_of_eq {p q d x : PTm k}
    (h : Γ ⊢[PRAAx] P a (succ d) p q d x ≐ P b (succ d) p q d x) :
    Γ ⊢[PRAAx] neg (inst2 (rootK a b) (pairT p q) (pairT d x) ≐ zero) := by
  rw [rootK_at]
  have e : Γ ⊢[PRAAx] inst2 (side a) (pairT p q) (pairT d x) ≐
      inst2 (side b) (pairT p q) (pairT d x) :=
    (side_at a p q d x).eqTrans (h.eqTrans (side_at b p q d x).eqSymm)
  exact .impI (one_ne_zero _ ((eqb_of_eq e.wk).eqSymm.eqTrans Prf.hyp0))

/-- A code passing the test decodes to a pair satisfying the cleared equation. -/
theorem eq_of_root_test {n d x : PTm k}
    (h : Γ ⊢[PRAAx] neg (inst2 (rootK a b) n (pairT d x) ≐ zero)) :
    Γ ⊢[PRAAx] P a (succ d) (fstT n) (sndT n) d x ≐ P b (succ d) (fstT n) (sndT n) d x := by
  rw [rootK_at] at h
  exact (side_gen a n d x).eqSymm.eqTrans ((eq_of_eqb_ne h).eqTrans (side_gen b n d x))

/-- Soundness of the root list: every listed code decodes to a root of the cleared equation. -/
theorem roots_sound {r B d x : PTm k}
    (h : Γ ⊢[PRAAx] lt r (rank (rootK a b) (box B) (pairT d x))) :
    Γ ⊢[PRAAx]
      P a (succ d) (fstT (sel (rootK a b) r (box B) (pairT d x)))
          (sndT (sel (rootK a b) r (box B) (pairT d x))) d x ≐
        P b (succ d) (fstT (sel (rootK a b) r (box B) (pairT d x)))
          (sndT (sel (rootK a b) r (box B) (pairT d x))) d x :=
  eq_of_root_test a b (Prf.andE₂ (scan_sound (rootK a b) h))

/-- Completeness of the root list: every reduced root with nonzero numerator is listed in the
scan of radius `B(H)`. -/
theorem roots_listed {p' q' u v d x : PTm k} (hB : Γ ⊢[PRAAx] Bez p' (succ q') u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) (succ p') (succ q') d x ≐ P b (succ d) (succ p') (succ q') d x)
    (h0 : Γ ⊢[PRAAx] absd a b zero x ≐ succ (pred (absd a b zero x)))
    (hd : Γ ⊢[PRAAx] absd a b d x ≐ succ (pred (absd a b d x))) :
    Γ ⊢[PRAAx]
      lt (rank (rootK a b) (pairT (succ p') (succ q')) (pairT d x))
          (rank (rootK a b) (box (height a b d x)) (pairT d x)) ⋏
        (sel (rootK a b) (rank (rootK a b) (pairT (succ p') (succ q')) (pairT d x))
            (box (height a b d x)) (pairT d x) ≐ pairT (succ p') (succ q')) :=
  roots_complete (rootK a b) a b hB hE h0 hd (root_test_of_eq a b hE)

end LeanProofs.IPRA.Foundations.RationalRootList
