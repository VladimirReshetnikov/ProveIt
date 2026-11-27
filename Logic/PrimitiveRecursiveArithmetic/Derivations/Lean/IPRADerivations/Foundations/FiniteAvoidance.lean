import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Foundations.AuxiliaryEnvelope

/-!
# Finite avoidance by counting (`platonic_solids_ipra`, `lem:height`)

Packet: `geometry/platonic_solids_ipra`, `02_counting.tex`, lemma `lem:height`: "For `V`
distinct exactly represented points in three dimensions one can construct a linear functional
taking distinct values on all the points by trying at most `2·C(V, 2) + 1` integer candidates."
Proof: "Try `h_t(x, y, z) = x + ty + t²z` for integers `0 ≤ t ≤ 2·C(V, 2)`. For any distinct
pair of points, equality of their heights is a nonzero polynomial equation of degree at most
two in `t`. Such a polynomial has at most two distinct roots ... There are at most `2·C(V, 2)`
forbidden values. Testing the displayed list therefore returns a valid candidate. This is the
finite pigeonhole argument on decidable lists."

The same scan occurs in `ipra_resources_and_elimination_2026-11-15`, `lem:elim-shear` ("A scan
with a success flag, frozen at the first passing candidate, returns the required `c`").

The counting argument, for an arbitrary bit `bad(t, c, x)` ("candidate `t` violates constraint
`c`"), with `T` candidates and `P` constraints:

* `exists_good`: if every constraint is violated by at most `L` candidates and `P · L < T`,
  then some candidate violates no constraint: the bounded-search bit is one. The violations
  are counted by candidates and by constraints (`Core/Fubini`): `T ≤ ∑_t ∑_c ≤ P · L` would
  follow if every candidate violated something;
* `good T P x`: the first such candidate, a term; `good_lt`, `good_row` (it violates no
  constraint: its row count is zero), `good_at` (`bad(good, c, x) = 0` for every `c < P`);
* `height_candidate` (`lem:height`): with at most two forbidden candidates per pair and
  `2P + 1` candidates, a valid candidate exists.

Not derived: that a pair of distinct points forbids at most two candidates (a nonzero
polynomial of degree at most two has at most two roots among the candidates; for a fixed
number of candidates this is `Foundations/GenericDirection.some_nonroot`).
-/

namespace LeanProofs.IPRA.Foundations.FiniteAvoidance

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_none
  zero_of_compl_ne)
open LeanProofs.IPRA.Probability.Variance (sum_one)
open LeanProofs.IPRA.Signum (sg sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shift_pair (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

/-- `sg v = 0` gives `v = 0`. -/
theorem zero_of_sg {v : PTm n} (h : Γ ⊢[PRAAx] sg v ≐ zero) : Γ ⊢[PRAAx] v ≐ zero :=
  .orE (zero_or_succ v) Prf.hyp0 (Foundations.BoundedReflection.one_ne_zero _
    (((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans
      (sg_succ (pred v))).eqSymm.eqTrans h.wk))

variable (bad : PTm 3)

/-- The violation indicator `sg bad(t, c, x)`. -/
def aB : PTm 3 := sg bad

theorem inst3_aB (t c x : PTm n) : inst3 (aB bad) t c x = sg (inst3 bad t c x) := by
  simp [inst3, aB]

/-- The bit "candidate `t` violates none of the constraints below `fst y`". -/
def gB : PTm 2 := monus one (oB (aB bad))

theorem inst2_gB (t y : PTm n) :
    inst2 (gB bad) t y = monus one (inst2 (oB (aB bad)) t y) := by
  simp [inst2, gB]

/-- The number of candidates below `T` violating the constraint `c`. -/
abbrev colCount (T c x : PTm n) : PTm n := ap2 (sumF (colB (aB bad))) T (pairT c x)

/-- The number of constraints below `P` violated by the candidate `t`. -/
abbrev rowCount (P t x : PTm n) : PTm n := ap2 (sumF (rowB (aB bad))) P (pairT t x)

/-! ## The count -/

/-- If no candidate is good, every candidate contributes at least one violation. -/
theorem rows_ge {T P x : PTm n} (hz : Γ ⊢[PRAAx] exB (gB bad) T (pairT P x) ≐ zero) :
    Γ ⊢[PRAAx] le T (ap2 (sumF (oB (aB bad))) T (pairT P x)) := by
  refine le_congr (sum_one T zero) (.eqRefl _)
    (sum_le_params (one : PTm 2) (oB (aB bad)) zero (pairT P x) T (.allI (.impI ?_)))
  have e1 : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (zero : PTm n)) = one := by
    simp [inst2]
  rw [e1, shift_pair]
  have hz' : (Γ.map Fm.shift) ⊢[PRAAx]
      exB (gB bad) (Syn.shift T) (pairT (Syn.shift P) (Syn.shift x)) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using hz.shift
  have z := ex_none (gB bad) (hz'.wk (ψ := lt (var 0) (Syn.shift T)))
    (Prf.hyp0 (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift T)))
  rw [inst2_gB] at z
  exact z

/-- The violations counted by constraints. -/
theorem cols_le {T P L x : PTm n}
    (hcol : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift P) ⟶
      le (colCount bad (Syn.shift T) (var 0) (Syn.shift x)) (Syn.shift L))) :
    Γ ⊢[PRAAx] le (ap2 (sumF (pB (aB bad))) P (pairT T x)) (P * L) := by
  refine sum_le_const (pB (aB bad)) (.allI (.impI ?_))
  rw [shift_pair, inst2_pB]
  exact le_congr (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
    (.eqRefl _) (.impE hcol.allOpen.wk Prf.hyp0)

/-- If every constraint is violated by at most `L` candidates and `P · L < T`, some candidate
violates no constraint. -/
theorem exists_good {T P L x : PTm n}
    (hcol : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift P) ⟶
      le (colCount bad (Syn.shift T) (var 0) (Syn.shift x)) (Syn.shift L)))
    (hsmall : Γ ⊢[PRAAx] lt (P * L) T) :
    Γ ⊢[PRAAx] exB (gB bad) T (pairT P x) ≐ one := by
  refine .orE (ex_cases (gB bad) T (pairT P x)) ?_ Prf.hyp0
  exact not_succ_le_self _ _ (le_trans hsmall.wk (le_trans (rows_ge bad Prf.hyp0)
    (le_congr (fubini (aB bad) T P x).eqSymm (.eqRefl _) (cols_le bad hcol.wk))))

/-! ## The first good candidate -/

/-- The first candidate below `T` that violates no constraint below `P`. -/
abbrev good (T P x : PTm n) : PTm n := wit (gB bad) T (pairT P x)

theorem good_lt {T P x : PTm n} (h : Γ ⊢[PRAAx] exB (gB bad) T (pairT P x) ≐ one) :
    Γ ⊢[PRAAx] lt (good bad T P x) T :=
  Prf.andE₁ (ex_elim (gB bad) h)

/-- The good candidate violates no constraint: its row count is zero. -/
theorem good_row {T P x : PTm n} (h : Γ ⊢[PRAAx] exB (gB bad) T (pairT P x) ≐ one) :
    Γ ⊢[PRAAx] rowCount bad P (good bad T P x) x ≐ zero := by
  have ne := Prf.andE₂ (ex_elim (gB bad) h)
  rw [inst2_gB] at ne
  exact (oB_at (aB bad) _ _ _).eqSymm.eqTrans (zero_of_compl_ne ne)

/-- `bad(good, c, x) = 0` for every constraint `c < P`. -/
theorem good_at {T P x c : PTm n} (h : Γ ⊢[PRAAx] exB (gB bad) T (pairT P x) ≐ one)
    (hc : Γ ⊢[PRAAx] lt c P) : Γ ⊢[PRAAx] inst3 bad (good bad T P x) c x ≐ zero := by
  have z := sum_zero_elim (rowB (aB bad)) (good_row bad h) hc
  rw [inst2_rowB] at z
  have z' : Γ ⊢[PRAAx] inst3 (aB bad) (good bad T P x) c x ≐ zero :=
    (congrInst3 (aB bad) (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqSymm.eqTrans z
  rw [inst3_aB] at z'
  exact zero_of_sg z'

/-! ## The generic height -/

/-- `lem:height`: with `P` pairs, at most two forbidden candidates per pair and `2P + 1`
candidates, a candidate that is forbidden by no pair exists. -/
theorem height_candidate {P x : PTm n}
    (hcol : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift P) ⟶
      le (colCount bad (Syn.shift (succ (P * two))) (var 0) (Syn.shift x)) (Syn.shift two))) :
    Γ ⊢[PRAAx] exB (gB bad) (succ (P * two)) (pairT P x) ≐ one :=
  exists_good bad hcol (le_refl _)

end LeanProofs.IPRA.Foundations.FiniteAvoidance
