import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.LinearCombination

/-!
# Splitting a finite sum at a cut point

For a body `g(i, x)`: `∑_{i<M+K} g(i, x) = ∑_{i<M} g(i, x) + ∑_{i<K} g(M + i, x)`.

The second summand needs the offset `M` as well as `x`, so its body reads the parameter as a pair
`y = ⟨M, x⟩`: `offB g (i, y) = g(fst y + i, snd y)`.

* `sum_split`: the identity above, by induction on `K`;
* `sum_split₃`: the split at two cut points.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `g(fst y + i, snd y)`. -/
def offB (g : PTm 2) : PTm 2 := Syn.subst ![fstT (var 1) + var 0, sndT (var 1)] g

theorem inst2_offB (g : PTm 2) (i y : PTm n) :
    inst2 (offB g) i y = inst2 g (fstT y + i) (sndT y) := by
  simp only [inst2, offB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem split_base (g : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF g) (M + zero) x ≐ ap2 (sumF g) M x + ap2 (sumF (offB g)) zero (pairT M x) := by
  ipra_lc natEq (congrAp2 (sumF g) (add_zero (Γ := Γ) M) (.eqRefl x)) - natEq (sum_zero (Γ := Γ) (offB g) (pairT M x))

theorem split_step (g : PTm 2) {M K x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF g) (M + K) x ≐ ap2 (sumF g) M x + ap2 (sumF (offB g)) K (pairT M x)) :
    Γ ⊢[PRAAx] ap2 (sumF g) (M + succ K) x ≐
      ap2 (sumF g) M x + ap2 (sumF (offB g)) (succ K) (pairT M x) := by
  have c := natEq (congrAp2 (sumF g) (add_succ (Γ := Γ) M K) (.eqRefl x))
  have s := natEq (sum_succ' (Γ := Γ) g (M + K) x)
  have s' := sum_succ' (Γ := Γ) (offB g) K (pairT M x)
  rw [inst2_offB] at s'
  have a' := natEq s'
  have pt := natEq (congrInst2 g (congrAdd (fst_pair (Γ := Γ) M x) (.eqRefl K)) (snd_pair M x))
  have i := natEq ih
  apply deriveNat; ipra_simps
  linear_combination c + s + i - a' - pt

/-- Variables: `0 = K` (induction), `1 = M`, `2 = x`. -/
private abbrev splitF (g : PTm 2) : Fm PTm 3 :=
  ap2 (sumF g) (var 1 + var 0) (var 2) ≐
    ap2 (sumF g) (var 1) (var 2) + ap2 (sumF (offB g)) (var 0) (pairT (var 1) (var 2))

private theorem split₀ (g : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] splitF g := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact split_base g _ _
  · exact split_step g Prf.hyp0

/-- `∑_{i<M+K} g(i, x) = ∑_{i<M} g(i, x) + ∑_{i<K} g(M + i, x)`. -/
theorem sum_split (g : PTm 2) (M K x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF g) (M + K) x ≐ ap2 (sumF g) M x + ap2 (sumF (offB g)) K (pairT M x) := by
  have h := inst (Γ := Γ) (split₀ g) (![K, M, x] : Fin 3 → PTm n)
  simpa using h

/-- The split at two cut points:
`∑_{i<A+R+H} g = ∑_{i<A} g + ∑_{i<R} g(A + i) + ∑_{i<H} g(A + R + i)`. -/
theorem sum_split₃ (g : PTm 2) (A R H x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF g) (A + R + H) x ≐
      ap2 (sumF g) A x + ap2 (sumF (offB g)) R (pairT A x) + ap2 (sumF (offB g)) H (pairT (A + R) x) :=
  (sum_split g (A + R) H x).eqTrans (congrAdd (sum_split g A R x) (.eqRefl _))

end LeanProofs.IPRA
