import IPRADerivations.Core.BoundedSums

/-!
# Manipulating finite sums

For bodies `f(i, x)`, with `S_f(M, x) = ∑_{i<M} f(i, x)`:

* `sum_shift`: `S_f(M + 1, x) = f(0, x) + ∑_{i<M} f(i + 1, x)`;
* `sum_add`: `∑ (f + g) = ∑ f + ∑ g`;
* `sum_congr_bounded`: sums agree when the bodies agree below the bound;
* `term_le_sum`: `i < M → f(i, x) ≤ S_f(M, x)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The body `f(i + 1, x)`. -/
def shiftBody (f : PTm 2) : PTm 2 := Syn.subst ![succ (var 0), var 1] f

theorem inst2_shiftBody (f : PTm 2) (i x : PTm n) : inst2 (shiftBody f) i x = inst2 f (succ i) x := by
  simp only [inst2, shiftBody, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- `f + g` as a body. -/
def addBody (f g : PTm 2) : PTm 2 := f + g

theorem inst2_addBody (f g : PTm 2) (i x : PTm n) :
    inst2 (addBody f g) i x = inst2 f i x + inst2 g i x := by
  simp [inst2, addBody]

/-- Variables: `0 = M`, `1 = x`. -/
private abbrev shiftF (f : PTm 2) : Fm PTm 2 :=
  ap2 (sumF f) (succ (var 0)) (var 1) ≐ inst2 f zero (var 1) + ap2 (sumF (shiftBody f)) (var 0) (var 1)

private theorem sum_shift₀ (f : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] shiftF f := by
  ipra_ind [subst_ap2, subst_inst2]
  · exact (sum_singleton f (var 0)).eqTrans
      ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) (sum_zero _ _).eqSymm))
  · refine (sum_succ' f (succ (var 0)) (var 1)).eqTrans ?_
    refine (congrAdd Prf.hyp0 (.eqRefl _)).eqTrans ?_
    refine (add_assoc _ _ _).eqTrans (congrAdd (.eqRefl _) ?_)
    refine .eqTrans ?_ (sum_succ' (shiftBody f) (var 0) (var 1)).eqSymm
    rw [inst2_shiftBody]
    exact .eqRefl _

theorem sum_shift (f : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF f) (succ M) x ≐ inst2 f zero x + ap2 (sumF (shiftBody f)) M x := by
  have h := inst (Γ := Γ) (sum_shift₀ f) (![M, x] : Fin 2 → PTm n)
  simpa using h

/-- Variables: `0 = M`, `1 = x`. -/
private abbrev addF (f g : PTm 2) : Fm PTm 2 :=
  ap2 (sumF (addBody f g)) (var 0) (var 1) ≐ ap2 (sumF f) (var 0) (var 1) + ap2 (sumF g) (var 0) (var 1)

private theorem sum_add₀ (f g : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] addF f g := by
  ipra_ind [subst_ap2]
  · exact (sum_zero _ _).eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (sum_zero _ _) (sum_zero _ _)).eqSymm)
  · refine (sum_succ' _ (var 0) (var 1)).eqTrans ?_
    rw [inst2_addBody]
    refine withEq Prf.hyp0 fun e₁ => withEq (sum_succ' f (var 0) (var 1)) fun e₂ =>
      withEq (sum_succ' g (var 0) (var 1)) fun e₃ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₃]; ring

theorem sum_add (f g : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (addBody f g)) M x ≐ ap2 (sumF f) M x + ap2 (sumF g) M x := by
  have h := inst (Γ := Γ) (sum_add₀ f g) (![M, x] : Fin 2 → PTm n)
  simpa using h

/-- Sums agree when the bodies agree below the bound (with possibly different parameters). -/
theorem sum_congr_bounded (f g : PTm 2) (x y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 f (var 0) (Syn.shift x) ≐ inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF g) N y := by
  let P : Fm PTm (n + 1) :=
    ap2 (sumF f) (var 0) (Syn.shift x) ≐ ap2 (sumF g) (var 0) (Syn.shift y)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · simpa [P] using (sum_zero (Γ := Γ) f x).eqTrans (sum_zero g y).eqSymm
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ((sum_succ' f (var 0) _).eqTrans (.eqTrans ?_ (sum_succ' g (var 0) _).eqSymm))
      exact congrAdd Prf.hyp1 (.impE h.allOpen.wk.wk Prf.hyp0)
  simpa [P] using atBound

theorem term_le_sum (f : PTm 2) {i M x : PTm n} (h : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] le (inst2 f i x) (ap2 (sumF f) M x) :=
  sum_term_le f h

end LeanProofs.IPRA
