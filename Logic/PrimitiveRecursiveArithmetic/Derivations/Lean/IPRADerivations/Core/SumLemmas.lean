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

namespace GeometricSum

/-- The cleared geometric-sum identity for a summand that equals `b^i` below the bound. -/
theorem sum_eq_pow (f : PTm 2) (N x : PTm n) {a b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ a + one)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 f (var 0) (Syn.shift x) ≐ pw (Syn.shift b) (var 0)))) :
    Γ ⊢[PRAAx] a * ap2 (sumF f) N x + one ≐ pw b N := by
  let P : Fm PTm (n + 1) :=
    Syn.shift a * ap2 (sumF f) (var 0) (Syn.shift x) + one ≐ pw (Syn.shift b) (var 0)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · have base : Γ ⊢[PRAAx] a * ap2 (sumF f) zero x + one ≐ pw b zero :=
        (congrAdd ((congrMul (.eqRefl _) (sum_zero f x)).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans
          ((zero_add one).eqTrans (pw_zero b).eqSymm)
      simpa [P] using base
    · simp only [P, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift N) :: P :: Γ.map Fm.shift
      have point := Prf.impE h.allOpen.wk.wk (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N))
      have sumStep := (sum_succ' (Γ := Δ) f (var 0) (Syn.shift x)).eqTrans (congrAdd (.eqRefl _) point)
      have powStep := pw_succ (Γ := Δ) (Syn.shift b) (var 0)
      have baseEq : Γ.map Fm.shift ⊢[PRAAx] Syn.shift b ≐ Syn.shift a + one := by
        simpa [Syn.shift] using Order.shift_eq hb
      have previous : Δ ⊢[PRAAx] P := Prf.hyp1
      refine withEq sumStep fun s => withEq powStep fun p =>
        withEq previous.eqSymm fun ih => withEq baseEq.wk.wk fun e => ?_
      apply deriveNat
      ipra_simps
      rw [s, p, ih, e]
      ring
  simpa [P] using atBound

end GeometricSum

end LeanProofs.IPRA
