import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination

/-!
# Tail sums, inclusion–exclusion and total expectation

Packet: `probability/expected_value_ipra_2026-11-16`, Sections 5 and 7 (`thm:tail-sum`,
`thm:indicator`, `thm:total-expectation`), for a weight body `w(i, x)` on outcomes `i < M`.

* `tail_pt`: `x = ∑_{k<B} [x > k]` for `x ≤ B`, by induction on `B` with the two-sided invariant
  "the sum is `x` if `x ≤ B`, and `B` if `B ≤ x`";
* `tail_sum` (`thm:tail-sum`): if `X_i ≤ B` on the outcomes, then
  `∑_{i<M} w_i X_i = ∑_{k<B} ∑_{i<M} w_i [X_i > k]`, by exchanging the two sums
  (`tail_col_pt` reads off the summand of the tail weight);
* `incl_excl` (`thm:indicator`): for an indicator `A ≤ 1`,
  `Ew(A ∨ B) + Ew(A B) = Ew(A) + Ew(B)` with `A ∨ B = A + (1 ∸ A) B`;
* `union_bound₂`: `Ew(A ∨ B) ≤ Ew(A) + Ew(B)`;
* `total_expectation` (`thm:total-expectation`): for a partition map `c(i) < R` with cell sums
  `S_j = ∑_{i<M} w_i X_i [c(i) = j]`, `∑_{j<R} S_j = ∑_{i<M} w_i X_i`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.TailSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add' geI geI_true geI_false exp_add)
open LeanProofs.IPRA.Probability.Lotus (pvB pushforward_total)
open LeanProofs.IPRA.Probability.Independence (shift_inst2 row_pt col_pt sum_scale dsum dsum_rows)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The pointwise tail sum -/

/-- `[x > k]`, with `k` the summation index and `x` the parameter. -/
def gtB : PTm 2 := monus one (monus (succ (var 0)) (var 1))

theorem inst2_gtB (k x : PTm n) : inst2 gtB k x = geI (succ k) x := by simp [inst2, gtB]

/-- `T(B) = ∑_{k<B} [x > k]`. -/
abbrev tS (B x : PTm n) : PTm n := ap2 (sumF gtB) B x

theorem tS_succ (B x : PTm n) : Γ ⊢[PRAAx] tS (succ B) x ≐ tS B x + geI (succ B) x := by
  have e := sum_succ' (Γ := Γ) gtB B x
  rw [inst2_gtB] at e
  exact e

section TailStep

variable {B x : PTm n}

theorem tstep_le (ihA : Γ ⊢[PRAAx] le x B ⟶ (tS B x ≐ x)) (h : Γ ⊢[PRAAx] le x B) :
    Γ ⊢[PRAAx] tS (succ B) x ≐ x :=
  (tS_succ B x).eqTrans ((congrAdd (Prf.impE ihA h)
    (geI_false ((succ_monus_succ x B).eqTrans h))).eqTrans (add_zero _))

theorem tstep_eq (ihB : Γ ⊢[PRAAx] le B x ⟶ (tS B x ≐ B)) (h : Γ ⊢[PRAAx] x ≐ succ B) :
    Γ ⊢[PRAAx] tS (succ B) x ≐ x :=
  (tS_succ B x).eqTrans ((congrAdd (Prf.impE ihB (le_congr (.eqRefl _) h.eqSymm (le_succ_self B)))
    (geI_true (le_congr (.eqRefl _) h.eqSymm (le_refl (succ B))))).eqTrans
    ((succ_eq_add_one B).eqSymm.eqTrans h.eqSymm))

theorem tstep_ge (ihB : Γ ⊢[PRAAx] le B x ⟶ (tS B x ≐ B)) (h : Γ ⊢[PRAAx] le (succ B) x) :
    Γ ⊢[PRAAx] tS (succ B) x ≐ succ B :=
  (tS_succ B x).eqTrans ((congrAdd (Prf.impE ihB (le_trans (le_succ_self B) h)) (geI_true h)).eqTrans
    (succ_eq_add_one B).eqSymm)

theorem tstep (ihA : Γ ⊢[PRAAx] le x B ⟶ (tS B x ≐ x)) (ihB : Γ ⊢[PRAAx] le B x ⟶ (tS B x ≐ B)) :
    Γ ⊢[PRAAx] (le x (succ B) ⟶ (tS (succ B) x ≐ x)) ⋏ (le (succ B) x ⟶ (tS (succ B) x ≐ succ B)) :=
  .andI (.impI (.orE (lt_or_eq_of_le Prf.hyp0)
      (tstep_le ihA.wk.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)) (tstep_eq ihB.wk.wk Prf.hyp0)))
    (.impI (tstep_ge ihB.wk Prf.hyp0))

end TailStep

/-- Variables: `0 = B`, `1 = x`. -/
private abbrev tlF : Fm PTm 2 :=
  (le (var 1) (var 0) ⟶ (tS (var 0) (var 1) ≐ var 1)) ⋏ (le (var 0) (var 1) ⟶ (tS (var 0) (var 1) ≐ var 0))

private theorem tl₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] tlF := by
  refine ind _ ⟨⟨le_QF _ _, trivial⟩, ⟨le_QF _ _, trivial⟩⟩ ?_ ?_
  · simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .andI (.impI ((sum_zero _ _).eqTrans ((monus_zero _).eqSymm.eqTrans Prf.hyp0).eqSymm))
      (.impI (sum_zero _ _))
  · simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tstep (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)

/-- `∑_{k<B} [x > k] = x` for `x ≤ B`. -/
theorem tail_pt {B x : PTm n} (h : Γ ⊢[PRAAx] le x B) : Γ ⊢[PRAAx] ap2 (sumF gtB) B x ≐ x := by
  have i := inst (Γ := Γ) tl₀ (![B, x] : Fin 2 → PTm n)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at i
  exact Prf.impE (Prf.andE₁ i) h

/-! ## The tail-sum formula for an expectation -/

section Tail

variable (w X : PTm 2)

/-- `a(i, k, x) = w(i, x) · [X(i, x) > k]`. -/
def tlA : PTm 3 :=
  Syn.subst ![var 0, var 2] w * monus one (monus (succ (var 1)) (Syn.subst ![var 0, var 2] X))

theorem inst3_tlA (i k x : PTm n) :
    inst3 (tlA w X) i k x = inst2 w i x * geI (succ k) (inst2 X i x) := by
  simp only [inst3, tlA, inst2, geI, PTm.subst_mul, PTm.subst_monus, Syn.subst_subst, Syn.subst_var,
    ConciseIPRA.PTm.subst_succ]
  congr 1
  · congr 1; funext j; fin_cases j <;> rfl
  · congr 1
    · simp
    · congr 1; congr 1; funext j; fin_cases j <;> rfl

/-- The row sum: `∑_{k<B} w_i [X_i > k] = w_i X_i` when `X_i ≤ B`. -/
theorem tail_row {i B x : PTm n} (h : Γ ⊢[PRAAx] le (inst2 X i x) B) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (tlA w X))) B (pairT i x) ≐ inst2 w i x * inst2 X i x := by
  refine (sum_scale (rowB (tlA w X)) gtB B (inst2 w i x) (inst2 X i x) (pairT i x)
    (.allI (.impI ?_))).eqTrans (congrMul (.eqRefl _) (tail_pt h))
  rw [shift_pairT, shift_inst2, shift_inst2, inst2_gtB]
  refine (row_pt _ _ _ _).eqTrans ?_
  rw [inst3_tlA]
  exact .eqRefl _

/-- The summand of the tail weight `∑_{i<M} w_i [X_i > k]`. -/
theorem tail_col_pt (i k x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (tlA w X)) i (pairT k x) ≐ inst2 w i x * geI (succ k) (inst2 X i x) := by
  refine (col_pt _ _ _ _).eqTrans ?_
  rw [inst3_tlA]
  exact .eqRefl _

/-- `thm:tail-sum`: if `X_i ≤ B` for `i < M`, then
`∑_{i<M} w_i X_i = ∑_{k<B} ∑_{i<M} w_i [X_i > k]`. -/
theorem tail_sum {M B x : PTm n}
    (hB : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ le (inst2 X (var 0) (Syn.shift x)) (Syn.shift B))) :
    Γ ⊢[PRAAx] Ew w X M x ≐ ap2 (sumF (pB (tlA w X))) B (pairT M x) := by
  have e : Γ ⊢[PRAAx] dsum (tlA w X) M B x ≐ ap2 (sumF (w * X)) M x := by
    refine dsum_rows (tlA w X) (w * X) M B x x (.allI (.impI ?_))
    rw [inst2_mul']
    exact tail_row w X (Prf.impE hB.allOpen.wk Prf.hyp0)
  exact e.eqSymm.eqTrans (fubini (tlA w X) M B x)

end Tail

/-! ## Inclusion–exclusion -/

/-- The union indicator `A ∨ B = A + (1 ∸ A) · B`. -/
def orB (A B : PTm 2) : PTm 2 := A + monus one A * B

theorem inst2_orB (A B : PTm 2) (i x : PTm n) :
    inst2 (orB A B) i x = inst2 A i x + monus one (inst2 A i x) * inst2 B i x := by
  simp [inst2, orB]

theorem or_pt {a b : PTm n} (h : Γ ⊢[PRAAx] le a one) :
    Γ ⊢[PRAAx] (a + monus one a * b) + a * b ≐ a + b := by
  ipra_lc (-(Groth.ι (IPRA.Q.mk Γ b))) * natEq (eq_add_of_le h)

/-- `thm:indicator`: `Ew(A ∨ B) + Ew(A B) = Ew(A) + Ew(B)` for an indicator `A ≤ 1`. -/
theorem incl_excl (w A B : PTm 2) (N x : PTm n)
    (hA : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 A (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] Ew w (orB A B) N x + Ew w (A * B) N x ≐ Ew w A N x + Ew w B N x := by
  refine (exp_add w (orB A B) (A * B) N x).eqSymm.eqTrans (.eqTrans ?_ (exp_add w A B N x))
  refine sum_congr_bounded (w * (orB A B + A * B)) (w * (A + B)) x x N (.allI (.impI ?_))
  rw [inst2_mul', inst2_mul', inst2_add', inst2_add', inst2_mul', inst2_orB]
  exact congrMul (.eqRefl _) (or_pt (Prf.impE hA.allOpen.wk Prf.hyp0))

/-- The union bound for two events: `Ew(A ∨ B) ≤ Ew(A) + Ew(B)`. -/
theorem union_bound₂ (w A B : PTm 2) (N x : PTm n)
    (hA : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 A (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] le (Ew w (orB A B) N x) (Ew w A N x + Ew w B N x) :=
  le_of_eq_add (incl_excl w A B N x hA).eqSymm

/-! ## Total expectation -/

/-- `thm:total-expectation`: for a partition map `c(i) < R`, the cell sums
`S_j = ∑_{i<M} w_i X_i [c(i) = j]` add up to `∑_{i<M} w_i X_i`. -/
theorem total_expectation (w X c : PTm 2) {R x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll c R x)
    (M : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (pvB (w * X) c)) R (pairT M x) ≐ Ew w X M x :=
  pushforward_total (w * X) c hr M

end LeanProofs.IPRA.Probability.TailSum
