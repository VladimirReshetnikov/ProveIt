import IPRADerivations.Foundations.HurwitzProduct
import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.CommonLemmas

/-!
# Uniqueness for triangular recurrences (`ipra_coherent_methods_2026-11-15`, `thm:hurwitz-ode`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, Theorem `thm:hurwitz-ode`, the
uniqueness clause: "If its coefficients agree through `n`, finite evaluation of `G` agrees at
coefficient `n`, so (9) forces agreement at `n + 1`. Bounded-prefix induction proves equality
of the whole requested prefix."

Two sequences `y(n, x)`, `y'(n, x)` (terms; variables `0 = n`, `1 = x`) satisfy triangular
recurrences `y(n + 1) = F(n)`, `y'(n + 1) = F'(n)` with the same initial value
(`Triangular`), where triangularity is the supplied rule

`(∀ j ≤ n. y(j) = y'(j))` gives `F(n) = F'(n)`

(the premise is the object-level bounded statement `agree y y' (n + 1) x`). Then

* `unique`: `y(n, x) = y'(n, x)` for every `n`; closed form `unique_closed`.

The induction is on the quantifier-free bit of the bounded prefix,
`allB [y(j) = y'(j)] (n + 1) = 1` (`Foundations/BoundedReflection`); the bounded universal
statement needed by the triangularity rule is recovered from the bit by reflection.

* `hurwitz_linear_unique`: uniqueness of the solution of the linear Hurwitz system
  `Y' = A ⋆ Y`, the packet's (10): if `y(0) = y'(0)`, `y(n + 1) = (A ⋆ y)_n` and
  `y'(n + 1) = (A ⋆ y')_n`, then `y = y'`. Triangularity holds because `(A ⋆ y)_n` reads `y`
  only at indices `n ∸ j ≤ n` (`hw_congr`).

Not derived: existence of the prefix for a general polynomial system `G(T, Y)` (it needs an
evaluator of coded polynomial expressions over the Hurwitz algebra) and compatibility under
shortening of the coefficient input.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TriangularUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection
  (allB allB_zero allB_succ all_elim all_reflect)
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open LeanProofs.IPRA.Foundations.HurwitzProduct
open LeanProofs.IPRA.Combinatorics.BinomialTransform (bgB)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem up_shift {m j : ℕ} (σ : Fin m → PTm j) (t : PTm m) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

/-! ## Agreement of two sequences on a prefix -/

section Agree

variable (y y' : PTm 2)

/-- The bit `[y(j, x) = y'(j, x)]`. -/
def eB : PTm 2 := eqb y y'

theorem inst2_eB (j x : PTm k) : inst2 (eB y y') j x = eqb (inst2 y j x) (inst2 y' j x) := by
  simp [inst2, eB]

/-- `∀ j < N. y(j, x) = y'(j, x)`. -/
def agree (N x : PTm k) : Fm PTm k :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    (inst2 y (var 0) (Syn.shift x) ≐ inst2 y' (var 0) (Syn.shift x)))

@[simp] theorem subst_agree {m : ℕ} (σ : Fin k → PTm m) (N x : PTm k) :
    (agree y y' N x).subst σ = agree y y' (Syn.subst σ N) (Syn.subst σ x) := by
  simp only [agree, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst2,
    Syn.subst_var, Syn.up_zero, up_shift]

theorem shift_agree (N x : PTm k) :
    Fm.shift (agree y y' N x) = agree y y' (Syn.shift N) (Syn.shift x) := by
  simp [Fm.shift, Syn.shift]

/-- Instantiating the agreement at an index below the bound. -/
theorem agree_elim {N x j : PTm k} (h : Γ ⊢[PRAAx] agree y y' N x) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] inst2 y j x ≐ inst2 y' j x := by
  have e := Prf.allE j h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at e
  exact .impE e hj

/-- The agreement on a prefix from its bit. -/
theorem agree_of_bit {N x : PTm k} (h : Γ ⊢[PRAAx] allB (eB y y') N x ≐ one) :
    Γ ⊢[PRAAx] agree y y' N x := by
  have r := all_reflect (eB y y') h
  refine .allI (.impI ?_)
  have o := Prf.impE (r.allOpen.wk (ψ := lt (var 0) (Syn.shift N))) Prf.hyp0
  rw [inst2_eB] at o
  exact eq_of_eqb_ne o

end Agree

/-! ## Triangular recurrences -/

/-- Two sequences with the same initial value satisfying triangular recurrences. -/
structure Triangular (y y' F F' : PTm 2) : Prop where
  init : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k),
    Γ ⊢[PRAAx] inst2 y zero x ≐ inst2 y' zero x
  step : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (n x : PTm k),
    Γ ⊢[PRAAx] inst2 y (succ n) x ≐ inst2 F n x
  step' : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (n x : PTm k),
    Γ ⊢[PRAAx] inst2 y' (succ n) x ≐ inst2 F' n x
  tri : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {n x : PTm k},
    (Γ ⊢[PRAAx] agree y y' (succ n) x) → (Γ ⊢[PRAAx] inst2 F n x ≐ inst2 F' n x)

section Unique

variable {y y' F F' : PTm 2}

theorem bit_of_eq {j x : PTm k} (h : Γ ⊢[PRAAx] inst2 y j x ≐ inst2 y' j x) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.Signum.sg (inst2 (eB y y') j x) ≐ one := by
  rw [inst2_eB]
  exact sg_of_pos (c := zero) (eqb_of_eq h)

theorem bit_zero (T : Triangular y y' F F') (x : PTm k) :
    Γ ⊢[PRAAx] allB (eB y y') (succ zero) x ≐ one :=
  (allB_succ (eB y y') zero x).eqTrans
    ((congrMul (allB_zero (eB y y') x) (bit_of_eq (T.init x))).eqTrans (one_mul _))

theorem bit_step (T : Triangular y y' F F') {n x : PTm k}
    (ih : Γ ⊢[PRAAx] allB (eB y y') (succ n) x ≐ one) :
    Γ ⊢[PRAAx] allB (eB y y') (succ (succ n)) x ≐ one := by
  have e : Γ ⊢[PRAAx] inst2 y (succ n) x ≐ inst2 y' (succ n) x :=
    (T.step n x).eqTrans ((T.tri (agree_of_bit y y' ih)).eqTrans (T.step' n x).eqSymm)
  exact (allB_succ (eB y y') (succ n) x).eqTrans
    ((congrMul ih (bit_of_eq e)).eqTrans (one_mul _))

/-- Variables: `0 = n`, `1 = x`. -/
private def bitF (y y' : PTm 2) : Fm PTm 2 :=
  allB (eB y y') (succ (var 0)) (var 1) ≐ one

private theorem bit₀ (T : Triangular y y' F F') : ([] : List (Fm PTm 2)) ⊢[PRAAx] bitF y y' := by
  refine ind _ trivial ?_ ?_
  · simp only [bitF, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact bit_zero T _
  · simp only [bitF, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [bitF y y'] ⊢[PRAAx] allB (eB y y') (succ (var 0)) (var 1) ≐ one := Prf.hyp0
    exact bit_step T ih

/-- The uniqueness clause of `thm:hurwitz-ode` for an arbitrary triangular recurrence. -/
theorem unique (T : Triangular y y' F F') (n x : PTm k) :
    Γ ⊢[PRAAx] inst2 y n x ≐ inst2 y' n x := by
  have i := inst (Γ := Γ) (bit₀ T) (![n, x] : Fin 2 → PTm k)
  simp [bitF] at i
  have ne := all_elim (eB y y') i (le_refl (succ n))
  rw [inst2_eB] at ne
  exact eq_of_eqb_ne ne

/-- Uniqueness as a closed sentence. Variables: `0 = n`, `1 = x`. -/
theorem unique_closed (T : Triangular y y' F F') :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (inst2 y (var 0) (var 1) ≐ inst2 y' (var 0) (var 1)) :=
  closeUniv 2 (unique T _ _)

end Unique

/-! ## The linear Hurwitz system `Y' = A ⋆ Y` -/

section Linear

variable (A y y' : PTm 2)

/-- `h ∸ j ≤ h`. -/
alias monus_le' := Common.monus_le_self

/-- The summands of `(A ⋆ y)_n` and `(A ⋆ y')_n` agree when `y`, `y'` agree up to `n`. -/
theorem lin_pt {j n x : PTm k} (h : Γ ⊢[PRAAx] agree y y' (succ n) x) :
    Γ ⊢[PRAAx] inst2 (bgB (cv A y)) j (pairT n (pairT n x)) ≐
      inst2 (bgB (cv A y')) j (pairT n (pairT n x)) := by
  have hl : Γ ⊢[PRAAx] lt (monus n j) (succ n) :=
    (succ_monus_succ (monus n j) n).eqTrans (monus_le' n j)
  have e := agree_elim y y' h hl
  refine (term_at A y j n n x).eqTrans (.eqTrans ?_ (term_at A y' j n n x).eqSymm)
  exact congrMul (.eqRefl _) (congrMul (.eqRefl _) e)

/-- `(A ⋆ y)_n` reads `y` only up to index `n`. -/
theorem hw_congr {n x : PTm k} (h : Γ ⊢[PRAAx] agree y y' (succ n) x) :
    Γ ⊢[PRAAx] hw A y n x ≐ hw A y' n x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT]
  have h' := h.shift
  rw [shift_agree] at h'
  have e : Syn.shift (succ n) = succ (Syn.shift n) := by simp [Syn.shift]
  rw [e] at h'
  exact lin_pt A y y' h'.wk

/-- `(A ⋆ y)_n` as a term in `n` and `x`. -/
def hwB : PTm 2 := hw A y (var 0) (var 1)

theorem inst2_hwB (n x : PTm k) : inst2 (hwB A y) n x = hw A y n x := by
  simp [inst2, hwB]

variable {A y y'}

/-- Uniqueness of the solution of `Y' = A ⋆ Y` with a given initial value. -/
theorem hurwitz_linear_unique
    (h₀ : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k),
      Γ ⊢[PRAAx] inst2 y zero x ≐ inst2 y' zero x)
    (hy : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (n x : PTm k),
      Γ ⊢[PRAAx] inst2 y (succ n) x ≐ hw A y n x)
    (hy' : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (n x : PTm k),
      Γ ⊢[PRAAx] inst2 y' (succ n) x ≐ hw A y' n x)
    (n x : PTm k) : Γ ⊢[PRAAx] inst2 y n x ≐ inst2 y' n x :=
  unique (F := hwB A y) (F' := hwB A y')
    { init := h₀
      step := fun n x => by rw [inst2_hwB]; exact hy n x
      step' := fun n x => by rw [inst2_hwB]; exact hy' n x
      tri := fun h => by rw [inst2_hwB, inst2_hwB]; exact hw_congr A y y' h } n x

end Linear

end LeanProofs.IPRA.Foundations.TriangularUniqueness
