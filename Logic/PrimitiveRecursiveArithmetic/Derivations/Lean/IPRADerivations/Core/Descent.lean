import IPRADerivations.Core.BoundedSums

/-!
# Infinite descent in iPRA

A generic form of Fermat's method of infinite descent, for a quantifier-free
property of pairs of natural numbers given by an indicator term `χ(a, b)`:

* `χ` takes the values `0` and `1` (`h01`), and `χ(a, 0) = 0` (`h0`);
* every solution satisfies a bound `a < β(b)` (`hb`);
* a solution with `b ≠ 0` yields a smaller one: terms `a', b'` with `χ(a', b') = 1`
  and `b' < b` (`hstep`).

Then `χ(a, b) = 1` is refutable (`descent`). The proof is an induction on `N` for
`T(N) = 0`, where `T(N) = ∑_{b<N} ∑_{a<β(b)} χ(a, b)` counts the solutions with
`b < N`; the sums act as bounded quantifiers (`Core.BoundedSums`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `β(b)`. -/
def inst1 (β : PTm 1) (b : PTm n) : PTm n := Syn.subst ![b] β

@[simp] theorem subst_inst1 {m : ℕ} (σ : Fin n → PTm m) (β : PTm 1) (b : PTm n) :
    Syn.subst σ (inst1 β b) = inst1 β (Syn.subst σ b) := by
  simp only [inst1, Syn.subst_subst, subst_vecCons, subst_vecEmpty]

namespace Descent

variable (χ : PTm 2) (β : PTm 1)

/-- `inner(M, b) = ∑_{a<M} χ(a, b)`. -/
abbrev innerF : PR 2 := sumF χ
/-- The outer body `inner(β(b), b)`; variables `0 = b`, `1` unused. -/
abbrev outerBody : PTm 2 := ap2 (innerF χ) (inst1 β (var 0)) (var 0)
abbrev outerF : PR 2 := sumF (outerBody χ β)
/-- `T(N)`. -/
abbrev T (N : PTm n) : PTm n := ap2 (outerF χ β) N zero

theorem inst2_outer (b x : PTm n) :
    inst2 (outerBody χ β) b x = ap2 (innerF χ) (inst1 β b) b := by
  simp only [inst2, outerBody, subst_ap2, subst_inst1, Syn.subst_var, Matrix.cons_val_zero]

/-- The hypotheses of the descent, over the variables `0 = a`, `1 = b`. -/
structure Hyps (a' b' : PTm 2) : Prop where
  h01 : ([] : List (Fm PTm 2)) ⊢[PRAAx] (inst2 χ (var 0) (var 1) ≐ zero) ⋎ (inst2 χ (var 0) (var 1) ≐ one)
  h0 : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst2 χ (var 0) zero ≐ zero
  hb : ([inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx] lt (var 0) (inst1 β (var 1))
  hstep : ([var 1 ≐ succ (pred (var 1)), inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
    (inst2 χ a' b' ≐ one) ⋏ lt b' (var 1)

variable {χ β} {a' b' : PTm 2}

/-- A derivation over the two variables, used under hypotheses `Δ` that derive its context. -/
private theorem use {Θ Δ : List (Fm PTm 2)} {φ : Fm PTm 2} (h : Θ ⊢[PRAAx] φ)
    (s : ∀ ψ ∈ Θ, Δ ⊢[PRAAx] ψ) : Δ ⊢[PRAAx] φ := h.trans s

/-- The bound applied to an arbitrary pair of terms. -/
private theorem bound (H : Hyps χ β a' b') {Δ : List (Fm PTm 2)} {a b : PTm 2}
    (h : Δ ⊢[PRAAx] inst2 χ a b ≐ one) : Δ ⊢[PRAAx] lt a (inst1 β b) := by
  have i := inst (Γ := Δ) (.impI H.hb) ![a, b]
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst1, subst_inst2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at i
  exact .impE i h

/-- A zero count below `N` rules out a solution whose second coordinate is below `N`. -/
theorem no_solution_below {a b N : PTm n}
    (hT : Γ ⊢[PRAAx] T χ β N ≐ zero) (hlt : Γ ⊢[PRAAx] lt b N)
    (ha : Γ ⊢[PRAAx] inst2 χ a b ≐ one) (hb : Γ ⊢[PRAAx] lt a (inst1 β b)) :
    Γ ⊢[PRAAx] Fm.bot := by
  have hinner := sum_zero_elim (outerBody χ β) hT hlt
  rw [inst2_outer] at hinner
  exact succ_ne_zero (a := zero) (ha.eqSymm.eqTrans (sum_zero_elim χ hinner hb))

/-- If a zero count at `b` makes every term in row `b` vanish, all counts are zero. -/
theorem count_zero_of_term_zero
    (hzero : ([T χ β (var 1) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx] inst2 χ (var 0) (var 1) ≐ zero) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] T χ β (var 0) ≐ zero := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' (outerBody χ β) (var 0) zero).eqTrans ?_
    rw [inst2_outer]
    refine (congrAdd Prf.hyp0 ?_).eqTrans (add_zero _)
    refine sum_zero_of_all χ (var 0) (.allI ?_) _
    simpa [Fm.shift, Syn.shift] using hzero

/-- In the context `T(b) = 0`: `χ(a, b) = 0`. -/
private theorem term_zero (H : Hyps χ β a' b') :
    ([T χ β (var 1) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx] inst2 χ (var 0) (var 1) ≐ zero := by
  refine .orE (H.h01.ofNil) Prf.hyp0 ?_
  refine .orE (zero_or_succ (var 1)) ?_ ?_
  · -- b = 0: χ(a, 0) = 0, contradicting χ(a, b) = 1.
    refine .botE _ (succ_ne_zero (a := zero) ?_)
    refine Prf.hyp1.eqSymm.eqTrans ?_
    exact (congrInst2 χ (.eqRefl _) Prf.hyp0).eqTrans H.h0.ofNil
  · refine .botE _ ?_
    have hs := use H.hstep (Δ := [var 1 ≐ succ (pred (var 1)), inst2 χ (var 0) (var 1) ≐ one,
      T χ β (var 1) ≐ zero]) (by
        intro ψ hψ; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hψ
        rcases hψ with rfl | rfl
        · exact Prf.hyp0
        · exact Prf.hyp1)
    exact no_solution_below hyp2 hs.andE₂ hs.andE₁ (bound H hs.andE₁)

/-- `T(N) = 0` for every `N`. -/
theorem count_zero (H : Hyps χ β a' b') : ([] : List (Fm PTm 1)) ⊢[PRAAx] T χ β (var 0) ≐ zero :=
  count_zero_of_term_zero (term_zero H)

/-- Infinite descent: `χ(a, b) = 1` is refutable. -/
theorem descent (H : Hyps χ β a' b') :
    ([inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx] Fm.bot := by
  have hT : ([inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
      T χ β (succ (var 1)) ≐ zero := by
    simpa using inst (Γ := [inst2 χ (var 0) (var 1) ≐ one]) (count_zero H)
      (![succ (var 1)] : Fin 1 → PTm 2)
  exact no_solution_below hT ((succ_monus_succ _ _).eqTrans (le_refl _)) Prf.hyp0 H.hb

end Descent

end LeanProofs.IPRA
