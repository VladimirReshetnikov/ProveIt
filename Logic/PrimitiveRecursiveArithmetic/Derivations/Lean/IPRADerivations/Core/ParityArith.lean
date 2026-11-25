import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.Tactic
import IPRADerivations.Core.LinearCombination

/-!
# Arithmetic of parities

`par x` is the parity bit of `x` (`Core/Parity`). Addition modulo two is the exclusive or of
bits, so these lemmas are the calculus of xor-sums:

* `even_of`, `odd_of`: `par m = 0` gives `m = 2 · half m`, `par m = 1` gives `m = 2 · half m + 1`;
* `par_add_two`: `par (X + 2Y) = par X`;
* `par_add_even`: `par (X + T) = par X` when `T` is even;
* `par_add`: `par (x + y) = par (par x + par y)`;
* `par_par_add₃`: `par (par A + par B + par C) = par (A + B + C)`;
* `par_self_add`: `par (x + x) = 0`;
* `par_eq_of_add_even`: `par (A + B) = 0` gives `par A = par B`;
* `par_replacement`: `P₁ + T = P₂ + 2C` with `T` even gives `par P₁ = par P₂`;
* `sum_even_bounded`: a bounded sum of even terms is even.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem even_of {m : PTm n} (h : Γ ⊢[PRAAx] par m ≐ zero) : Γ ⊢[PRAAx] m ≐ two * half m :=
  (half_par m).eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_zero _))

theorem odd_of {m : PTm n} (h : Γ ⊢[PRAAx] par m ≐ one) : Γ ⊢[PRAAx] m ≐ two * half m + one :=
  (half_par m).eqTrans (congrAdd (.eqRefl _) h)

/-- `par (X + 2Y) = par X`. -/
theorem par_add_two (X Y : PTm n) : Γ ⊢[PRAAx] par (X + two * Y) ≐ par X := by
  refine .orE (par_cases X) ?_ ?_
  · have e : ((par X ≐ zero) :: Γ) ⊢[PRAAx] X + two * Y ≐ two * (half X + Y) := by
      have e₁ := natEq (even_of (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := par X ≐ zero)))
      apply deriveNat; ipra_simps
      linear_combination e₁
    exact ((congrAp1 parF e).eqTrans (par_double _)).eqTrans Prf.hyp0.eqSymm
  · have e : ((par X ≐ one) :: Γ) ⊢[PRAAx] X + two * Y ≐ two * (half X + Y) + one := by
      have e₁ := natEq (odd_of (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := par X ≐ one)))
      apply deriveNat; ipra_simps
      linear_combination e₁
    exact ((congrAp1 parF e).eqTrans (par_double_succ _)).eqTrans Prf.hyp0.eqSymm

/-- Adding an even number does not change the parity. -/
theorem par_add_even (X : PTm n) {T : PTm n} (hT : Γ ⊢[PRAAx] par T ≐ zero) :
    Γ ⊢[PRAAx] par (X + T) ≐ par X :=
  (congrAp1 parF (congrAdd (.eqRefl X) (even_of hT))).eqTrans (par_add_two X (half T))

/-- The parity of a sum is the exclusive or of the parities. -/
theorem par_add (x y : PTm n) : Γ ⊢[PRAAx] par (x + y) ≐ par (par x + par y) := by
  have e : Γ ⊢[PRAAx] x + y ≐ (par x + par y) + two * (half x + half y) := by
    ipra_lc natEq (half_par (Γ := Γ) x) + natEq (half_par (Γ := Γ) y)
  exact (congrAp1 parF e).eqTrans (par_add_two _ _)

theorem par_par_add₃ (A B C : PTm n) :
    Γ ⊢[PRAAx] par (par A + par B + par C) ≐ par (A + B + C) := by
  have e : Γ ⊢[PRAAx] A + B + C ≐ (par A + par B + par C) + two * (half A + half B + half C) := by
    ipra_lc natEq (half_par (Γ := Γ) A) + natEq (half_par (Γ := Γ) B) + natEq (half_par (Γ := Γ) C)
  exact ((congrAp1 parF e).eqTrans (par_add_two _ _)).eqSymm

/-- Two copies cancel. -/
theorem par_self_add (x : PTm n) : Γ ⊢[PRAAx] par (x + x) ≐ zero := by
  have e : Γ ⊢[PRAAx] x + x ≐ two * x := by ipra_ring
  exact (congrAp1 parF e).eqTrans (par_double _)

/-- `par (A + B) = 0` gives `par A = par B`. -/
theorem par_eq_of_add_even {A B : PTm n} (h : Γ ⊢[PRAAx] par (A + B) ≐ zero) :
    Γ ⊢[PRAAx] par A ≐ par B := by
  -- `par A = par (A + (B + B)) = par ((A + B) + B) = par B`.
  have e : Γ ⊢[PRAAx] B + (A + B) ≐ A + two * B := by ipra_ring
  exact (par_add_two A B).eqSymm.eqTrans ((congrAp1 parF e).eqSymm.eqTrans (par_add_even B h))

/-- Finite replacement: quantities that differ modulo two by an even amount have equal
parities. -/
theorem par_replacement {P₁ P₂ T C : PTm n} (h : Γ ⊢[PRAAx] P₁ + T ≐ P₂ + two * C)
    (hT : Γ ⊢[PRAAx] par T ≐ zero) : Γ ⊢[PRAAx] par P₁ ≐ par P₂ :=
  (par_add_even P₁ hT).eqSymm.eqTrans ((congrAp1 parF h).eqTrans (par_add_two P₂ C))

/-- A bounded sum of even terms is even. -/
theorem sum_even_bounded (t : PTm 2) (x M : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ (par (inst2 t (var 0) (Syn.shift x)) ≐ zero))) :
    Γ ⊢[PRAAx] par (ap2 (sumF t) M x) ≐ zero := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift M) ⟶
      (par (ap2 (sumF t) (var 0) (Syn.shift x)) ≐ zero)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap1, subst_ap2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI ((congrAp1 parF (sum_zero t _)).eqTrans par_zero)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap1, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have hf := h.allOpen
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift M) ::
          (le (var 0) (Syn.shift M) ⟶ (par (ap2 (sumF t) (var 0) (Syn.shift x)) ≐ zero)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift M) :=
        le_trans (le_succ_self _) Prf.hyp0
      have ihh := Prf.impE Prf.hyp1 hle
      exact (congrAp1 parF (sum_succ' t (var 0) _)).eqTrans
        ((par_add_even _ (.impE hf.wk.wk Prf.hyp0)).eqTrans ihh)
  have h2 := Prf.allE M hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap1, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 (le_refl M)

end LeanProofs.IPRA
