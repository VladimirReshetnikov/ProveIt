import IPRADerivations.DiophantineNumberTheory.PellAll
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.LinearCombination

/-!
# The index of a Pell solution

Packet: `diophantine_ipra_2026-11-15`, `paper/03_stormer.tex`, Lemma `lem:stormer-pell-powers`: every
positive solution `(x, y)` of `x² − D y² = 1` equals `(x_m, y_m)` for a unique positive index `m ≤ x`.

For the powers `(X_m, Y_m) = (A, B)^m` of `Recurrences` (with `A, B ≥ 1`):

* `X_succ`, `Y_succ`: `X_{m+1} = A X_m + D B Y_m`, `Y_{m+1} = B X_m + A Y_m`;
* `X_pos`: `X_m ≥ 1`; `Y_mono`: `Y_m + k ≤ Y_{m+k}`, so the `Y_m` are strictly increasing;
* `index_unique`: `Y_m = Y_{m'}` forces `m = m'`;
* `stormer_pell_powers` (`lem:stormer-pell-powers`): for a fundamental solution `(A, B)`, `D ≥ 1` and a
  solution with `y ≥ 1`, the explicit exponent `c` of `PellAll` satisfies `(x, y) = (X_c, Y_c)` and
  `1 ≤ c ≤ x`, and it is the only index with `y = Y_m`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellIndex

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Recurrences (pellX pellY)
open LeanProofs.IPRA.DiophantineNumberTheory.PellAll (pell_all_at minimal C p3 Xp Yp)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem X_succ (m : PTm n) (ps : Fin 3 → PTm n) :
    Γ ⊢[PRAAx] Xp (succ m) ps ≐ ps 0 * Xp m ps + ps 2 * (ps 1 * Yp m ps) := by
  have h := sim₁_succ (Γ := Γ) one zero pellX pellY ps m
  simp only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one,
    finCases_two, finCases_three, finCases_four, finCases_five, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, fin_succ_two] at h
  exact h

theorem Y_succ (m : PTm n) (ps : Fin 3 → PTm n) :
    Γ ⊢[PRAAx] Yp (succ m) ps ≐ ps 1 * Xp m ps + ps 0 * Yp m ps := by
  have h := sim₂_succ (Γ := Γ) one zero pellX pellY ps m
  simp only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one,
    finCases_two, finCases_three, finCases_four, finCases_five, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, fin_succ_two] at h
  exact h

theorem X_zero (ps : Fin 3 → PTm n) : Γ ⊢[PRAAx] Xp zero ps ≐ one := by
  simpa using sim₁_zero (Γ := Γ) one zero pellX pellY ps

theorem Y_zero (ps : Fin 3 → PTm n) : Γ ⊢[PRAAx] Yp zero ps ≐ zero := by
  simpa using sim₂_zero (Γ := Γ) one zero pellX pellY ps

theorem congrYp {m m' : PTm n} (ps : Fin 3 → PTm n) (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Yp m ps ≐ Yp m' ps := by
  have e := Prf.eqSubst1 (Fm.eq (Yp (var 0) (fun i => Syn.shift (ps i))) (Syn.shift (Yp m ps))) h
    (by simpa [Syn.subst_inst_shift] using Prf.eqRefl (Γ := Γ) (Yp m ps))
  simpa [Syn.subst_inst_shift] using e.eqSymm

section Mono

variable {ps : Fin 3 → PTm n} (hA : Γ ⊢[PRAAx] le one (ps 0)) (hB : Γ ⊢[PRAAx] le one (ps 1))
include hA hB

theorem X_step {m : PTm n} (ih : Γ ⊢[PRAAx] le one (Xp m ps)) : Γ ⊢[PRAAx] le one (Xp (succ m) ps) := by
  have a := natEq (eq_add_of_le hA); have x := natEq (eq_add_of_le ih)
  refine le_of_eq_add (d := monus (Xp m ps) one + monus (ps 0) one * Xp m ps + ps 2 * (ps 1 * Yp m ps)) ?_
  ipra_lc natEq (X_succ (Γ := Γ) m ps) + 𝔞 (Xp m ps) * a + x

/-- `X_m ≥ 1`. -/
theorem X_pos (m : PTm n) : Γ ⊢[PRAAx] le one (Xp m ps) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le one (Xp (var 0) fun i => Syn.shift (ps i))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_sim₁, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact le_congr (.eqRefl _) (X_zero ps).eqSymm (le_refl _)
    · simp only [subst_le, subst_sim₁, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have hA' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift (ps 0)) := by simpa [Fm.shift, Syn.shift] using hA.shift
      have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift (ps 1)) := by simpa [Fm.shift, Syn.shift] using hB.shift
      exact X_step (ps := fun i => Syn.shift (ps i)) hA'.wk hB'.wk Prf.hyp0
  simpa [Syn.subst_inst_shift] using Prf.allE m hall

/-- `Y_{m+1} ≥ Y_m + 1`. -/
theorem Y_step (m : PTm n) : Γ ⊢[PRAAx] le (succ (Yp m ps)) (Yp (succ m) ps) := by
  have a := natEq (eq_add_of_le hA); have b := natEq (eq_add_of_le hB)
  refine le_of_eq_add (d := monus (ps 1) one * Xp m ps + monus (Xp m ps) one + monus (ps 0) one * Yp m ps) ?_
  ipra_lc natEq (Y_succ (Γ := Γ) m ps) + 𝔞 (Xp m ps) * b + natEq (eq_add_of_le (X_pos hA hB m)) + 𝔞 (Yp m ps) * a

/-- `Y_m + k ≤ Y_{m+k}`. -/
theorem Y_mono (m k : PTm n) : Γ ⊢[PRAAx] le (Yp m ps + k) (Yp (m + k) ps) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (Yp (Syn.shift m) (fun i => Syn.shift (ps i)) + var 0)
      (Yp (Syn.shift m + var 0) fun i => Syn.shift (ps i))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_sim₂, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      exact le_congr (add_zero _).eqSymm (congrYp ps (add_zero m).eqSymm) (le_refl _)
    · simp only [subst_le, subst_sim₂, PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have hA' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift (ps 0)) := by simpa [Fm.shift, Syn.shift] using hA.shift
      have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift (ps 1)) := by simpa [Fm.shift, Syn.shift] using hB.shift
      let C : List (Fm PTm (n + 1)) := le (Yp (Syn.shift m) (fun i => Syn.shift (ps i)) + var 0)
        (Yp (Syn.shift m + var 0) fun i => Syn.shift (ps i)) :: Γ.map Fm.shift
      have st := Y_step (Γ := C) (ps := fun i => Syn.shift (ps i)) hA'.wk hB'.wk (Syn.shift m + var 0)
      have ih' : C ⊢[PRAAx] le (succ (Yp (Syn.shift m) (fun i => Syn.shift (ps i)) + var 0))
          (succ (Yp (Syn.shift m + var 0) fun i => Syn.shift (ps i))) := (succ_monus_succ _ _).eqTrans Prf.hyp0
      exact le_congr (add_succ _ _).eqSymm (congrYp _ (add_succ _ _).eqSymm) (le_trans ih' st)
  simpa [Syn.subst_inst_shift] using Prf.allE k hall

theorem lt_index_absurd {m m' : PTm n} (φ : Fm PTm n) (hlt : Γ ⊢[PRAAx] lt m m')
    (h : Γ ⊢[PRAAx] Yp m ps ≐ Yp m' ps) : Γ ⊢[PRAAx] φ := by
  have e := eq_add_of_le (le_of_lt hlt)
  have mono := Y_mono hA hB m (monus m' m)
  have l := le_congr (.eqRefl _) (congrYp ps e.eqSymm) mono
  have e' := natEq (eq_add_of_le hlt); have e'' := natEq e
  have pos : Γ ⊢[PRAAx] le one (monus m' m) :=
    le_of_eq_add (d := monus m' (succ m)) (by apply deriveNat; ipra_simps; linear_combination e' - e'')
  have l2 : Γ ⊢[PRAAx] le (succ (Yp m ps)) (Yp m' ps) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (add_le_add₂ (le_refl _) pos)) l
  exact lt_irrefl _ _ (le_congr (.eqRefl _) h.eqSymm l2)

/-- `Y_m = Y_{m'}` forces `m = m'`. -/
theorem index_unique {m m' : PTm n} (h : Γ ⊢[PRAAx] Yp m ps ≐ Yp m' ps) : Γ ⊢[PRAAx] m ≐ m' :=
  .orE (lt_or_le m m') (lt_index_absurd hA.wk hB.wk _ Prf.hyp0 h.wk)
    (.orE (lt_or_le m' m) (lt_index_absurd hA.wk.wk hB.wk.wk _ Prf.hyp0 h.wk.wk.eqSymm)
      (le_antisymm Prf.hyp0 Prf.hyp1))

end Mono

/-! ## `lem:stormer-pell-powers` -/

section Stormer

variable {ps : Fin 5 → PTm n} (hA : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ one + ps 2 * (ps 1 * ps 1))
  (hB : Γ ⊢[PRAAx] ps 1 ≐ succ (pred (ps 1))) (hmin : Γ ⊢[PRAAx] minimal (ps 2) (ps 1))
  (hx : Γ ⊢[PRAAx] ps 3 * ps 3 ≐ one + ps 2 * (ps 4 * ps 4)) (hy : Γ ⊢[PRAAx] ps 4 ≐ succ (pred (ps 4)))
  (hD : Γ ⊢[PRAAx] le one (ps 2))

include hA in
theorem A_pos : Γ ⊢[PRAAx] le one (ps 0) := by
  refine .orE (zero_or_succ (ps 0)) ?_ (DiophantineNumberTheory.Coprime.one_le_of_pos Prf.hyp0)
  have a := natEq (hA.wk (ψ := ps 0 ≐ zero)); have z := natEq (Prf.hyp0 : ((ps 0 ≐ zero) :: Γ) ⊢[PRAAx] ps 0 ≐ zero)
  exact succ_ne_zero' _ (a := ps 2 * (ps 1 * ps 1)) (by apply deriveNat; ipra_simps; linear_combination -a + (𝔞 (ps 0) + 0) * z)

include hA hB hmin hx hy hD in
/-- `lem:stormer-pell-powers`: `(x, y) = (x_c, y_c)` with `1 ≤ c ≤ x`. -/
theorem stormer_pell_powers :
    Γ ⊢[PRAAx] ((ps 3 ≐ Xp (C (ps 4) ps) (p3 ps)) ⋏ (ps 4 ≐ Yp (C (ps 4) ps) (p3 ps))) ⋏
      (le one (C (ps 4) ps) ⋏ le (C (ps 4) ps) (ps 3)) := by
  have all := pell_all_at hA hB hmin hx
  have ex := Prf.andE₁ all; have ey := Prf.andE₁ (Prf.andE₂ all); have cy := Prf.andE₂ (Prf.andE₂ all)
  refine .andI (.andI ex ey) (.andI ?_ ?_)
  · refine .orE (zero_or_succ (C (ps 4) ps)) ?_ (DiophantineNumberTheory.Coprime.one_le_of_pos Prf.hyp0)
    have y0 := ey.wk.eqTrans ((congrYp _ Prf.hyp0).eqTrans (Y_zero _))
    exact succ_ne_zero' _ (hy.wk.eqSymm.eqTrans y0)
  · refine le_trans cy (DiophantineNumberTheory.Coprime.le_of_sq_le ?_)
    have a := natEq hx; have d := natEq (eq_add_of_le hD)
    refine le_of_eq_add (d := one + monus (ps 2) one * (ps 4 * ps 4)) ?_
    ipra_lc a + 𝔞 (ps 4) * 𝔞 (ps 4) * d

include hA hB in
/-- `lem:stormer-pell-powers`, uniqueness: any index `m` with `y = y_m` is `c`. -/
theorem stormer_index_unique {m : PTm n} (h : Γ ⊢[PRAAx] Yp m (p3 ps) ≐ Yp (C (ps 4) ps) (p3 ps)) :
    Γ ⊢[PRAAx] m ≐ C (ps 4) ps :=
  index_unique (ps := p3 ps) (A_pos hA) (DiophantineNumberTheory.Coprime.one_le_of_pos hB) h

end Stormer

end LeanProofs.IPRA.DiophantineNumberTheory.PellIndex
