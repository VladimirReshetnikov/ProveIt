import IPRADerivations.DiophantineNumberTheory.Recurrences
import IPRADerivations.AnalyticNumberTheory.PhiUpper
import IPRADerivations.Core.LinearCombination

/-!
# Strong divisibility of the Pell sequence

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Theorem `thm:gcd`:
`gcd(Y_m, Y_n) = Y_{gcd(m, n)}` for the powers `(X_m, Y_m)` of a solution `(u, v)` of
`u² = D v² + 1` (`Recurrences.X`, `Recurrences.Y`), here for `m, n, v ≥ 1`.

* `X_add`, `Y_add`: `X_{m+n} = X_m X_n + D Y_m Y_n` and `Y_{m+n} = X_m Y_n + X_n Y_m`;
* `cop_XY`: `gcd(Y_k, X_k) = 1`, from `X_k² = D Y_k² + 1`;
* `Y_dvd_mul`: `Y_g ∣ Y_{qg}`;
* the theorem: `Y_g` divides both, and with Bézout `g + Vn = Um`,
  `Y_{Um} = X_g Y_{Vn} + X_{Vn} Y_g`, so `gcd(Y_m, Y_n)` divides `X_{Vn} Y_g`, and it is coprime to
  `X_{Vn}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellGcd

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Recurrences (pellX pellY)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Seq

variable (u v D : PTm n)

/-- `X_m` and `Y_m` for the parameters `u, v, D`. -/
def PX (m : PTm n) : PTm n := Recurrences.X m ![u, v, D]
def PY (m : PTm n) : PTm n := Recurrences.Y m ![u, v, D]

@[simp] theorem subst_PX {k : ℕ} (σ : Fin n → PTm k) (m : PTm n) :
    Syn.subst σ (PX u v D m) = PX (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ D) (Syn.subst σ m) := by
  simp only [PX, subst_sim₁]
  congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem subst_PY {k : ℕ} (σ : Fin n → PTm k) (m : PTm n) :
    Syn.subst σ (PY u v D m) = PY (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ D) (Syn.subst σ m) := by
  simp only [PY, subst_sim₂]
  congr 1; funext i; fin_cases i <;> rfl

theorem congrPX {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] PX u v D m ≐ PX u v D m' := by
  unfold PX Recurrences.X sim₁
  exact congrFst (congrApp _ fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h
    · exact .eqRefl _)

theorem congrPY {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] PY u v D m ≐ PY u v D m' := by
  unfold PY Recurrences.Y sim₂
  exact congrSnd (congrApp _ fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h
    · exact .eqRefl _)

theorem X_zero : Γ ⊢[PRAAx] PX u v D zero ≐ one := by
  have h := sim₁_zero (Γ := Γ) one zero pellX pellY ![u, v, D]
  unfold PX; simpa using h

theorem Y_zero : Γ ⊢[PRAAx] PY u v D zero ≐ zero := by
  have h := sim₂_zero (Γ := Γ) one zero pellX pellY ![u, v, D]
  unfold PY; simpa using h

theorem X_succ (m : PTm n) : Γ ⊢[PRAAx] PX u v D (succ m) ≐ u * PX u v D m + D * (v * PY u v D m) := by
  have h := sim₁_succ (Γ := Γ) one zero pellX pellY ![u, v, D] m
  unfold PX PY; simpa using h

theorem Y_succ (m : PTm n) : Γ ⊢[PRAAx] PY u v D (succ m) ≐ v * PX u v D m + u * PY u v D m := by
  have h := sim₂_succ (Γ := Γ) one zero pellX pellY ![u, v, D] m
  unfold PX PY; simpa using h

end Seq

/-! ## Addition formulas -/

section Add

variable {u v D : PTm n}

abbrev addF (u v D m k : PTm n) : Fm PTm n :=
  (PX u v D (m + k) ≐ PX u v D m * PX u v D k + D * (PY u v D m * PY u v D k)) ⋏
    (PY u v D (m + k) ≐ PX u v D m * PY u v D k + PX u v D k * PY u v D m)

theorem add_base (m : PTm n) : Γ ⊢[PRAAx] addF u v D m zero := by
  have e := congrPX u v D (Γ := Γ) (add_zero m)
  have f := congrPY u v D (Γ := Γ) (add_zero m)
  have x0 := natEq (X_zero (Γ := Γ) u v D); have y0 := natEq (Y_zero (Γ := Γ) u v D)
  refine .andI ?_ ?_
  · refine e.eqTrans ?_; apply deriveNat; ipra_simps; rw [x0, y0]; ring
  · refine f.eqTrans ?_; apply deriveNat; ipra_simps; rw [x0, y0]; ring

theorem add_step {m k : PTm n} (ih : Γ ⊢[PRAAx] addF u v D m k) : Γ ⊢[PRAAx] addF u v D m (succ k) := by
  have e := congrPX u v D (Γ := Γ) (add_succ m k)
  have f := congrPY u v D (Γ := Γ) (add_succ m k)
  have h₁ := natEq (Prf.andE₁ ih); have h₂ := natEq (Prf.andE₂ ih)
  have xs := natEq (X_succ (Γ := Γ) u v D (m + k)); have ys := natEq (Y_succ (Γ := Γ) u v D (m + k))
  have xk := natEq (X_succ (Γ := Γ) u v D k); have yk := natEq (Y_succ (Γ := Γ) u v D k)
  refine .andI (e.eqTrans ?_) (f.eqTrans ?_)
  · apply deriveNat; ipra_simps; rw [xs, xk, yk, h₁, h₂]; ring
  · apply deriveNat; ipra_simps; rw [ys, xk, yk, h₁, h₂]; ring

theorem add_formula (m k : PTm n) : Γ ⊢[PRAAx] addF u v D m k := by
  have hall : Γ ⊢[PRAAx] Fm.all (addF (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift m) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simp only [Fm.subst_and, Fm.subst_eq, subst_PX, subst_PY, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      exact add_base _
    · simp only [Fm.subst_and, Fm.subst_eq, subst_PX, subst_PY, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      exact add_step Prf.hyp0
  have h := Prf.allE k hall
  simp only [Fm.subst_and, Fm.subst_eq, subst_PX, subst_PY, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at h
  exact h

end Add

/-! ## Norm, positivity, coprimality -/

open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)

section Norm

variable {u v D : PTm n} (hU : Γ ⊢[PRAAx] u * u ≐ D * (v * v) + one)
include hU

abbrev normF (u v D k : PTm n) : Fm PTm n := PX u v D k * PX u v D k ≐ D * (PY u v D k * PY u v D k) + one

theorem norm_step {k : PTm n} (ih : Γ ⊢[PRAAx] normF u v D k) : Γ ⊢[PRAAx] normF u v D (succ k) := by
  have h₁ := natEq hU; have h₂ := natEq ih
  have xs := natEq (X_succ (Γ := Γ) u v D k); have ys := natEq (Y_succ (Γ := Γ) u v D k)
  apply deriveNat; ipra_simps; rw [xs, ys]
  linear_combination (Groth.ι (Q.mk _ (PX u v D k)) * Groth.ι (Q.mk _ (PX u v D k)) -
    Groth.ι (Q.mk _ D) * Groth.ι (Q.mk _ (PY u v D k)) * Groth.ι (Q.mk _ (PY u v D k))) * h₁ + h₂

/-- `X_k² = D Y_k² + 1`. -/
theorem pell_norm (k : PTm n) : Γ ⊢[PRAAx] normF u v D k := by
  have hU' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift u * Syn.shift u ≐ Syn.shift D * (Syn.shift v * Syn.shift v) + one := by
    have h := hU.shift
    simp only [Fm.shift, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] at h
    exact h
  have hall : Γ ⊢[PRAAx] Fm.all (normF (Syn.shift u) (Syn.shift v) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_PX, subst_PY, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have x0 := natEq (X_zero (Γ := Γ) u v D); have y0 := natEq (Y_zero (Γ := Γ) u v D)
      apply deriveNat; ipra_simps; rw [x0, y0]; ring
    · simp only [Fm.subst_eq, subst_PX, subst_PY, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact norm_step hU'.wk Prf.hyp0
  have h := Prf.allE k hall
  simp only [Fm.subst_eq, subst_PX, subst_PY, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem X_pos (k : PTm n) : Γ ⊢[PRAAx] PX u v D k ≐ succ (pred (PX u v D k)) := by
  refine .orE (zero_or_succ (PX u v D k)) ?_ Prf.hyp0
  refine succ_ne_zero' _ (a := D * (PY u v D k * PY u v D k)) ?_
  ipra_lc -natEq ((pell_norm hU k).wk (ψ := PX u v D k ≐ zero)) +
    Groth.ι (Q.mk _ (PX u v D k)) * natEq (Prf.hyp0 : ((PX u v D k ≐ zero) :: Γ) ⊢[PRAAx] _)

/-- `gcd(Y_k, X_k) = 1`. -/
theorem cop_XY (k : PTm n) : Γ ⊢[PRAAx] gcd (PY u v D k) (PX u v D k) ≐ one := by
  have hX := X_pos hU k
  have hg := gcd_pos_right (a := PY u v D k) hX
  have d := gcd_dvd_at hg
  have dXX := dvd_mul' hg (PX u v D k) (Prf.andE₂ d)
  have dYY := dvd_congr (mul_comm _ _) (dvd_mul' hg D (dvd_mul' hg (PY u v D k) (Prf.andE₁ d)))
  have e : Γ ⊢[PRAAx] PX u v D k * PX u v D k ≐ one + D * (PY u v D k * PY u v D k) :=
    (pell_norm hU k).eqTrans (add_comm _ _)
  exact eq_one_of_dvd_one hg (dvd_sub' hg (dvd_congr e dXX) dYY)

end Norm

theorem Y_pos {u v D k : PTm n} (hU : Γ ⊢[PRAAx] u * u ≐ D * (v * v) + one) (hv : Γ ⊢[PRAAx] v ≐ succ (pred v))
    (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) : Γ ⊢[PRAAx] PY u v D k ≐ succ (pred (PY u v D k)) := by
  have hX := X_pos hU (pred k)
  have e := (congrPY u v D hk).eqTrans (Y_succ u v D (pred k))
  refine eq_succ_pred (y := pred v * pred (PX u v D (pred k)) + pred v + pred (PX u v D (pred k)) +
    u * PY u v D (pred k)) ?_
  ipra_lc natEq e + Groth.ι (Q.mk _ (PX u v D (pred k))) * natEq hv + (Groth.ι (Q.mk _ (pred v)) + 1) * natEq hX

/-! ## `Y_g ∣ Y_{qg}` -/

theorem Y_dvd_mul {u v D g : PTm n} (hg : Γ ⊢[PRAAx] PY u v D g ≐ succ (pred (PY u v D g))) (q : PTm n) :
    Γ ⊢[PRAAx] dvd (PY u v D g) (PY u v D (q * g)) := by
  have hg' : Γ.map Fm.shift ⊢[PRAAx] PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift g) ≐
      succ (pred (PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift g))) := by
    have h := hg.shift
    simp only [Fm.shift, Fm.subst_eq, subst_PY, PTm.subst_pred, ConciseIPRA.PTm.subst_succ] at h
    exact h
  have hall : Γ ⊢[PRAAx] Fm.all (dvd (PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift g))
      (PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (var 0 * Syn.shift g))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_PY, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact dvd_congr ((Y_zero u v D).eqSymm.eqTrans (congrPY u v D (zero_mul _).eqSymm))
        (rem_zero _)
    · simp only [Fm.subst_eq, subst_ap2, subst_PY, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have e : (dvd (PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift g))
          (PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (var 0 * Syn.shift g)) :: Γ.map Fm.shift) ⊢[PRAAx]
          PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (succ (var 0) * Syn.shift g) ≐
            PX (Syn.shift u) (Syn.shift v) (Syn.shift D) (var 0 * Syn.shift g) *
              PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift g) +
            PX (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift g) *
              PY (Syn.shift u) (Syn.shift v) (Syn.shift D) (var 0 * Syn.shift g) :=
        (congrPY _ _ _ (by ipra_ring)).eqTrans (Prf.andE₂ (add_formula _ _))
      refine dvd_congr e.eqSymm (dvd_add' hg'.wk ?_ ?_)
      · exact dvd_congr (mul_comm _ _) (dvd_mul' hg'.wk _ (dvd_self' hg'.wk))
      · exact dvd_congr (mul_comm _ _) (dvd_mul' hg'.wk _ Prf.hyp0)
  have h := Prf.allE q hall
  simp only [Fm.subst_eq, subst_ap2, subst_PY, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h
  exact h

/-! ## The theorem -/

/-- One Bézout branch: `g + V B = U A` and `h ∣ Y_A`, `h ∣ Y_B` give `h ∣ Y_g`. -/
theorem branch {u v D A B g U V h : PTm n} (hU : Γ ⊢[PRAAx] u * u ≐ D * (v * v) + one)
    (hh : Γ ⊢[PRAAx] h ≐ succ (pred h)) (hYA : Γ ⊢[PRAAx] PY u v D A ≐ succ (pred (PY u v D A)))
    (hYB : Γ ⊢[PRAAx] PY u v D B ≐ succ (pred (PY u v D B))) (hA : Γ ⊢[PRAAx] dvd h (PY u v D A))
    (hB : Γ ⊢[PRAAx] dvd h (PY u v D B)) (hb : Γ ⊢[PRAAx] g + V * B ≐ U * A) :
    Γ ⊢[PRAAx] dvd h (PY u v D g) := by
  have dUA := dvd_trans' hh hYA hA (Y_dvd_mul hYA U)
  have dVB := dvd_trans' hh hYB hB (Y_dvd_mul hYB V)
  have e := (congrPY u v D hb.eqSymm).eqTrans (Prf.andE₂ (add_formula g (V * B)))
  have hsum := dvd_congr (e.eqTrans (add_comm _ _)) dUA
  have hy := dvd_congr (mul_comm _ _) (dvd_mul' hh (PX u v D g) dVB)
  have hx := dvd_sub' hh hsum hy
  have hcop := coprime_dvd_left hh dVB (cop_XY hU (V * B))
  exact gauss hh hcop hx

/-- `thm:gcd` at arbitrary terms: `gcd(Y_m, Y_n) = Y_{gcd(m, n)}` for `m, n, v ≥ 1`. -/
theorem pell_gcd_at {u v D m N : PTm n} (hU : Γ ⊢[PRAAx] u * u ≐ D * (v * v) + one)
    (hv : Γ ⊢[PRAAx] v ≐ succ (pred v)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] gcd (PY u v D m) (PY u v D N) ≐ PY u v D (gcd m N) := by
  have hg := gcd_pos (B := N) hm
  have hYg := Y_pos hU hv hg
  have hYm := Y_pos hU hv hm
  have hYN := Y_pos hU hv hN
  have dg := gcd_dvd' (b := N) hm
  have em := (eq_of_dvd' hg (Prf.andE₁ dg)).eqTrans (mul_comm _ _)
  have eN := (eq_of_dvd' hg (Prf.andE₂ dg)).eqTrans (mul_comm _ _)
  have dYm := dvd_congr (congrPY u v D em.eqSymm) (Y_dvd_mul hYg (quo m (gcd m N)))
  have dYN := dvd_congr (congrPY u v D eN.eqSymm) (Y_dvd_mul hYg (quo N (gcd m N)))
  have hh := gcd_pos (B := PY u v D N) hYm
  have hd := gcd_dvd' (b := PY u v D N) hYm
  have l₁ := dvd_le' hYg (gcd_greatest' hYg dYm dYN) hh
  have l₂ : Γ ⊢[PRAAx] dvd (gcd (PY u v D m) (PY u v D N)) (PY u v D (gcd m N)) := by
    refine .orE (bezout_at m N) ?_ ?_
    · exact branch hU.wk hh.wk hYm.wk hYN.wk (Prf.andE₁ hd).wk (Prf.andE₂ hd).wk Prf.hyp0
    · exact branch hU.wk hh.wk hYN.wk hYm.wk (Prf.andE₂ hd).wk (Prf.andE₁ hd).wk Prf.hyp0
  exact le_antisymm (dvd_le' hh l₂ hYg) l₁

/-- `thm:gcd`: variables `0 = m − 1`, `1 = n − 1`, `2 = u`, `3 = v − 1`, `4 = D`. -/
abbrev pellGcdFormula : Fm PTm 5 :=
  var 2 * var 2 ≐ var 4 * (succ (var 3) * succ (var 3)) + one ⟶
    gcd (PY (var 2) (succ (var 3)) (var 4) (succ (var 0))) (PY (var 2) (succ (var 3)) (var 4) (succ (var 1))) ≐
      PY (var 2) (succ (var 3)) (var 4) (gcd (succ (var 0)) (succ (var 1)))

theorem pell_gcd : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 pellGcdFormula :=
  closeUniv 5 (.impI (pell_gcd_at Prf.hyp0 (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm)
    (congrSucc (pred_succ _).eqSymm)))

end LeanProofs.IPRA.DiophantineNumberTheory.PellGcd
