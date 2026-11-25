import IPRADerivations.Combinatorics.Fibonacci
import IPRADerivations.Combinatorics.HockeyStick
import IPRADerivations.Core.LinearCombination

/-!
# Fibonacci numbers as diagonal sums of Pascal's triangle

Packet: `combinatorics/Combinatorics-iPRA`, `enumeration.tex`, result 05 ("Compositions and Fibonacci
identities"): "`F_{n+1} = ∑_{j=0}^{⌊n/2⌋} b(n − j, j)`". With the guarded coefficients `C(m, k)` of
`Combinatorics/Vandermonde` (zero for `k > m`) the sum is taken over all `j ≤ n`; the terms with `j > n − j`
vanish. Uniformly in the term `n`, as iPRA derivations:

* `diag n = ∑_{j ≤ n} C(n − j, j)` and `offd n = ∑_{j ≤ n} C(n − j, j + 1)`;
* `diag_zero`, `diag_one`: `diag 0 = diag 1 = 1`;
* `diag_succ`: `diag (n + 1) = 1 + offd n` (split off `j = 0` and shift the index);
* `diag_succ_succ`: `diag (n + 2) = 1 + (offd n + diag n)` (split off `j = 0` and `j = n + 2`, then Pascal's
  rule `C(n + 1 − j, j + 1) = C(n − j, j + 1) + C(n − j, j)` for `j ≤ n`);
* `diag_rec`: `diag (n + 2) = diag (n + 1) + diag n`;
* `fib_diagonal`: `∑_{j ≤ n} C(n − j, j) = F_{n+1}`, by induction on the pair of equations for `n` and `n + 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciDiagonal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_pascal gb_above)
open LeanProofs.IPRA.Combinatorics.Fibonacci (fib fibS fibS_zero fib_zero fibS_succ fib_succ subst_fibS)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `C(x − j, j)`; variables `0 = j`, `1 = x`. -/
abbrev dB : PTm 2 := gb (monus (var 1) (var 0)) (var 0)

/-- `C(x − j, j + 1)`; variables `0 = j`, `1 = x`. -/
abbrev eB : PTm 2 := gb (monus (var 1) (var 0)) (succ (var 0))

theorem inst2_d (j x : PTm n) : inst2 dB j x = gb (monus x j) j := by simp [inst2]

theorem inst2_e (j x : PTm n) : inst2 eB j x = gb (monus x j) (succ j) := by simp [inst2]

/-- `∑_{j ≤ x} C(x − j, j)`. -/
abbrev diag (x : PTm n) : PTm n := ap2 (sumF dB) (succ x) x

/-- `∑_{j ≤ x} C(x − j, j + 1)`. -/
abbrev offd (x : PTm n) : PTm n := ap2 (sumF eB) (succ x) x

/-! ## Pointwise identities -/

/-- `C(m + 1 − (j + 1), j + 1) = C(m − j, j + 1)`. -/
theorem pt_one (j m : PTm n) : Γ ⊢[PRAAx] inst2 (shiftBody dB) j (succ m) ≐ inst2 eB j m := by
  rw [inst2_shiftBody, inst2_d, inst2_e]
  exact congrGb (succ_monus_succ m j) (.eqRefl _)

/-- For `j ≤ m`: `C(m + 2 − (j + 1), j + 1) = C(m − j, j + 1) + C(m − j, j)`. -/
theorem pt_two {j m : PTm n} (h : Γ ⊢[PRAAx] lt j (succ m)) :
    Γ ⊢[PRAAx] inst2 (shiftBody dB) j (succ (succ m)) ≐ inst2 (addBody eB dB) j m := by
  rw [inst2_shiftBody, inst2_addBody, inst2_d, inst2_e, inst2_d]
  have hle : Γ ⊢[PRAAx] le j m := (succ_monus_succ j m).eqSymm.eqTrans h
  have e1 : Γ ⊢[PRAAx] monus (succ (succ m)) (succ j) ≐ succ (monus m j) := by
    refine (succ_monus_succ (succ m) j).eqTrans ?_
    exact (congrMonus ((congrSucc (eq_add_of_le hle)).eqTrans (add_succ _ _).eqSymm) (.eqRefl _)).eqTrans
      (add_monus' _ _)
  exact (congrGb e1 (.eqRefl _)).eqTrans (gb_pascal _ _)

/-! ## The diagonal sums -/

theorem diag_zero : Γ ⊢[PRAAx] diag (zero : PTm n) ≐ one := by
  have s := sum_succ' (Γ := Γ) dB zero zero
  rw [inst2_d] at s
  exact s.eqTrans ((congrAdd (sum_zero _ _) (gb_zero _)).eqTrans (zero_add _))

theorem offd_zero : Γ ⊢[PRAAx] offd (zero : PTm n) ≐ zero := by
  have s := sum_succ' (Γ := Γ) eB zero zero
  rw [inst2_e] at s
  exact s.eqTrans ((congrAdd (sum_zero _ _)
    ((congrGb (monus_self _) (.eqRefl _)).eqTrans (gb_above (le_refl _)))).eqTrans (zero_add _))

/-- `diag (m + 1) = 1 + offd m`. -/
theorem diag_succ (m : PTm n) : Γ ⊢[PRAAx] diag (succ m) ≐ one + offd m := by
  have s := sum_shift (Γ := Γ) dB (succ m) (succ m)
  rw [inst2_d] at s
  have c : Γ ⊢[PRAAx] ap2 (sumF (shiftBody dB)) (succ m) (succ m) ≐ ap2 (sumF eB) (succ m) m := by
    refine sum_congr_bounded (shiftBody dB) eB (succ m) m (succ m) (.allI (.impI ?_))
    have es : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
    rw [es]
    exact pt_one _ _
  exact s.eqTrans (congrAdd (gb_zero _) c)

theorem diag_one : Γ ⊢[PRAAx] diag (succ (zero : PTm n)) ≐ one :=
  (diag_succ zero).eqTrans ((congrAdd (.eqRefl _) offd_zero).eqTrans (add_zero _))

/-- `diag (m + 2) = 1 + (offd m + diag m)`. -/
theorem diag_succ_succ (m : PTm n) :
    Γ ⊢[PRAAx] diag (succ (succ m)) ≐ one + (offd m + diag m) := by
  have s := sum_shift (Γ := Γ) dB (succ (succ m)) (succ (succ m))
  rw [inst2_d] at s
  have l := sum_succ' (Γ := Γ) (shiftBody dB) (succ m) (succ (succ m))
  rw [inst2_shiftBody, inst2_d] at l
  have hk : Γ ⊢[PRAAx] le (succ zero) (succ (succ m)) :=
    le_of_eq_add (d := succ m) (by ipra_ring)
  have z : Γ ⊢[PRAAx] gb (monus (succ (succ m)) (succ (succ m))) (succ (succ m)) ≐ zero :=
    (congrGb (monus_self _) (.eqRefl _)).eqTrans (gb_above hk)
  have c : Γ ⊢[PRAAx] ap2 (sumF (shiftBody dB)) (succ m) (succ (succ m)) ≐
      ap2 (sumF (addBody eB dB)) (succ m) m := by
    refine sum_congr_bounded (shiftBody dB) (addBody eB dB) (succ (succ m)) m (succ m) (.allI (.impI ?_))
    have es : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
    have es2 : Syn.shift (succ (succ m)) = succ (succ (Syn.shift m)) := by simp [Syn.shift]
    rw [es2, es]
    exact pt_two Prf.hyp0
  have a := sum_add (Γ := Γ) eB dB (succ m) m
  refine s.eqTrans (congrAdd (gb_zero _) ?_)
  exact l.eqTrans ((congrAdd (c.eqTrans a) z).eqTrans (add_zero _))

/-- `diag (m + 2) = diag (m + 1) + diag m`. -/
theorem diag_rec (m : PTm n) : Γ ⊢[PRAAx] diag (succ (succ m)) ≐ diag (succ m) + diag m := by
  ipra_lc natEq (diag_succ_succ (Γ := Γ) m) - natEq (diag_succ (Γ := Γ) m)

/-! ## Identification with the Fibonacci numbers -/

theorem fibS_one : Γ ⊢[PRAAx] fibS (succ (zero : PTm n)) ≐ one :=
  (fibS_succ zero).eqTrans ((congrAdd fibS_zero fib_zero).eqTrans (add_zero _))

theorem diag_step {k : PTm n} (a : Γ ⊢[PRAAx] diag k ≐ fibS k)
    (b : Γ ⊢[PRAAx] diag (succ k) ≐ fibS (succ k)) :
    Γ ⊢[PRAAx] diag (succ (succ k)) ≐ fibS (succ (succ k)) := by
  ipra_lc natEq (diag_rec (Γ := Γ) k) + natEq b + natEq a - natEq (fibS_succ (Γ := Γ) (succ k)) -
    natEq (fib_succ (Γ := Γ) k)

/-- Variable: `0 = k`. -/
private abbrev fdF : Fm PTm 1 :=
  (diag (var 0) ≐ fibS (var 0)) ⋏ (diag (succ (var 0)) ≐ fibS (succ (var 0)))

private theorem fd₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fdF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_and, Fm.subst_eq, subst_ap2, subst_fibS, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .andI (diag_zero.eqTrans fibS_zero.eqSymm) (diag_one.eqTrans fibS_one.eqSymm)
  · simp only [Fm.subst_and, Fm.subst_eq, subst_ap2, subst_fibS, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .andI (Prf.andE₂ Prf.hyp0) (diag_step (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0))

/-- `∑_{j ≤ k} C(k − j, j) = F_{k+1}`. -/
theorem fib_diagonal (k : PTm n) : Γ ⊢[PRAAx] diag k ≐ fibS k := by
  have h := inst (Γ := Γ) fd₀ (![k] : Fin 1 → PTm n)
  simp only [Fm.subst_and, Fm.subst_eq, subst_ap2, subst_fibS, Syn.subst_var, ConciseIPRA.PTm.subst_succ,
    Matrix.cons_val_zero] at h
  exact Prf.andE₁ h

end LeanProofs.IPRA.Combinatorics.FibonacciDiagonal
