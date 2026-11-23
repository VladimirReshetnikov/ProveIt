import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.Combinatorics.CentralBinomial
import IPRADerivations.DiophantineNumberTheory.ResidueFacts

/-!
# Bertrand's postulate: the odd central binomial coefficient

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex`, §"Two estimates from Pascal's triangle", the
estimate (5): `C(2a + 1, a) ≤ 4^a`.

The paper bounds twice the coefficient by the row sum `2^{2a+1}` through the symmetry of the row. Here the
same bound comes from the central coefficients, with no row sum:

* `cb_succ_odd`: `C(2k + 2, k + 1) = 2 C(2k + 1, k)`, from `(k + 1) C(2k + 2, k + 1) = 2 (2k + 1) C(2k, k)`
  and the two Catalan identities `(k + 1) Cat_k = C(2k, k)`, `(2k + 1) Cat_k = C(2k + 1, k)`;
* `cb_succ_le`: `C(2k + 2, k + 1) ≤ 4 C(2k, k)`, from `2 Cat_k + C(2k + 2, k + 1) = 4 C(2k, k)`;
* `cb_succ_half`: `C(2k + 2, k + 1) ≤ 2 · 4^k`, by induction;
* `odd_binom_le` (the estimate (5)): `C(2k + 1, k) ≤ 4^k`;
* `odd_binom_pos`: `C(2k + 1, k) ≥ 1`.

Powers of four are written `2^{2k}`, as in `CentralBinomial.central_lower`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BertrandCentral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.Catalan (cb cat cb_rec cb_zero cat_spec cat_odd_binom cat_telescope succ_pos)
open LeanProofs.IPRA.Combinatorics.CentralBinomial (central_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (pw_two)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The central coefficient of the next even row -/

/-- `C(2k + 2, k + 1) = 2 C(2k + 1, k)`. -/
theorem cb_succ_odd (k : PTm n) : Γ ⊢[PRAAx] cb (succ k) ≐ two * binom (succ (two * k)) k := by
  refine mul_cancel (D := succ k) (succ_pos k) ?_
  have r := natEq (cb_rec (Γ := Γ) k); have s₀ := natEq (cat_spec (Γ := Γ) k)
  have o := natEq (cat_odd_binom (Γ := Γ) k)
  apply deriveNat; ipra_simps
  linear_combination r - 2 * (2 * 𝔞(k) + 1) * s₀ + 2 * (𝔞(k) + 1) * o

/-- `C(2k + 2, k + 1) ≤ 4 C(2k, k)`. -/
theorem cb_succ_le (k : PTm n) : Γ ⊢[PRAAx] le (cb (succ k)) ((two * two) * cb k) :=
  le_of_eq_add (d := two * cat k) ((cat_telescope k).eqSymm.eqTrans (add_comm _ _))

/-- `C(2, 1) = 2`. -/
theorem cb_one : Γ ⊢[PRAAx] cb (succ (zero : PTm n)) ≐ two := by
  have r := natEq (cb_rec (Γ := Γ) zero); have z := natEq (cb_zero (Γ := Γ))
  apply deriveNat; ipra_simps
  linear_combination r + 2 * z

/-- `4^{k+1} = 4 · 4^k`, as `2^{2(k+1)} = 4 · 2^{2k}`. -/
theorem four_step (k : PTm n) : Γ ⊢[PRAAx] pw two (two * succ k) ≐ (two * two) * pw two (two * k) := by
  have e : Γ ⊢[PRAAx] two * succ k ≐ two * k + two := by apply deriveNat; ipra_simps; ring
  exact (congrPw (.eqRefl _) e).eqTrans ((pw_add two (two * k) two).eqTrans
    ((congrMul (.eqRefl _) (pw_two two)).eqTrans (mul_comm _ _)))

/-- `4^0 = 1`. -/
theorem four_zero : Γ ⊢[PRAAx] pw two (two * (zero : PTm n)) ≐ one := by
  have e : Γ ⊢[PRAAx] two * (zero : PTm n) ≐ zero := by apply deriveNat; ipra_simps; ring
  exact (congrPw (.eqRefl _) e).eqTrans (pw_zero two)

/-- Variable: `0 = k` (induction). -/
private abbrev halfF : Fm PTm 1 := le (cb (succ (var 0))) (two * pw two (two * var 0))

private theorem half₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] halfF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    have p : ([] : List (Fm PTm 0)) ⊢[PRAAx] two * pw two (two * zero) ≐ two :=
      (congrMul (.eqRefl _) four_zero).eqTrans ((mul_comm _ _).eqTrans (one_mul _))
    exact le_congr cb_one.eqSymm p.eqSymm (le_refl two)
  · simp only [subst_le, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    have ih : [halfF] ⊢[PRAAx] le (cb (succ (var 0))) (two * pw two (two * var 0)) := Prf.hyp0
    have f := natEq (four_step (Γ := [halfF]) (var 0))
    have E : [halfF] ⊢[PRAAx] (two * two) * (two * pw two (two * var 0)) ≐ two * pw two (two * succ (var 0)) := by
      apply deriveNat; ipra_simps
      linear_combination -2 * f
    exact le_trans (cb_succ_le (succ (var 0))) (le_congr (.eqRefl _) E (le_mul_mono (le_refl (two * two)) ih))

/-- `C(2k + 2, k + 1) ≤ 2 · 4^k`. -/
theorem cb_succ_half (k : PTm n) : Γ ⊢[PRAAx] le (cb (succ k)) (two * pw two (two * k)) := by
  simpa using inst (Γ := Γ) half₀ (![k] : Fin 1 → PTm n)

/-! ## The estimate (5) -/

/-- `C(2k + 1, k) ≤ 4^k`. -/
theorem odd_binom_le (k : PTm n) : Γ ⊢[PRAAx] le (binom (succ (two * k)) k) (pw two (two * k)) :=
  mul_le_cancel (d' := one) (le_congr (cb_succ_odd k) (.eqRefl _) (cb_succ_half k))

/-- `C(2k + 1, k) ≥ 1`. -/
theorem odd_binom_pos (k : PTm n) :
    Γ ⊢[PRAAx] binom (succ (two * k)) k ≐ succ (pred (binom (succ (two * k)) k)) := by
  refine .orE (zero_or_succ (binom (succ (two * k)) k)) ?_ Prf.hyp0
  have z := natEq (Prf.hyp0 (Γ := Γ) (φ := binom (succ (two * k)) k ≐ zero))
  have o := natEq ((cb_succ_odd (Γ := Γ) k).wk (ψ := binom (succ (two * k)) k ≐ zero))
  have e1 := natEq (eq_add_of_le (central_pos (Γ := (binom (succ (two * k)) k ≐ zero) :: Γ) (succ k)))
  refine succ_ne_zero' (a := monus (cb (succ k)) one) _ ?_
  apply deriveNat; ipra_simps
  linear_combination o + 2 * z - e1

end LeanProofs.IPRA.AnalyticNumberTheory.BertrandCentral
