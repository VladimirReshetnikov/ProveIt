import IPRADerivations.AnalyticNumberTheory.FactorVector
import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.AnalyticNumberTheory.MuLambda
import IPRADerivations.Core.Fubini

/-!
# Valuations determine a positive number; the weight of a power

Infrastructure for `analytic-number-theory/mertens-ipra`, `identities.tex`, `thm:totient-chebyshev` ("Unique
factorization gives `log a = ∑_{p ≤ N} v_p(a) log p` in these coordinates … Its multiplicative form in positive
rationals is `∏ a^{M(q_N(a))} = lcm(1, …, N)`").

* **`val_ext`**: positive `A`, `B` with `v_p(A) = v_p(B)` for every prime `p` are equal. Both are the product
  `∏_{p < N} p^{[p prime] v_p}` for `N = A + B + 1` (`FactorVector.reconstruct`), and the products agree factor by
  factor. The hypothesis is the universally quantified formula `∀ p. isP p = 1 → v_p(A) = v_p(B)`;
* `dW`, **`lw_delta`**: for the weight `w(q) = [q = p]` the completely additive weight `L_w` of
  `WeightedMangoldt` is the valuation: `L_w(m) = v_p(m)` for a prime `p` and `m ≥ 1`;
* **`lw_pow`**: `L_w(a^e) = e · L_w(a)` for `a ≥ 1` and every weight `w`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ValuationExt

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 isP_of_prime pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos val_big)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (R reconstruct)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw ellB)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (ell_at lw_mul congrLw)
open LeanProofs.IPRA.AnalyticNumberTheory.MuLambda (lw_one)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Extensionality -/

/-- **Positive numbers with the same valuation at every prime are equal.** -/
theorem val_ext {A B : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (h : Γ ⊢[PRAAx] Fm.all ((isP (var 0) ≐ one) ⟶
      (val (var 0) (Syn.shift A) ≐ val (var 0) (Syn.shift B)))) : Γ ⊢[PRAAx] A ≐ B := by
  have lA : Γ ⊢[PRAAx] lt A (succ (A + B)) := (succ_monus_succ _ _).eqTrans (le_add_right A B)
  have lB : Γ ⊢[PRAAx] lt B (succ (A + B)) := (succ_monus_succ _ _).eqTrans (le_add_left B A)
  have e : Γ ⊢[PRAAx] R (succ (A + B)) A ≐ R (succ (A + B)) B := by
    refine prod_congr_bounded FactorVector.fB FactorVector.fB A B (succ (A + B)) (.allI (.impI ?_))
    rw [FactorVector.inst2_fB, FactorVector.inst2_fB]
    refine .orE (isP_01 (var 0)) ?_ ?_
    · have h0 : ((isP (var 0) ≐ zero) :: lt (var 0) (Syn.shift (succ (A + B))) :: Γ.map Fm.shift) ⊢[PRAAx]
          isP (var 0) ≐ zero := Prf.hyp0
      exact congrPw (.eqRefl _) ((zero_mul_l h0 _).eqTrans (zero_mul_l h0 _).eqSymm)
    · exact congrPw (.eqRefl _) (congrMul (.eqRefl _) (.impE h.allOpen.wk.wk Prf.hyp0))
  exact (reconstruct hA lA).eqSymm.eqTrans (e.eqTrans (reconstruct hB lB))

/-! ## The weight that reads off one valuation -/

/-- The weight `[q = y]`, over `0 = q`, `1 = y`. -/
abbrev dW : PTm 2 := eqb (var 1) (var 0)

theorem inst2_dW (q y : PTm n) : inst2 dW q y = eqb y q := by simp [inst2]

/-- `[q prime] v_q(m)`, over `0 = q`, `1 = m`. -/
abbrev vG : PTm 2 := isP (var 0) * val (var 0) (var 1)

theorem inst2_vG (q m : PTm n) : inst2 vG q m = isP q * val q m := by simp [inst2]

/-- The term of `L_w` for the weight `[q = p]`, as a term of a delta sum. -/
theorem delta_pt (q m p : PTm n) :
    Γ ⊢[PRAAx] inst2 (ellB dW) q (pairT m p) ≐ inst2 (dB vG) q (pairT p m) := by
  rw [inst2_dB, inst2_vG]
  have e := ell_at (Γ := Γ) dW q m p
  rw [inst2_dW] at e
  exact e.eqTrans ((mul_comm _ _).eqTrans (congrMul
    (AnalyticNumberTheory.Euler.congrEqb (fst_pair _ _).eqSymm (.eqRefl _))
    (congrMul (.eqRefl _) (Mobius.congrVal (.eqRefl _) (snd_pair _ _).eqSymm))))

/-- **`L_w(m) = v_p(m)` for the weight `w(q) = [q = p]`**, `p` prime and `m ≥ 1`. -/
theorem lw_delta {p m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Lw dW m p ≐ val p m := by
  have s1 : Γ ⊢[PRAAx] Lw dW m p ≐ ap2 (sumF (dB vG)) (succ m) (pairT p m) := by
    refine sum_congr_bounded (ellB dW) (dB vG) (pairT m p) (pairT p m) (succ m) (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT]
    exact delta_pt _ _ _
  refine .orE (lt_or_le p (succ m)) ?_ ?_
  · have hlt : (lt p (succ m) :: Γ) ⊢[PRAAx] lt p (succ m) := Prf.hyp0
    have s2 := sum_delta vG (x := m) hlt
    rw [inst2_vG] at s2
    exact s1.wk.eqTrans (s2.eqTrans ((congrMul (isP_of_prime hp.wk) (.eqRefl _)).eqTrans (one_mul _)))
  · let C : List (Fm PTm n) := le (succ m) p :: Γ
    have hle : C ⊢[PRAAx] le (succ m) p := Prf.hyp0
    have hle' : C.map Fm.shift ⊢[PRAAx] le (succ (Syn.shift m)) (Syn.shift p) := by
      simpa [Fm.shift, Syn.shift] using hle.shift
    have z : C ⊢[PRAAx] ap2 (sumF (dB vG)) (succ m) (pairT p m) ≐ zero := by
      refine sum_zero_of_bounded (dB vG) (pairT p m) (succ m) (.allI (.impI ?_))
      have ss : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
      rw [shift_pairT, inst2_dB, ss]
      have hq : (lt (var 0) (succ (Syn.shift m)) :: C.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift p) :=
        le_trans Prf.hyp0 hle'.wk
      exact zero_mul_l ((AnalyticNumberTheory.Euler.congrEqb (fst_pair _ _) (.eqRefl _)).eqTrans
        (eqb_zero_of_gt hq)) _
    exact s1.wk.eqTrans (z.eqTrans (val_big hm.wk hle).eqSymm)

/-! ## The weight of a power -/

theorem succ_mul_alg (v L : PTm n) : Γ ⊢[PRAAx] v * L + L ≐ succ v * L := by
  apply deriveNat; ipra_simps; ring

/-- **`L_w(a^e) = e · L_w(a)`** for `a ≥ 1`. -/
theorem lw_pow (w : PTm 2) {a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (e y : PTm n) :
    Γ ⊢[PRAAx] Lw w (pw a e) y ≐ e * Lw w a y := by
  have ha' := shift_pos ha
  have hall : Γ ⊢[PRAAx] Fm.all (Lw w (pw (Syn.shift a) (var 0)) (Syn.shift y) ≐
      var 0 * Lw w (Syn.shift a) (Syn.shift y)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact (congrLw w _ (pw_zero _)).eqTrans ((lw_one w _).eqTrans (zero_mul _).eqSymm)
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine (congrLw w _ (pw_succ _ _)).eqTrans ((lw_mul w (pw_pos' ha'.wk _) ha'.wk).eqTrans ?_)
      exact (congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (succ_mul_alg _ _)
  have h2 := Prf.allE e hall
  simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact h2

end LeanProofs.IPRA.AnalyticNumberTheory.ValuationExt
