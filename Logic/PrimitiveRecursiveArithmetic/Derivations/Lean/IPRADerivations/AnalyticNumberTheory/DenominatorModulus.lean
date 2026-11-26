import IPRADerivations.AnalyticNumberTheory.DenominatorRange
import IPRADerivations.AnalyticNumberTheory.BinomialLcm
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Probability.ProductReplacement
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The comparison `S ≤ G` for the product of the primes coprime to `q`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the proof of the
denominator bound `eq:sieve-denominator`: "Summing `eq:radical-bound` over all possible radicals yields
`H_q(z) ≤ G_q(z)`."

The modulus is the product of the primes up to `y` that do not divide `q`:

    A_q(y) = ∏_{p ≤ y, p prime, gcd(p, q) = 1} p                                   (`Aq`).

* `Aq_succ`, `Aq_zero`, `Aq_pos`; `cop_next`: a prime `y + 1` is coprime to `A_q(y)` (its valuation in
  `A_q(y)` is `0`, `BinomialLcm.val_PE`);
* `Cz_one`: the base `C_z(1) = 0`: `S_1(t) ≤ z! ≤ G_1(t)` for `t ≥ 1` (`EulerDomination.base_le`);
* `out_step`, `out_open`, **`Cz_all`**: `C_z(A_q(y)) = 0` for every `y`, by induction on `y` with
  `DenominatorRange.range_step` at the primes `y + 1` coprime to `q`;
* **`smooth_le_totient`**: for every `y` and `t ≤ z`,
  `∑_{1 ≤ m ≤ t} [m ∣ A_q(y)^L] ⌊z!/m⌋ ≤ ∑_{1 ≤ d ≤ t} [d ∣ A_q(y)] ⌊z!/φ(d)⌋`.

At `y = t = z` the left side contains every `m ≤ z` coprime to `q` (for `L` large) and the right side is the
sum over the squarefree `d ≤ z` coprime to `q`; these two identifications and the factor `q/φ(q)` are not
derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DenominatorModulus

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP val_not_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (f_zero f_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg isP_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (PE XE inst2_PE inst2_XE PE_pos val_PE)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (phi_one)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (quo_one)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (Sm gB base_le le_zero_of)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientTermStep (gt gt_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientSumStep (Gs GtB Gt_at)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorRange (VaB Cz P3 Va_at le_of_Cz range_step S_zero)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_self')
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.Probability.ProductReplacement (prod_succ')
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The modulus -/

/-- `A_q(y) = ∏_{p ≤ y} p^{[p prime][gcd(p, q) = 1]}`. -/
abbrev Aq (y q : PTm n) : PTm n := ap2 (prodF (PE totBody)) (succ y) q

theorem fac_at (i q : PTm n) : inst2 (PE totBody) i q = pw i (isP i * eqb (gcd i q) one) := by
  rw [inst2_PE, inst2_XE, inst2_tot]

theorem Aq_pos (y q : PTm n) : Γ ⊢[PRAAx] Aq y q ≐ succ (pred (Aq y q)) := PE_pos _ _ _

theorem Aq_succ (y q : PTm n) :
    Γ ⊢[PRAAx] Aq (succ y) q ≐ Aq y q * pw (succ y) (isP (succ y) * eqb (gcd (succ y) q) one) := by
  have e := prod_succ' (Γ := Γ) (PE totBody) (succ y) q
  rw [fac_at] at e
  exact e

/-- A growing prefix step records the new prime and its gcd certificate. -/
abbrev AqAppendsPrime (y q : PTm n) : Fm PTm n :=
  (Aq (succ y) q ≐ Aq y q * succ y) ⋏ prime (succ y) ⋏ (gcd (succ y) q ≐ one)

/-- The modulus either stays unchanged or appends the next prime coprime to `q`. -/
theorem Aq_step_cases (y q : PTm n) : Γ ⊢[PRAAx] (Aq (succ y) q ≐ Aq y q) ⋎ AqAppendsPrime y q := by
  have next := Aq_succ (Γ := Γ) y q
  refine .orE (isP_01 (succ y)) ?_ ?_
  · exact .orI₁ (next.wk.eqTrans ((congrMul (.eqRefl _) (f_zero Prf.hyp0)).eqTrans (Common.mul_one_right _)))
  · let Δ := (isP (succ y) ≐ one) :: Γ
    let bit := eqb (gcd (succ y) q) one
    have accepted : Δ ⊢[PRAAx] isP (succ y) ≐ one := Prf.hyp0
    have factor := next.wk.eqTrans (congrMul (.eqRefl _) (f_one accepted))
    refine .orE (eqb_cases (gcd (succ y) q) one) ?_ ?_
    · have h : (bit ≐ zero) :: Δ ⊢[PRAAx] bit ≐ zero := Prf.hyp0
      have excluded := (congrPw (.eqRefl (succ y)) h).eqTrans (pw_zero (succ y))
      exact .orI₁ (factor.wk.eqTrans ((congrMul (.eqRefl _) excluded).eqTrans (Common.mul_one_right _)))
    · have h : (bit ≐ one) :: Δ ⊢[PRAAx] bit ≐ one := Prf.hyp0
      have included := (congrPw (.eqRefl (succ y)) h).eqTrans (pw_one (succ y))
      exact .orI₂ (.andI (factor.wk.eqTrans (congrMul (.eqRefl _) included))
        (.andI (prime_of_isP accepted.wk) (eq_of_eqb h)))

theorem Aq_zero (q : PTm n) : Γ ⊢[PRAAx] Aq zero q ≐ one := by
  have e := prod_succ' (Γ := Γ) (PE totBody) zero q
  rw [fac_at] at e
  exact e.eqTrans ((congrMul (prod_zero _ _) (f_zero isP_zero)).eqTrans (one_mul _))

/-- A prime `y + 1` is coprime to `A_q(y)`. -/
theorem cop_next {y q : PTm n} (hp : Γ ⊢[PRAAx] prime (succ y)) :
    Γ ⊢[PRAAx] gcd (succ y) (Aq y q) ≐ one := by
  have hp2 := prime_two hp
  have v : Γ ⊢[PRAAx] val (succ y) (Aq y q) ≐ zero :=
    (val_PE hp totBody (succ y) q).eqTrans
      ((congrMul (.eqRefl _) ((congrSg (monus_self (succ y))).eqTrans sg_zero)).eqTrans (mul_zero _))
  have h := val_not_dvd (p := succ y) (m := Aq y q) hp2 (Aq_pos y q)
  refine gcd_prime hp (.impI (.impE h.wk ?_))
  exact (congrAp2 remF (.eqRefl _) ((congrPw (.eqRefl _) (congrSucc v.wk)).eqTrans (pw_one _))).eqTrans Prf.hyp0

/-! ## The base -/

theorem Cz_congr {a a' L z : PTm n} (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] Cz a L z ≐ Cz a' L z :=
  congrAp2 (sumF VaB) (.eqRefl _) (congrPairT h (.eqRefl _))

/-- `z! ≤ G_1(t)` for `t ≥ 1`. -/
theorem G_one_ge (z j : PTm n) : Γ ⊢[PRAAx] le (fact z) (Gs one z (succ (succ j))) := by
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  have lt1 : Γ ⊢[PRAAx] lt (one : PTm n) (succ (succ j)) :=
    (succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus j))
  have t := term_le_sum GtB (x := pairT one z) lt1
  have e : Γ ⊢[PRAAx] inst2 GtB one (pairT one z) ≐ fact z :=
    (Gt_at one one z).eqTrans ((gt_dvd h1 (dvd_self' h1)).eqTrans
      ((congrAp2 quoF (.eqRefl _) phi_one).eqTrans (quo_one _)))
  exact le_congr e (.eqRefl _) t

theorem base_le' (L z t : PTm n) : Γ ⊢[PRAAx] le (Sm one L (fact z) (succ t)) (Gs one z (succ t)) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · have h0 : ((t ≐ zero) :: Γ) ⊢[PRAAx] t ≐ zero := Prf.hyp0
    exact le_zero_of ((congrAp2 (sumF gB) (congrSucc h0) (.eqRefl _)).eqTrans (S_zero _ _ _))
  · have ht : ((t ≐ succ (pred t)) :: Γ) ⊢[PRAAx] t ≐ succ (pred t) := Prf.hyp0
    have g := G_one_ge (Γ := (t ≐ succ (pred t)) :: Γ) z (pred t)
    exact le_trans (base_le L (fact z) (succ t))
      (le_congr (.eqRefl _) (congrAp2 (sumF GtB) (congrSucc ht.eqSymm) (.eqRefl _)) g)

/-- `C_z(1) = 0`. -/
theorem Cz_one (L z : PTm n) : Γ ⊢[PRAAx] Cz one L z ≐ zero := by
  refine sum_zero_of_bounded VaB (P3 one L z) (succ z) (.allI (.impI ?_))
  have sz : Syn.shift (P3 (one : PTm n) L z) = P3 one (Syn.shift L) (Syn.shift z) := by simp [Syn.shift]
  rw [sz]
  exact (Va_at _ _ _ _).eqTrans (base_le' _ _ _)

/-! ## The induction over the primes -/

alias mul_one_r := Common.mul_one_right

theorem out_step {y q L z : PTm n} (ih : Γ ⊢[PRAAx] Cz (Aq y q) L z ≐ zero) :
    Γ ⊢[PRAAx] Cz (Aq (succ y) q) L z ≐ zero := by
  refine .orE (Aq_step_cases y q) ?_ ?_
  · exact (Cz_congr Prf.hyp0).eqTrans ih.wk
  · have h : AqAppendsPrime y q :: Γ ⊢[PRAAx] AqAppendsPrime y q := Prf.hyp0
    have hp := h.andE₂.andE₁
    exact (Cz_congr h.andE₁).eqTrans (range_step hp (cop_next hp) ih.wk)

/-- Variables: `0 = y`, `1 = q`, `2 = L`, `3 = z`. -/
abbrev outF : Fm PTm 4 :=
  ap2 (sumF VaB) (succ (var 3))
    (pairT (ap2 (prodF (PE totBody)) (succ (var 0)) (var 1)) (pairT (var 2) (var 3))) ≐ zero

theorem out_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] outF := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact (Cz_congr (Aq_zero _)).eqTrans (Cz_one _ _)
  · exact out_step Prf.hyp0

/-- **No violation for `A_q(y)`**: `C_z(A_q(y)) = 0` for every `y`, `q`, `L`, `z`. -/
theorem Cz_all (y q L z : PTm n) : Γ ⊢[PRAAx] Cz (Aq y q) L z ≐ zero := by
  have i := inst (Γ := Γ) out_open (![y, q, L, z] : Fin 4 → PTm n)
  simp only [outF, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact i

/-- **The smooth sum is at most the totient sum**: for every `y` and `t ≤ z`,
`S_{A_q(y)}(t) ≤ G_{A_q(y)}(t)`. -/
theorem smooth_le_totient (y q L : PTm n) {z t : PTm n} (ht : Γ ⊢[PRAAx] le t z) :
    Γ ⊢[PRAAx] le (Sm (Aq y q) L (fact z) (succ t)) (Gs (Aq y q) z (succ t)) :=
  le_of_Cz (Cz_all y q L z) ht

end LeanProofs.IPRA.AnalyticNumberTheory.DenominatorModulus
