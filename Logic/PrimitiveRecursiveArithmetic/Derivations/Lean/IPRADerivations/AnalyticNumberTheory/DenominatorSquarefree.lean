import IPRADerivations.AnalyticNumberTheory.DenominatorSmooth
import IPRADerivations.AnalyticNumberTheory.SieveWeightOne

/-!
# The right endpoint of the denominator bound: `H_q(z) ≤ G_q(z)`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:radical-bound`
summed: "Summing over all possible radicals yields `H_q(z) ≤ G_q(z)`."

A divisor `d ≥ 1` of `A_q(z) = ∏_{p ≤ z, gcd(p, q) = 1} p` is coprime to `q` and squarefree, so its term
`⌊z!/φ(d)⌋` is a term of the denominator `A = z! G_q(z) = ∑_{r ≤ z} [gcd(r, q) = 1] μ(r)² z!/φ(r)` of the
finite sieve (`SieveWeightOne.Asum`, with `μ² = μ⁺ + μ⁻`).

* `cop_q`: `gcd(q, A_q(y)) = 1` for `q ≥ 1`; `cop_of_dvd`: a divisor of `A_q(z)` is coprime to `q`;
* `val_Aq_le`: `v_p(A_q(z)) ≤ 1`; `sq_zero_of_dvd`: a divisor of `A_q(z)` has no square prime factor;
* `bit_sum`, `mu_sum_one`: then `μ⁺(d) + μ⁻(d) = 1`;
* `term_le`, **`Gs_le_Asum`**: `∑_{d ≤ z} [d ∣ A_q(z)] ⌊z!/φ(d)⌋ ≤ z! G_q(z)`;
* **`Hq_le_Asum`**: `∑_{1 ≤ m ≤ z, gcd(m, q) = 1} ⌊z!/m⌋ ≤ z! G_q(z)`, that is `H_q(z) ≤ G_q(z)`.

The factor `q/φ(q)` between `H_z` and `H_q(z)` is not derived here.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DenominatorSquarefree

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd (val_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg congrEqb' zero_mul_l sq sqB inst2_sq om muP
  muN)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (PE XE inst2_XE val_PE)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues (YP YN YP_at YN_at)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (le_zero_of)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientTermStep (gt gt_zero gt_ndvd gt_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientSumStep (Gs GtB Gt_at)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorRange (P3 P3_z)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorModulus (Aq Aq_pos Aq_zero AqAppendsPrime Aq_step_cases)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorSmooth (sum_le2 Hq Hq_le_G)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Coprimality to `q` -/

alias mul_one_r := Common.mul_one_right

theorem cop_step {y q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (ih : Γ ⊢[PRAAx] gcd q (Aq y q) ≐ one) : Γ ⊢[PRAAx] gcd q (Aq (succ y) q) ≐ one := by
  refine .orE (Aq_step_cases y q) ?_ ?_
  · exact (congrGcd (.eqRefl _) Prf.hyp0).eqTrans ih.wk
  · have h : AqAppendsPrime y q :: Γ ⊢[PRAAx] AqAppendsPrime y q := Prf.hyp0
    have g1 := gcd_comm_one hq.wk h.andE₂.andE₂
    exact (congrGcd (.eqRefl _) h.andE₁).eqTrans (coprime_mul hq.wk ih.wk g1)

/-- Variables: `0 = y`, `1 = q`. -/
abbrev copF : Fm PTm 2 :=
  (var 1 ≐ succ (pred (var 1))) ⟶ (gcd (var 1) (ap2 (prodF (PE totBody)) (succ (var 0)) (var 1)) ≐ one)

theorem cop_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] copF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ex2, subst_ap2]
  · refine .impI ?_
    have hq : [(var 0 : PTm 1) ≐ succ (pred (var 0))] ⊢[PRAAx] (var 0 : PTm 1) ≐ succ (pred (var 0)) := Prf.hyp0
    exact (congrGcd (.eqRefl _) (Aq_zero (var 0))).eqTrans
      (eq_one_of_dvd_one (gcd_pos hq) (Prf.andE₂ (gcd_dvd' (b := one) hq)))
  · exact .impI (cop_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `gcd(q, A_q(y)) = 1` for `q ≥ 1`. -/
theorem cop_q {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (y : PTm n) :
    Γ ⊢[PRAAx] gcd q (Aq y q) ≐ one := by
  have i := inst (Γ := Γ) cop_open (![y, q] : Fin 2 → PTm n)
  simp only [copF, Fm.subst_imp, Fm.subst_eq, subst_ex2, subst_ap2, PTm.subst_pred, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at i
  exact .impE i hq

/-- A divisor `d ≥ 1` of `A_q(z)` is coprime to `q`. -/
theorem cop_of_dvd {d z q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (h : Γ ⊢[PRAAx] dvd d (Aq z q)) : Γ ⊢[PRAAx] gcd d q ≐ one :=
  coprime_dvd_left hd h (gcd_comm_one (Aq_pos z q) (cop_q hq z))

/-! ## Squarefreeness -/

theorem ones_alg : Γ ⊢[PRAAx] ((one : PTm n) * one) * one ≐ one := by ipra_ring

/-- `v_p(A_q(z)) ≤ 1` for a prime `p`. -/
theorem val_Aq_le {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (z q : PTm n) :
    Γ ⊢[PRAAx] le (val p (Aq z q)) one := by
  have e := val_PE hp totBody (succ z) q
  rw [inst2_XE, inst2_tot] at e
  exact le_congr e.eqSymm ones_alg
    (le_mul_mono (le_mul_mono (le_congr (isP_of_prime hp).eqSymm (.eqRefl _) (le_refl one)) (eqb_le_one _ _))
      (sg_le1 _))

theorem shift_dvd_Aq {d z q : PTm n} (h : Γ ⊢[PRAAx] dvd d (Aq z q)) :
    Γ.map Fm.shift ⊢[PRAAx] dvd (Syn.shift d) (Aq (Syn.shift z) (Syn.shift q)) := by
  simpa only [Syn.shift, subst_ap2, ConciseIPRA.PTm.subst_succ] using Gcd.shift_dvd h

/-- A divisor `d ≥ 1` of `A_q(z)` has no square prime factor. -/
theorem sq_zero_of_dvd {d z q : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (h : Γ ⊢[PRAAx] dvd d (Aq z q)) : Γ ⊢[PRAAx] sq (succ d) d ≐ zero := by
  have hd' := shift_pos hd
  have h' := shift_dvd_Aq h
  refine sum_zero_of_bounded sqB d (succ d) (.allI (.impI ?_))
  rw [inst2_sq]
  refine .orE (isP_01 (var 0)) ?_ ?_
  · exact zero_mul_l Prf.hyp0 _
  · have hp := prime_of_isP (Prf.hyp0 (Γ := lt (var 0) (Syn.shift (succ d)) :: Γ.map Fm.shift)
      (φ := isP (var 0) ≐ one))
    have l := le_trans (val_mono (prime_two hp) hd'.wk.wk (Aq_pos _ _) h'.wk.wk) (val_Aq_le hp _ _)
    exact (congrMul (.eqRefl _) ((congrSg l).eqTrans sg_zero)).eqTrans (mul_zero _)

/-- For `r < 2`: `[r = 0] + [r = 1] = 1`. -/
theorem bit_sum {r : PTm n} (h : Γ ⊢[PRAAx] lt r two) : Γ ⊢[PRAAx] eqb r zero + eqb r one ≐ one := by
  refine .orE (lt_succ_cases h) ?_ ?_
  · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := Γ) (φ := lt r one))) (lt_zero_absurd _ Prf.hyp0) ?_
    have h0 : ((r ≐ zero) :: lt r one :: Γ) ⊢[PRAAx] r ≐ zero := Prf.hyp0
    exact (congrAdd (eqb_of_eq h0) (eqb_zero_of_lt Prf.hyp1)).eqTrans (add_zero one)
  · have h1 : ((r ≐ one) :: Γ) ⊢[PRAAx] r ≐ one := Prf.hyp0
    have l : ((r ≐ one) :: Γ) ⊢[PRAAx] lt zero r := lt_congr (.eqRefl _) h1.eqSymm (le_refl one)
    exact (congrAdd (eqb_zero_of_gt l) (eqb_of_eq h1)).eqTrans (zero_add one)

theorem mu_alg {E e0 e1 : PTm n} (hE : Γ ⊢[PRAAx] E ≐ one) (hb : Γ ⊢[PRAAx] e0 + e1 ≐ one) :
    Γ ⊢[PRAAx] E * e0 + E * e1 ≐ one := by
  ipra_lc (𝔞 e0 + 𝔞 e1) * natEq hE + natEq hb

/-- `μ⁺(d) + μ⁻(d) = 1` when `d` has no square prime factor. -/
theorem mu_sum_one {d : PTm n} (hs : Γ ⊢[PRAAx] sq (succ d) d ≐ zero) :
    Γ ⊢[PRAAx] muP (succ d) d + muN (succ d) d ≐ one :=
  mu_alg (eqb_of_eq hs) (bit_sum (rem_lt' two_pos' (om (succ d) d)))

/-! ## The comparison with the denominator -/

theorem rhs_alg {c s mP mN Q' Q : PTm n} (hc : Γ ⊢[PRAAx] c ≐ one) (hs : Γ ⊢[PRAAx] s ≐ one)
    (hm : Γ ⊢[PRAAx] mP + mN ≐ one) (hQ : Γ ⊢[PRAAx] Q' ≐ Q) :
    Γ ⊢[PRAAx] c * ((s * mP) * Q') + c * ((s * mN) * Q') ≐ Q := by
  ipra_lc 𝔞 c * 𝔞 s * 𝔞 Q' * natEq hm + 𝔞 s * 𝔞 Q' * natEq hc + 𝔞 Q' * natEq hs + natEq hQ

/-- The term at `d`: `[d ∣ A_q(z)] ⌊z!/φ(d)⌋ ≤ Y⁺_d + Y⁻_d`. -/
theorem term_le {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (a z d : PTm n) :
    Γ ⊢[PRAAx] le (gt (Aq z q) (fact z) d) (inst2 YP d (P3 q a z) + inst2 YN d (P3 q a z)) := by
  rw [YP_at, YN_at]
  refine .orE (zero_or_succ d) ?_ ?_
  · exact le_zero_of (gt_zero Prf.hyp0)
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    refine .orE (eq_or_ne (rem (Aq z q) d) zero) ?_ ?_
    · let D : List (Fm PTm n) := (rem (Aq z q) d ≐ zero) :: C
      have h : D ⊢[PRAAx] dvd d (Aq z q) := Prf.hyp0
      have hc := cop_of_dvd hq.wk.wk hd.wk h
      have cb : D ⊢[PRAAx] eqb (gcd d (fstT (P3 q a z))) one ≐ one :=
        eqb_of_eq ((congrGcd (.eqRefl _) (fst_pair _ _)).eqTrans hc)
      have hQ : D ⊢[PRAAx] quo (fact (sndT (sndT (P3 q a z)))) (phi d) ≐ quo (fact z) (phi d) :=
        congrAp2 quoF (congrAp2 factF (P3_z q a z) (.eqRefl _)) (.eqRefl _)
      have ms := mu_sum_one (sq_zero_of_dvd hd.wk h)
      exact le_congr (gt_dvd hd.wk h).eqSymm
        (rhs_alg cb ((congrSg hd.wk).eqTrans (sg_succ _)) ms hQ).eqSymm (le_refl _)
    · exact le_zero_of (gt_ndvd Prf.hyp0)

/-- **`∑_{d ≤ z} [d ∣ A_q(z)] ⌊z!/φ(d)⌋ ≤ z! G_q(z)`**. -/
theorem Gs_le_Asum {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (a z : PTm n) :
    Γ ⊢[PRAAx] le (Gs (Aq z q) z (succ z)) (Asum (P3 q a z)) := by
  have hq' := shift_pos hq
  have ez : Γ ⊢[PRAAx] succ (sndT (sndT (P3 q a z))) ≐ succ z := congrSucc (P3_z q a z)
  have eA : Γ ⊢[PRAAx] Asum (P3 q a z) ≐ ap2 (sumF (addBody YP YN)) (succ z) (P3 q a z) :=
    (congrAdd (congrAp2 (sumF YP) ez (.eqRefl _)) (congrAp2 (sumF YN) ez (.eqRefl _))).eqTrans
      (sum_add YP YN (succ z) (P3 q a z)).eqSymm
  refine le_congr (.eqRefl _) eA.eqSymm ?_
  refine sum_le2 GtB (addBody YP YN) (pairT (Aq z q) z) (P3 q a z) (succ z) (.allI (.impI ?_))
  have s1 : Syn.shift (pairT (Aq z q) z) = pairT (Aq (Syn.shift z) (Syn.shift q)) (Syn.shift z) := by
    simp [Syn.shift]
  have s2 : Syn.shift (P3 q a z) = P3 (Syn.shift q) (Syn.shift a) (Syn.shift z) := by simp [Syn.shift]
  rw [s1, s2, inst2_addBody]
  exact le_congr (Gt_at _ _ _).eqSymm (.eqRefl _) (term_le hq'.wk _ _ _)

/-- **`H_q(z) ≤ G_q(z)`**, cleared by `z!`: `∑_{1 ≤ m ≤ z, gcd(m, q) = 1} ⌊z!/m⌋ ≤ z! G_q(z)`. -/
theorem Hq_le_Asum {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (a z : PTm n) :
    Γ ⊢[PRAAx] le (Hq q (fact z) (succ z)) (Asum (P3 q a z)) :=
  le_trans (Hq_le_G q z) (Gs_le_Asum hq a z)

end LeanProofs.IPRA.AnalyticNumberTheory.DenominatorSquarefree
