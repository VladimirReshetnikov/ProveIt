import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.LinearCombination

/-!
# Solutions of `φ(n) = 2`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-two`:
`φ(n) = 2 ⟺ n ∈ {3, 4, 6}`.

* `φ(3) = φ(4) = φ(6) = 2` (`phi_three`, `phi_four`, `phi_six`);
* conversely, write `n = 2^a m` with `m` odd (`Valuation`); for odd `m`, `φ(m)² ≥ m`
  (`PhiLower.phi_sq_odd`) bounds `m` when `φ(m) ∈ {1, 2}`, and `φ(n) = 2^{a−1} φ(m)` forces `a ≤ 2`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiTwo

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody coprime_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf lpf_dvd lpf_prime prime eq_succ_pred)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq' rem_lt' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos' phi_two odd_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiEvenPow (eq_one_of_lt_two)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (phi_one)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (phi_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (phi_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (prime_two phi_ppow phi_sq_odd)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev three : PTm n := succ two
abbrev four : PTm n := succ three
abbrev six : PTm n := succ (succ four)

/-! ## The values at `3`, `4`, `6` -/

theorem prime_three : Γ ⊢[PRAAx] prime (three : PTm n) := by
  have d := lpf_dvd (Γ := Γ) (one : PTm n)
  have l := two_le_lpf (Γ := Γ) (three : PTm n)
  refine prime_congr ?_ (lpf_prime one)
  refine .orE (lt_or_eq_of_le (Prf.andE₂ d)) ?_ Prf.hyp0
  -- `lpf 3 < 3` gives `lpf 3 = 2`, which does not divide `3`.
  have e : (lt (lpf three) three :: Γ) ⊢[PRAAx] lpf three ≐ two :=
    le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) l.wk
  have r : (lt (lpf three) three :: Γ) ⊢[PRAAx] rem three two ≐ one :=
    rem_eq' two_pos' (q := one) (by ipra_ring) (le_refl _)
  exact succ_ne_zero' _ (a := zero) (r.eqSymm.eqTrans ((congrAp2 remF (.eqRefl _) e).eqSymm.eqTrans (Prf.andE₁ d).wk))

theorem phi_three : Γ ⊢[PRAAx] phi (three : PTm n) ≐ two :=
  (phi_prime prime_three).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))

theorem phi_four : Γ ⊢[PRAAx] phi (four : PTm n) ≐ two := by
  have e : Γ ⊢[PRAAx] pw two (succ one) ≐ (four : PTm n) := by
    refine (pw_succ _ _).eqTrans ((congrMul (pw_one _) (.eqRefl _)).eqTrans ?_)
    ipra_ring
  refine (congrAp2 (sumF totBody) e e).eqSymm.eqTrans ((phi_ppow prime_two one).eqTrans ?_)
  refine (congrMul (pw_one _) ((succ_monus_succ _ _).eqTrans (monus_zero _))).eqTrans ?_
  ipra_ring

theorem phi_six : Γ ⊢[PRAAx] phi (six : PTm n) ≐ two := by
  have e : Γ ⊢[PRAAx] two * three ≐ (six : PTm n) := by ipra_ring
  have e₃ : Γ ⊢[PRAAx] two * one + one ≐ (three : PTm n) := by ipra_ring
  have hg := (DiophantineNumberTheory.QuarticStep.congrGcd (.eqRefl _) e₃.eqSymm).eqTrans (odd_cop (Γ := Γ) one)
  have h3 : Γ ⊢[PRAAx] (three : PTm n) ≐ succ (pred three) := congrSucc (pred_succ _).eqSymm
  refine (congrAp2 (sumF totBody) e e).eqSymm.eqTrans ((Multiplicative.phi_mul_at two_pos' h3 hg).eqTrans ?_)
  refine (congrMul phi_two phi_three).eqTrans ?_
  ipra_ring

/-! ## Small cases -/

theorem phi_congr' {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] phi a ≐ phi b := congrAp2 (sumF totBody) h h

theorem le4_cases {M : PTm n} (h : Γ ⊢[PRAAx] le M four) :
    Γ ⊢[PRAAx] (M ≐ zero) ⋎ ((M ≐ one) ⋎ ((M ≐ two) ⋎ ((M ≐ three) ⋎ (M ≐ four)))) := by
  refine .orE (lt_or_le M three) ?_ ?_
  · refine .orE (TotientCorollaries.lt3_cases Prf.hyp0) (.orI₁ Prf.hyp0) (.orE Prf.hyp0 ?_ ?_)
    · exact .orI₂ (.orI₁ Prf.hyp0)
    · exact .orI₂ (.orI₂ (.orI₁ Prf.hyp0))
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact .orI₂ (.orI₂ (.orI₂ (.orI₂ (le_antisymm h.wk.wk Prf.hyp0))))
    · exact .orI₂ (.orI₂ (.orI₂ (.orI₁ Prf.hyp0.eqSymm)))

theorem rem_two_even {k : PTm n} : Γ ⊢[PRAAx] rem (two * k) two ≐ zero :=
  rem_eq' two_pos' (q := k) (add_zero _).eqSymm (zero_lt' two_pos')

theorem odd_ne_even {M k : PTm n} (hodd : Γ ⊢[PRAAx] rem M two ≐ one) (h : Γ ⊢[PRAAx] M ≐ two * k) :
    Γ ⊢[PRAAx] Fm.bot :=
  succ_ne_zero (a := zero) (hodd.eqSymm.eqTrans ((congrAp2 remF h (.eqRefl _)).eqTrans rem_two_even))

/-- An odd `m` with `φ(m) = 2` is `3`. -/
theorem odd_phi2 {M : PTm n} (hodd : Γ ⊢[PRAAx] rem M two ≐ one) (h : Γ ⊢[PRAAx] phi M ≐ two) :
    Γ ⊢[PRAAx] M ≐ three := by
  have hle : Γ ⊢[PRAAx] le M four :=
    le_congr (.eqRefl _) ((congrMul h h).eqTrans (by ipra_ring)) (phi_sq_odd hodd)
  refine .orE (le4_cases hle) ?_ (.orE Prf.hyp0 ?_ (.orE Prf.hyp0 ?_ (.orE Prf.hyp0 Prf.hyp0 ?_)))
  · exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans ((phi_congr' Prf.hyp0).eqTrans phi_zero)))
  · exact .botE _ (succ_ne_zero (a := zero) ((pred_succ _).eqSymm.eqTrans
      ((congrPred (h.wk.wk.eqSymm.eqTrans ((phi_congr' Prf.hyp0).eqTrans phi_one))).eqTrans (pred_succ _))))
  · exact .botE _ (odd_ne_even (k := one) hodd.wk.wk.wk (Prf.hyp0.eqTrans (by ipra_ring)))
  · exact .botE _ (odd_ne_even (k := two) hodd.wk.wk.wk.wk (Prf.hyp0.eqTrans (by ipra_ring)))

/-- An odd `m` with `φ(m) = 1` is `1`. -/
theorem odd_phi1 {M : PTm n} (hodd : Γ ⊢[PRAAx] rem M two ≐ one) (h : Γ ⊢[PRAAx] phi M ≐ one) :
    Γ ⊢[PRAAx] M ≐ one := by
  have hle : Γ ⊢[PRAAx] le M one :=
    le_congr (.eqRefl _) ((congrMul h h).eqTrans (by ipra_ring)) (phi_sq_odd hodd)
  refine .orE (lt_or_eq_of_le hle) ?_ Prf.hyp0
  have z : (lt M one :: Γ) ⊢[PRAAx] M ≐ zero := (monus_zero _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  exact .botE _ (odd_ne_even (k := zero) hodd.wk (z.eqTrans (mul_zero _).eqSymm))

/-! ## The even case -/

section Even

variable {N M k : PTm n} (hNe : Γ ⊢[PRAAx] N ≐ pw two (succ k) * M) (hmo : Γ ⊢[PRAAx] rem M two ≐ one)
  (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hφ : Γ ⊢[PRAAx] two ≐ pw two k * phi M)
include hNe hmo hM hφ

omit hM in
theorem leaf_k0 (hk : Γ ⊢[PRAAx] k ≐ zero) : Γ ⊢[PRAAx] N ≐ six := by
  have hp : Γ ⊢[PRAAx] pw two k ≐ one := (congrAp2 powF hk (.eqRefl _)).eqTrans (pw_zero _)
  have hm2 : Γ ⊢[PRAAx] phi M ≐ two := (one_mul _).eqSymm.eqTrans ((congrMul hp (.eqRefl _)).eqSymm.eqTrans hφ.eqSymm)
  have h3 := odd_phi2 hmo hm2
  have hk' : Γ ⊢[PRAAx] pw two (succ k) ≐ two := (congrAp2 powF (congrSucc hk) (.eqRefl _)).eqTrans (pw_one _)
  exact hNe.eqTrans ((congrMul hk' h3).eqTrans (by ipra_ring))

omit hM in
theorem leaf_k1 (hk : Γ ⊢[PRAAx] k ≐ one) : Γ ⊢[PRAAx] N ≐ four := by
  have hp : Γ ⊢[PRAAx] pw two k ≐ two := (congrAp2 powF hk (.eqRefl _)).eqTrans (pw_one _)
  have h1 : Γ ⊢[PRAAx] phi M ≐ one := by
    refine (mul_cancel two_pos' ?_).eqSymm
    exact (by ipra_ring : Γ ⊢[PRAAx] two * one ≐ two).eqTrans
      (hφ.eqTrans (congrMul hp (.eqRefl _)))
  have m1 := odd_phi1 hmo h1
  have hk' : Γ ⊢[PRAAx] pw two (succ k) ≐ pw two (succ one) := congrAp2 powF (congrSucc hk) (.eqRefl _)
  refine hNe.eqTrans ((congrMul (hk'.eqTrans ((pw_succ _ _).eqTrans (congrMul (pw_one _) (.eqRefl _)))) m1).eqTrans ?_)
  ipra_ring

omit hNe in
theorem leaf_k2 {i : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (succ i)) : Γ ⊢[PRAAx] Fm.bot := by
  -- `φ(m) ≥ 1`.
  have hφm : Γ ⊢[PRAAx] phi M ≐ succ (pred (phi M)) := by
    refine .orE (zero_or_succ (phi M)) ?_ Prf.hyp0
    have l := le_congr (.eqRefl _) ((congrMul Prf.hyp0 Prf.hyp0).eqTrans (mul_zero _)) (phi_sq_odd hmo.wk)
    exact succ_ne_zero' _ (hM.wk.eqSymm.eqTrans ((monus_zero _).eqSymm.eqTrans l))
  have hu := pos_mul (pw_pos' two_pos' i) hφm
  have e₂ := natEq ((congrAp2 powF hk (.eqRefl two)).eqTrans ((pw_succ _ _).eqTrans
    (congrMul (pw_succ _ _) (.eqRefl _))))
  refine succ_ne_zero (a := succ (four * pred (pw two i * phi M))) ?_
  ipra_lc -natEq hφ - Groth.ι (Q.mk _ (phi M)) * e₂ - 4 * natEq hu

end Even

/-! ## The classification -/

theorem phi_two_even {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (h : Γ ⊢[PRAAx] phi N ≐ two)
    (ha : Γ ⊢[PRAAx] val two N ≐ succ (pred (val two N))) :
    Γ ⊢[PRAAx] (N ≐ three) ⋎ ((N ≐ four) ⋎ (N ≐ six)) := by
  have h2 : Γ ⊢[PRAAx] le two (two : PTm n) := le_refl _
  have hNe0 := cof_eq (m := N) h2
  have hmo := eq_one_of_lt_two (rem_lt' two_pos' _) (cof_not_dvd h2 hN)
  have hM : Γ ⊢[PRAAx] quo N (pw two (val two N)) ≐ succ (pred (quo N (pw two (val two N)))) := by
    refine .orE (zero_or_succ (quo N (pw two (val two N)))) ?_ Prf.hyp0
    exact succ_ne_zero' _ (hN.wk.eqSymm.eqTrans (hNe0.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))))
  have hP := pw_val_pos (m := N) h2
  have g₁ := gcd_prime prime_two (cof_not_dvd h2 hN)
  have hg := gcd_comm_one hP (coprime_pow hM (gcd_comm_one hM g₁) (val two N))
  have hmul := (phi_congr' hNe0).eqTrans (Multiplicative.phi_mul_at hP hM hg)
  have e₂ : Γ ⊢[PRAAx] pw two (succ (pred (val two N))) ≐ pw two (val two N) := congrAp2 powF ha.eqSymm (.eqRefl _)
  have hφP := (phi_congr' e₂).eqSymm.eqTrans (phi_ppow prime_two (pred (val two N)))
  have hs : Γ ⊢[PRAAx] monus two one ≐ (one : PTm n) := (succ_monus_succ _ _).eqTrans (monus_zero _)
  have hφ : Γ ⊢[PRAAx] two ≐ pw two (pred (val two N)) * phi (quo N (pw two (val two N))) :=
    h.eqSymm.eqTrans (hmul.eqTrans (congrMul (hφP.eqTrans ((congrMul (.eqRefl _) hs).eqTrans
      (EulerProduct.mul_one' _))) (.eqRefl _)))
  have hNe := hNe0.eqTrans (congrMul e₂.eqSymm (.eqRefl _))
  refine .orE (zero_or_succ (pred (val two N))) ?_ ?_
  · exact .orI₂ (.orI₂ (leaf_k0 hNe.wk hmo.wk hφ.wk Prf.hyp0))
  refine .orE (zero_or_succ (pred (pred (val two N)))) ?_ ?_
  · exact .orI₂ (.orI₁ (leaf_k1 hNe.wk.wk hmo.wk.wk hφ.wk.wk (Prf.hyp1.eqTrans (congrSucc Prf.hyp0))))
  · exact .botE _ (leaf_k2 hmo.wk.wk hM.wk.wk hφ.wk.wk (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))

/-- `thm:phi-two` (forward) at an arbitrary `n`. -/
theorem phi_two_inv {N : PTm n} (h : Γ ⊢[PRAAx] phi N ≐ two) :
    Γ ⊢[PRAAx] (N ≐ three) ⋎ ((N ≐ four) ⋎ (N ≐ six)) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans ((phi_congr' Prf.hyp0).eqTrans phi_zero)))
  have hN : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
  refine .orE (zero_or_succ (val two N)) ?_ (phi_two_even hN.wk h.wk.wk Prf.hyp0)
  have h2 : ((val two N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] le two (two : PTm n) := le_refl _
  have hNe0 := cof_eq (m := N) h2
  have hmo := eq_one_of_lt_two (rem_lt' two_pos' _) (cof_not_dvd h2 hN.wk)
  have e : ((val two N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ quo N (pw two (val two N)) :=
    hNe0.eqTrans ((congrMul ((congrAp2 powF Prf.hyp0 (.eqRefl _)).eqTrans (pw_zero _)) (.eqRefl _)).eqTrans (one_mul _))
  exact .orI₁ (odd_phi2 ((congrAp2 remF e (.eqRefl _)).eqTrans hmo) h.wk.wk)

/-- `thm:phi-two` (values): `φ(3) = φ(4) = φ(6) = 2`. -/
theorem phi_two_values :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] (phi three ≐ two) ⋏ ((phi four ≐ two) ⋏ (phi six ≐ two)) :=
  .andI phi_three (.andI phi_four phi_six)

/-- `thm:phi-two` (classification): `φ(n) = 2 → n ∈ {3, 4, 6}`. -/
abbrev phiTwoFormula : Fm PTm 1 := (phi (var 0) ≐ two) ⟶ ((var 0 ≐ three) ⋎ ((var 0 ≐ four) ⋎ (var 0 ≐ six)))

theorem phi_two_classification : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiTwoFormula :=
  closeUniv 1 (.impI (phi_two_inv Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiTwo
