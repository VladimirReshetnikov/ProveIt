import IPRADerivations.AnalyticNumberTheory.BertrandCentral
import IPRADerivations.AnalyticNumberTheory.PrimorialLower
import IPRADerivations.Foundations.StrongInduction

/-!
# Bertrand's postulate: the product of the primes up to `r` is at most `4^r`

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex`, §"A uniform bound for a product of distinct
primes", the estimate (6): `P(r) = ∏_{p ≤ r} p ≤ 4^r`.

`pri r = ∏_{i ≤ r} i^{[i prime]}` is the product of the primes up to `r` (the term `PrimorialLower.prim` with
its unused parameter fixed; `prim_eq`).

* `val_pri`: `v_q(pri r) = [q ≤ r]` for a prime `q`;
* `val_odd_pos`: a prime `q` with `k + 1 < q ≤ 2k + 2` divides `C(2k + 1, k)` (`k ≥ 1`): it divides
  `C(2k + 2, k + 1) = 2 C(2k + 1, k)` by `BinomialLcm.binom_val_ge`, and `q ≠ 2`;
* `pri_dvd`: `pri (2k + 2) ∣ pri (k + 1) · C(2k + 1, k)` for `k ≥ 1`, by comparing the valuations at every prime
  (`BinomialLcm.dvd_of_val_le`); no product is split and no prime is extracted;
* `pri_step`: `pri (2k + 2) ≤ pri (k + 1) · 4^k`, with `BertrandCentral.odd_binom_le`;
* `pri_le` (the estimate (6)): `pri r ≤ 4^r`, by strong induction (`Foundations/StrongInduction.strong_ind`)
  with the violation `pri r ∸ 4^r`: for `r ≥ 3` put `m = ⌊(r + 1)/2⌋`, so that `r ≤ 2m ≤ r + 1`, `2 ≤ m < r`,
  and `pri r ≤ pri (2m) ≤ pri m · 4^{m−1} ≤ 4^{2m−1} ≤ 4^r`;
* `primorial_le`: the same bound for `PrimorialLower.prim`.

The paper treats even and odd `r` separately (`P(2a) = P(2a − 1)`); here both are covered by the one
divisibility `pri_dvd` at the even argument `2m`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimorialUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (f_zero f_one f_pos one_le_pos two_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu lcm_valuation)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (dvd_of_val_le PE XE val_PE inst2_XE inst2_PE PE_pos
  binom_val_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialLower (prim inst2_one)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg isP_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos val_mul val_unique val_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandCentral (cb_succ_odd odd_binom_le odd_binom_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le')
open LeanProofs.IPRA.Combinatorics.Catalan (cb)
open LeanProofs.IPRA.Combinatorics.Binomial (binom pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Probability.ProductReplacement (prod_succ')
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The product of the primes up to `r` -/

/-- `∏_{p ≤ r, p prime} p = ∏_{i ≤ r} i^{[i prime]}`. -/
abbrev pri (r : PTm n) : PTm n := ap2 (prodF (PE one)) (succ r) zero

theorem fac_at (i x : PTm n) : inst2 (PE one) i x = pw i (isP i * one) := by
  rw [inst2_PE, inst2_XE, inst2_one]

theorem pri_pos (r : PTm n) : Γ ⊢[PRAAx] pri r ≐ succ (pred (pri r)) := PE_pos _ _ _

theorem congrPri {r r' : PTm n} (h : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx] pri r ≐ pri r' :=
  congrAp2 _ (congrSucc h) (.eqRefl _)

theorem pri_succ (r : PTm n) : Γ ⊢[PRAAx] pri (succ r) ≐ pri r * pw (succ r) (isP (succ r) * one) := by
  have e := prod_succ' (Γ := Γ) (PE one) (succ r) zero
  rw [fac_at] at e
  exact e

theorem pri_zero : Γ ⊢[PRAAx] pri (zero : PTm n) ≐ one := by
  have e := prod_succ' (Γ := Γ) (PE one) zero zero
  rw [fac_at] at e
  exact e.eqTrans ((congrMul (prod_zero _ _) (f_zero isP_zero)).eqTrans (one_mul _))

theorem one_le_succ (i : PTm n) : Γ ⊢[PRAAx] le one (succ i) :=
  le_of_eq_add (d := i) (by apply deriveNat; ipra_simps; ring)

theorem mul_one1 (X : PTm n) : Γ ⊢[PRAAx] X * one ≐ X := by apply deriveNat; ipra_simps; ring

/-- The factor at `i + 1` is at most `i + 1`. -/
theorem fac_le (i : PTm n) : Γ ⊢[PRAAx] le (pw (succ i) (isP (succ i) * one)) (succ i) := by
  refine .orE (isP_01 (succ i)) ?_ ?_
  · exact le_congr (f_zero Prf.hyp0).eqSymm (.eqRefl _) (one_le_succ i)
  · exact le_congr ((f_one Prf.hyp0).eqTrans (pw_one _)).eqSymm (.eqRefl _) (le_refl _)

theorem pri_step_le (r : PTm n) : Γ ⊢[PRAAx] le (pri (succ r)) (pri r * succ r) :=
  le_congr (pri_succ r).eqSymm (.eqRefl _) (le_mul_mono (le_refl _) (fac_le r))

theorem pri_mono_succ (r : PTm n) : Γ ⊢[PRAAx] le (pri r) (pri (succ r)) :=
  le_congr (mul_one1 _) (pri_succ r).eqSymm (le_mul_mono (le_refl (pri r)) (one_le_pos (f_pos (succ r) one)))

/-! ## Valuations -/

/-- `v_q(∏_{p ≤ r} p) = [q ≤ r]` for a prime `q`. -/
theorem val_pri {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (r : PTm n) :
    Γ ⊢[PRAAx] val q (pri r) ≐ sg (monus (succ r) q) := by
  have e := val_PE hq one (succ r) (zero : PTm n)
  rw [inst2_XE, inst2_one] at e
  exact e.eqTrans ((congrMul ((congrMul (isP_of_prime hq) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)).eqTrans
    (one_mul _))

theorem sg_le1 (t : PTm n) : Γ ⊢[PRAAx] le (sg t) one := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact le_congr ((congrSg Prf.hyp0).eqTrans sg_zero).eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr ((congrSg Prf.hyp0).eqTrans (sg_succ _)).eqSymm (.eqRefl _) (le_refl _)

/-- A prime `q > 2` does not divide `2`. -/
theorem val_two_zero {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h : Γ ⊢[PRAAx] lt two q) :
    Γ ⊢[PRAAx] val q two ≐ zero := by
  have hq2 := prime_two hq
  refine val_unique hq2 two_pos' (c := two)
    ((one_mul _).eqSymm.eqTrans (congrMul (pw_zero _).eqSymm (.eqRefl two))) ?_
  exact .impI (le_lt_absurd _ (dvd_le' (p_pos hq2).wk Prf.hyp0 two_pos') h.wk)

/-- A prime `q` with `k + 1 < q ≤ 2k + 2` divides `C(2k + 1, k)`, for `k = j + 1`. -/
theorem val_odd_pos {q j : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h1 : Γ ⊢[PRAAx] lt (succ (succ j)) q)
    (h2 : Γ ⊢[PRAAx] le q (two * succ (succ j))) :
    Γ ⊢[PRAAx] le one (val q (binom (succ (two * succ j)) (succ j))) := by
  have hq2 := prime_two hq
  have qpos := p_pos hq2
  have g := binom_val_ge hq h2
  have I2 := Prf.andE₂ (lcm_valuation hq (two * succ (succ j)))
  have big : Γ ⊢[PRAAx] lt (succ (succ j)) (pw q (val q (lcmu (two * succ (succ j))))) := by
    refine .orE (zero_or_succ (val q (lcmu (two * succ (succ j))))) ?_ ?_
    · have e0 : ((val q (lcmu (two * succ (succ j))) ≐ zero) :: Γ) ⊢[PRAAx]
          pw q (succ (val q (lcmu (two * succ (succ j))))) ≐ q :=
        (congrPw (.eqRefl _) (congrSucc Prf.hyp0)).eqTrans (pw_one q)
      exact le_lt_absurd _ h2.wk (le_congr (.eqRefl _) e0 I2.wk)
    · have ge : ((val q (lcmu (two * succ (succ j))) ≐ succ (pred (val q (lcmu (two * succ (succ j)))))) :: Γ)
          ⊢[PRAAx] le q (pw q (val q (lcmu (two * succ (succ j))))) :=
        le_congr qpos.wk.eqSymm (congrPw qpos.wk.eqSymm Prf.hyp0.eqSymm) (le_self_pw (pred q) _)
      exact lt_of_lt_of_le h1.wk ge
  have v1 : Γ ⊢[PRAAx] le one (val q (cb (succ (succ j)))) := le_congr (sg_lt big) (.eqRefl _) g
  have l2 : Γ ⊢[PRAAx] le two (succ (succ j)) := le_of_eq_add (d := j) (by apply deriveNat; ipra_simps; ring)
  have vm := (val_congr q (cb_succ_odd (Γ := Γ) (succ j))).eqTrans (val_mul hq two_pos' (odd_binom_pos (succ j)))
  have vz := val_two_zero hq (lt_of_le_of_lt l2 h1)
  exact le_congr (.eqRefl _) (vm.eqTrans ((congrAdd vz (.eqRefl _)).eqTrans (zero_add _))) v1

/-- `v_q(pri (2k + 2)) ≤ v_q(pri (k + 1) · C(2k + 1, k))` for a prime `q` and `k = j + 1`. -/
theorem val_step {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (j : PTm n) :
    Γ ⊢[PRAAx] le (val q (pri (two * succ (succ j))))
      (val q (pri (succ (succ j)) * binom (succ (two * succ j)) (succ j))) := by
  have vl := val_pri hq (two * succ (succ j))
  have vr := (val_mul hq (pri_pos (succ (succ j))) (odd_binom_pos (succ j))).eqTrans
    (congrAdd (val_pri hq (succ (succ j))) (.eqRefl _))
  refine le_congr vl.eqSymm vr.eqSymm ?_
  refine .orE (lt_or_le (succ (succ j)) q) ?_ ?_
  · refine .orE (lt_or_le (two * succ (succ j)) q) ?_ ?_
    · exact le_congr (sg_le (a := succ (two * succ (succ j))) (b := q) Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
    · have v := val_odd_pos (Γ := le q (two * succ (succ j)) :: lt (succ (succ j)) q :: Γ) (j := j)
        hq.wk.wk Prf.hyp1 Prf.hyp0
      exact le_trans (sg_le1 _) (le_trans v (le_add_left _ _))
  · have s := sg_lt (a := q) (b := succ (succ (succ j)))
      ((succ_monus_succ _ _).eqTrans (Prf.hyp0 (Γ := Γ) (φ := le q (succ (succ j)))))
    exact le_trans (sg_le1 _) (le_congr (.eqRefl _) (congrAdd s.eqSymm (.eqRefl _)) (le_add_right one _))

/-! ## The divisibility and the step of the induction -/

theorem lt_succ_add_l (a b : PTm n) : Γ ⊢[PRAAx] lt a (succ (a + b)) :=
  le_of_eq_add (d := b) (by apply deriveNat; ipra_simps; ring)

theorem lt_succ_add_r (a b : PTm n) : Γ ⊢[PRAAx] lt b (succ (a + b)) :=
  le_of_eq_add (d := a) (by apply deriveNat; ipra_simps; ring)

/-- `∏_{p ≤ 2k+2} p ∣ ∏_{p ≤ k+1} p · C(2k + 1, k)` for `k = j + 1`. -/
theorem pri_dvd (j : PTm n) : Γ ⊢[PRAAx]
    dvd (pri (two * succ (succ j))) (pri (succ (succ j)) * binom (succ (two * succ j)) (succ j)) := by
  have hb := pos_mul (pri_pos (Γ := Γ) (succ (succ j))) (odd_binom_pos (succ j))
  refine dvd_of_val_le
    (N := succ (pri (two * succ (succ j)) + pri (succ (succ j)) * binom (succ (two * succ j)) (succ j)))
    (pri_pos _) hb (lt_succ_add_l _ _) (lt_succ_add_r _ _) (.allI (.impI (.impI ?_)))
  have sa : Syn.shift (pri (two * succ (succ j))) = pri (two * succ (succ (Syn.shift j))) := by
    simp [Syn.shift]
  have sb : Syn.shift (pri (succ (succ j)) * binom (succ (two * succ j)) (succ j)) =
      pri (succ (succ (Syn.shift j))) * binom (succ (two * succ (Syn.shift j))) (succ (Syn.shift j)) := by
    simp [Syn.shift]
  rw [sa, sb]
  exact val_step (prime_of_isP Prf.hyp0) (Syn.shift j)

/-- `∏_{p ≤ 2k+2} p ≤ ∏_{p ≤ k+1} p · 4^k` for `k = j + 1`. -/
theorem pri_step (j : PTm n) : Γ ⊢[PRAAx]
    le (pri (two * succ (succ j))) (pri (succ (succ j)) * pw two (two * succ j)) :=
  le_trans (dvd_le' (pri_pos _) (pri_dvd j) (pos_mul (pri_pos (succ (succ j))) (odd_binom_pos (succ j))))
    (le_mul_mono (le_refl _) (odd_binom_le (succ j)))

/-! ## The small cases -/

theorem one_le_four (k : PTm n) : Γ ⊢[PRAAx] le one (pw two (two * k)) := one_le_pos (pw_pos' two_pos' _)

theorem pri_le_zero : Γ ⊢[PRAAx] le (pri (zero : PTm n)) (pw two (two * zero)) :=
  le_congr pri_zero.eqSymm (.eqRefl _) (one_le_four zero)

theorem pri_one_le : Γ ⊢[PRAAx] le (pri (one : PTm n)) one :=
  le_congr (.eqRefl _) ((congrMul pri_zero (.eqRefl _)).eqTrans (one_mul one)) (pri_step_le zero)

theorem pri_le_one : Γ ⊢[PRAAx] le (pri (one : PTm n)) (pw two (two * one)) :=
  le_trans pri_one_le (one_le_four one)

theorem pri_two_le : Γ ⊢[PRAAx] le (pri (two : PTm n)) two :=
  le_trans (pri_step_le one) (le_congr (.eqRefl _) (one_mul two) (mul_le_mul_right two pri_one_le))

theorem pri_le_two : Γ ⊢[PRAAx] le (pri (two : PTm n)) (pw two (two * two)) := by
  have h : Γ ⊢[PRAAx] le (one : PTm n) (two * two) :=
    le_of_eq_add (d := succ two) (by apply deriveNat; ipra_simps; ring)
  exact le_trans pri_two_le (le_congr (pw_one two) (.eqRefl _) (pw_le_exp two_pos' h))

theorem small {N c : PTm n} (e : Γ ⊢[PRAAx] N ≐ c) (h : Γ ⊢[PRAAx] le (pri c) (pw two (two * c))) :
    Γ ⊢[PRAAx] le (pri N) (pw two (two * N)) :=
  le_congr (congrPri e.eqSymm) (congrPw (.eqRefl _) (congrMul (.eqRefl _) e.eqSymm)) h

/-! ## The strong induction -/

/-- From the bound at `m = j + 2` to the bound at `N`, given `pri N ≤ pri (2m)` and `4m − 2 ≤ 2N`. -/
theorem tail {N m j : PTm n} (em : Γ ⊢[PRAAx] m ≐ succ (succ j))
    (hN : Γ ⊢[PRAAx] le (pri N) (pri (two * m)))
    (hE : Γ ⊢[PRAAx] le (two * m + two * succ j) (two * N))
    (ih : Γ ⊢[PRAAx] le (pri m) (pw two (two * m))) :
    Γ ⊢[PRAAx] le (pri N) (pw two (two * N)) := by
  have c1 : Γ ⊢[PRAAx] pri (two * m) ≐ pri (two * succ (succ j)) := congrPri (congrMul (.eqRefl _) em)
  have st := pri_step (Γ := Γ) j
  have ih' : Γ ⊢[PRAAx] le (pri (succ (succ j))) (pw two (two * m)) := le_congr (congrPri em) (.eqRefl _) ih
  have a := le_mul_mono ih' (le_refl (pw two (two * succ j)))
  have e := (pw_add (Γ := Γ) two (two * m) (two * succ j)).eqSymm
  have b := pw_le_exp two_pos' hE
  exact le_trans hN (le_trans (le_congr c1.eqSymm (.eqRefl _) st) (le_trans (le_congr (.eqRefl _) e a) b))

/-- The violation `pri r ∸ 4^r`, over `0 = r`. -/
abbrev violB : PTm 2 := monus (pri (var 0)) (pw two (two * var 0))

theorem inst2_violB (N x : PTm n) : inst2 violB N x = monus (pri N) (pw two (two * N)) := by simp [inst2]

theorem ih_at {N x m : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF violB) N x ≐ zero) (hm : Γ ⊢[PRAAx] lt m N) :
    Γ ⊢[PRAAx] le (pri m) (pw two (two * m)) := by
  have h := sum_zero_elim violB hS hm
  rw [inst2_violB] at h
  exact h

/-- The odd case `N + 1 = 2m`, `N ≥ 3`. -/
theorem step_odd {N x : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF violB) N x ≐ zero) (h3 : Γ ⊢[PRAAx] lt two N)
    (pz : Γ ⊢[PRAAx] par (succ N) ≐ zero) : Γ ⊢[PRAAx] le (pri N) (pw two (two * N)) := by
  have hp := natEq (half_par (Γ := Γ) (succ N)); have pzn := natEq pz
  have m2 : Γ ⊢[PRAAx] le two (half (succ N)) := by
    refine .orE (lt_or_le (half (succ N)) two) ?_ Prf.hyp0
    have hlt : (lt (half (succ N)) two :: Γ) ⊢[PRAAx] lt (half (succ N)) two := Prf.hyp0
    have h3' : (lt (half (succ N)) two :: Γ) ⊢[PRAAx] lt two N := h3.wk
    have hp' := natEq (half_par (Γ := lt (half (succ N)) two :: Γ) (succ N))
    have pz' := natEq (pz.wk (ψ := lt (half (succ N)) two))
    have bad : (lt (half (succ N)) two :: Γ) ⊢[PRAAx] le two zero := by
      ipra_le sl h3' + 2 * sl hlt with hp' + pz'
    exact lt_zero_absurd _ bad
  have em := two_eq m2
  have emn := natEq em
  have e2m : Γ ⊢[PRAAx] succ N ≐ two * half (succ N) := by
    apply deriveNat; ipra_simps; linear_combination hp + pzn
  have hN : Γ ⊢[PRAAx] le (pri N) (pri (two * half (succ N))) :=
    le_congr (.eqRefl _) (congrPri e2m) (pri_mono_succ N)
  have E : Γ ⊢[PRAAx] two * half (succ N) + two * succ (monus (half (succ N)) two) ≐ two * N := by
    apply deriveNat; ipra_simps; linear_combination -2 * hp - 2 * pzn - 2 * emn
  have hE := le_congr (.eqRefl _) E (le_refl _)
  have mN : Γ ⊢[PRAAx] lt (half (succ N)) N := by
    ipra_le 𝔞 (monus (half (succ N)) two) with hp + pzn + emn
  exact tail em hN hE (ih_at hS mN)

/-- The even case `N = 2m`, `N ≥ 3`. -/
theorem step_even {N x : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF violB) N x ≐ zero) (h3 : Γ ⊢[PRAAx] lt two N)
    (po : Γ ⊢[PRAAx] par (succ N) ≐ one) : Γ ⊢[PRAAx] le (pri N) (pw two (two * N)) := by
  have hp := natEq (half_par (Γ := Γ) (succ N)); have pon := natEq po
  have m2 : Γ ⊢[PRAAx] le two (half (succ N)) := by
    refine .orE (lt_or_le (half (succ N)) two) ?_ Prf.hyp0
    have hlt : (lt (half (succ N)) two :: Γ) ⊢[PRAAx] lt (half (succ N)) two := Prf.hyp0
    have h3' : (lt (half (succ N)) two :: Γ) ⊢[PRAAx] lt two N := h3.wk
    have hp' := natEq (half_par (Γ := lt (half (succ N)) two :: Γ) (succ N))
    have po' := natEq (po.wk (ψ := lt (half (succ N)) two))
    have bad : (lt (half (succ N)) two :: Γ) ⊢[PRAAx] le one zero := by
      ipra_le sl h3' + 2 * sl hlt with hp' + po'
    exact lt_zero_absurd _ bad
  have em := two_eq m2
  have emn := natEq em
  have e2m : Γ ⊢[PRAAx] N ≐ two * half (succ N) := by
    apply deriveNat; ipra_simps; linear_combination hp + pon
  have hN : Γ ⊢[PRAAx] le (pri N) (pri (two * half (succ N))) :=
    le_congr (.eqRefl _) (congrPri e2m) (le_refl (pri N))
  have hE : Γ ⊢[PRAAx] le (two * half (succ N) + two * succ (monus (half (succ N)) two)) (two * N) := by
    ipra_le 2 with 2 * hp + 2 * pon + 2 * emn
  have mN : Γ ⊢[PRAAx] lt (half (succ N)) N := by
    ipra_le 𝔞 (monus (half (succ N)) two) + 1 with hp + pon + emn
  exact tail em hN hE (ih_at hS mN)

theorem step {N x : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF violB) N x ≐ zero) :
    Γ ⊢[PRAAx] le (pri N) (pw two (two * N)) := by
  refine .orE (lt_or_le two N) ?_ ?_
  · refine .orE (par_cases (succ N)) ?_ ?_
    · exact step_odd hS.wk.wk Prf.hyp1 Prf.hyp0
    · exact step_even hS.wk.wk Prf.hyp1 Prf.hyp0
  · refine .orE (lt_or_eq_of_le (Prf.hyp0 (Γ := Γ) (φ := le N two))) ?_ ?_
    · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := le N two :: Γ) (φ := lt N two))) ?_ ?_
      · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := lt N two :: le N two :: Γ) (φ := lt N one))) ?_ ?_
        · exact lt_zero_absurd _ Prf.hyp0
        · exact small Prf.hyp0 pri_le_zero
      · exact small Prf.hyp0 pri_le_one
    · exact small Prf.hyp0 pri_le_two

/-- The estimate (6): `∏_{p ≤ r} p ≤ 4^r`. -/
theorem pri_le (r : PTm n) : Γ ⊢[PRAAx] le (pri r) (pw two (two * r)) := by
  have h := strong_ind (Γ := Γ) violB (fun N x hS => by rw [inst2_violB]; exact step hS) r zero
  rw [inst2_violB] at h
  exact h

/-! ## The primorial of `PrimorialLower` -/

theorem prim_eq (P : PTm n) : Γ ⊢[PRAAx] prim P ≐ pri P :=
  prod_congr_bounded (PE one) (PE one) P zero (succ P)
    (.allI (.impI (by rw [fac_at, fac_at]; exact .eqRefl _)))

/-- `∏_{p ≤ P} p ≤ 4^P` for the primorial of `PrimorialLower`. -/
theorem primorial_le (P : PTm n) : Γ ⊢[PRAAx] le (prim P) (pw two (two * P)) :=
  le_congr (prim_eq P).eqSymm (.eqRefl _) (pri_le P)

end LeanProofs.IPRA.AnalyticNumberTheory.PrimorialUpper
