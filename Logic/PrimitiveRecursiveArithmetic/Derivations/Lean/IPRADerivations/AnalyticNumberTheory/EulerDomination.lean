import IPRADerivations.AnalyticNumberTheory.Smooth
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.InductionTactic

/-!
# The Euler product dominates the harmonic sum

Packet: `analytic-number-theory/prime_reciprocal_ipra_2026-11-15`, Lemma `lem:euler-domination`
(`H_n ≤ E_n`, i.e. `NumH_n · DenE_n ≤ Fact_n · ProdP_n`), Corollary `cor:harmonic-upper` and the
main Theorem `thm:main` (`∑_{p ≤ n} 1/p > k` for `n = 2^{2·4^k}`).

Instead of the paper's factor-vector injection, the comparison is an induction over the primes.
For a modulus `a`, an exponent `L` and a numerator `F` put

  `Sm(a) = ∑_{m<N} sg(m) · [m ∣ a^L] · ⌊F/m⌋`  (the `a`-smooth part of the harmonic sum).

* `prime_step`: for a prime `p`, `p · Sm(ap) ≤ p · Sm(a) + Sm(ap)`. Indeed
  `[m ∣ (ap)^L] ≤ [m ∣ a^L] + [p ∣ m][m ∣ (ap)^L]` (Gauss, `ptA`), and the multiples `m = kp` are
  sent to `k` with `p ⌊F/(kp)⌋ ≤ ⌊F/k⌋` (`ptB`, `SumReindex.reindex_le`);
* `main`: `Sm(A(y)) · D(y) ≤ F · A(y)` by induction on `y`, starting from `Sm(1) ≤ F`;
* `euler_domination`: at `y = n + 1` every `1 ≤ m ≤ n` is smooth (`Smooth.smooth_all`), so
  `(∑_{m=1}^{n} ⌊F/m⌋) · DenE_n ≤ F · ProdP_n` for every `F`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (congrSg zo_eqb zo_sg eq_of_eqb congrPair)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq coprime_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq')
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (eqb_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime eq_succ_pred)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_le le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP isP_01 prime_of_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (A Dn pB dB pBt dBt A_succ Dn_succ A_pos pBt_zero pBt_one
  dBt_zero dBt_one ProdP DenE NumP sum_bounds_product)
open LeanProofs.IPRA.AnalyticNumberTheory.Smooth (smooth_all)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The smooth term -/

/-- `sg(m) · [m ∣ a^L] · ⌊F/m⌋`. -/
abbrev term (a L F m : PTm n) : PTm n := sg m * (eqb (rem (pw a L) m) zero * quo F m)

theorem congrTerm {a a' L L' F F' m m' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hL : Γ ⊢[PRAAx] L ≐ L')
    (hF : Γ ⊢[PRAAx] F ≐ F') (hm : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] term a L F m ≐ term a' L' F' m' :=
  congrMul (congrSg hm) (congrMul (congrEqb (congrAp2 remF (congrPw ha hL) hm) (.eqRefl _)) (congrAp2 quoF hF hm))

theorem term_zero {a L F m : PTm n} (h : Γ ⊢[PRAAx] m ≐ zero) : Γ ⊢[PRAAx] term a L F m ≐ zero :=
  (congrMul ((congrSg h).eqTrans sg_zero) (.eqRefl _)).eqTrans (zero_mul _)

theorem term_ndvd {a L F m : PTm n} (h : Γ ⊢[PRAAx] eqb (rem (pw a L) m) zero ≐ zero) :
    Γ ⊢[PRAAx] term a L F m ≐ zero :=
  (congrMul (.eqRefl _) ((congrMul h (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)

theorem term_pos {a L F m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hd : Γ ⊢[PRAAx] dvd m (pw a L)) :
    Γ ⊢[PRAAx] term a L F m ≐ quo F m :=
  (congrMul ((congrSg hm).eqTrans (sg_succ _)) ((congrMul (eqb_of_eq hd) (.eqRefl _)).eqTrans (one_mul _))).eqTrans
    (one_mul _)

alias le_zero_of := Common.le_of_eq_zero

alias sg_le_one := Common.sg_le_one

theorem term_le_quo (a L F m : PTm n) : Γ ⊢[PRAAx] le (term a L F m) (quo F m) :=
  le_congr (.eqRefl _) ((congrMul (.eqRefl _) (one_mul _)).eqTrans (one_mul _))
    (le_mul_mono (sg_le_one m) (le_mul_mono (eqb_le_one _ _) (le_refl _)))

/-- Monotonicity of the term in the smoothness condition, at `m ≥ 1`. -/
theorem term_le_of {a b L F m : PTm n} (h : Γ ⊢[PRAAx] dvd m (pw a L) ⟶ dvd m (pw b L))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] le (term a L F m) (term b L F m) :=
  .orE (zo_eqb (rem (pw a L) m) zero) (le_zero_of (term_ndvd Prf.hyp0))
    (le_congr (term_pos hm.wk (eq_of_eqb Prf.hyp0)).eqSymm
      (term_pos hm.wk (Prf.impE h.wk (eq_of_eqb Prf.hyp0))).eqSymm (le_refl _))

theorem neg_of_eqb_zero {x y : PTm n} (h : Γ ⊢[PRAAx] eqb x y ≐ zero) : Γ ⊢[PRAAx] neg (x ≐ y) :=
  .impI (succ_ne_zero' _ (a := zero) ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans h.wk))

/-! ## The two pointwise inequalities -/

/-- `p ∤ m` and `m ∣ (ap)^L` give `m ∣ a^L`. -/
theorem dvd_drop {p a L m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hnd : Γ ⊢[PRAAx] neg (dvd p m)) (hd : Γ ⊢[PRAAx] dvd m (pw (a * p) L)) : Γ ⊢[PRAAx] dvd m (pw a L) :=
  gauss hm (coprime_pow hm (gcd_comm_one hm (gcd_prime hp hnd)) L)
    (dvd_congr ((pw_mul_base a p L).eqTrans (mul_comm _ _)) hd)

theorem term_drop_pos {p a L F m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hnd : Γ ⊢[PRAAx] neg (dvd p m))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] le (term (a * p) L F m) (term a L F m) :=
  term_le_of (.impI (dvd_drop hp.wk hm.wk hnd.wk Prf.hyp0)) hm

theorem term_drop {p a L F m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hnd : Γ ⊢[PRAAx] neg (dvd p m)) :
    Γ ⊢[PRAAx] le (term (a * p) L F m) (term a L F m) :=
  .orE (zero_or_succ m) (le_zero_of (term_zero Prf.hyp0)) (term_drop_pos hp.wk hnd.wk Prf.hyp0)

/-- `[m ∣ (ap)^L] ≤ [m ∣ a^L] + [p ∣ m][m ∣ (ap)^L]`, weighted. -/
theorem ptA {p a L F m : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] le (term (a * p) L F m) (term a L F m + eqb (rem m p) zero * term (a * p) L F m) :=
  .orE (zo_eqb (rem m p) zero)
    (le_trans (term_drop hp.wk (neg_of_eqb_zero Prf.hyp0))
      (le_of_eq_add (d := eqb (rem m p) zero * term (a * p) L F m) (.eqRefl _)))
    (le_of_eq_add (d := term a L F m)
      ((congrAdd (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _))).eqTrans (add_comm _ _)))

theorem quo_pos_of {m p : PTm n} (hm : Γ ⊢[PRAAx] m ≐ p * quo m p) (mpos : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] quo m p ≐ succ (pred (quo m p)) :=
  .orE (zero_or_succ (quo m p))
    (succ_ne_zero' _ (a := pred m)
      (mpos.wk.eqSymm.eqTrans (hm.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))))
    Prf.hyp0

theorem ptB_dvd {p a L F m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ p * quo m p) (mpos : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hdX : Γ ⊢[PRAAx] dvd m (pw (a * p) L)) :
    Γ ⊢[PRAAx] le (p * term (a * p) L F m) (term (a * p) L F (quo m p)) := by
  have kpos := quo_pos_of hm mpos
  have hkm : Γ ⊢[PRAAx] dvd (quo m p) m := dvd_of_eq' kpos (w := p) (hm.eqTrans (mul_comm _ _))
  have hkX := dvd_trans' kpos mpos hkm hdX
  refine le_congr (congrMul (.eqRefl _) (term_pos mpos hdX)).eqSymm (term_pos kpos hkX).eqSymm ?_
  refine le_quo_of_mul_le kpos (le_of_eq_add (d := rem F m) ?_)
  ipra_lc natEq (div_eq (j := F) mpos) + Groth.ι (IPRA.Q.mk Γ (quo F m)) * natEq hm

theorem ptB_pos {p a L F m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ p * quo m p) (mpos : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (p * term (a * p) L F m) (term (a * p) L F (quo m p)) :=
  .orE (zo_eqb (rem (pw (a * p) L) m) zero)
    (le_zero_of ((congrMul (.eqRefl _) (term_ndvd Prf.hyp0)).eqTrans (mul_zero _)))
    (ptB_dvd hm.wk mpos.wk (eq_of_eqb Prf.hyp0))

theorem ptB_core {p a L F m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ p * quo m p) :
    Γ ⊢[PRAAx] le (p * term (a * p) L F m) (term (a * p) L F (quo m p)) :=
  .orE (zero_or_succ m) (le_zero_of ((congrMul (.eqRefl _) (term_zero Prf.hyp0)).eqTrans (mul_zero _)))
    (ptB_pos hm.wk Prf.hyp0)

/-- `p · [p ∣ m] t(m) ≤ [p ∣ m] t(m/p)`: the multiple `m = kp` is charged to `k`. -/
theorem ptB {p a L F m : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] le (p * (eqb (rem m p) zero * term (a * p) L F m))
      (eqb (rem m p) zero * term (a * p) L F (quo m p)) :=
  .orE (zo_eqb (rem m p) zero)
    (le_zero_of ((congrMul (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)))
    (le_congr (congrMul (.eqRefl p) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _))).eqSymm
      ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)).eqSymm
      (ptB_core (eq_of_dvd' hp.wk (eq_of_eqb Prf.hyp0))))

/-! ## The smooth sum -/

/-- The term as a body: `0 = m`, `1 = ⟨a, ⟨L, F⟩⟩`. -/
abbrev gB : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)

theorem inst2_g (m y : PTm n) : inst2 gB m y = term (fstT y) (fstT (sndT y)) (sndT (sndT y)) m := by
  simp [inst2]

abbrev par (a L F : PTm n) : PTm n := pairT a (pairT L F)

/-- `Sm(a) = ∑_{m<N} sg(m) [m ∣ a^L] ⌊F/m⌋`. -/
abbrev Sm (a L F N : PTm n) : PTm n := ap2 (sumF gB) N (par a L F)

theorem shift_par (a L F : PTm n) :
    Syn.shift (par a L F) = par (Syn.shift a) (Syn.shift L) (Syn.shift F) := by simp [Syn.shift]

theorem g_at (a L F m : PTm n) : Γ ⊢[PRAAx] inst2 gB m (par a L F) ≐ term a L F m := by
  rw [inst2_g]
  exact congrTerm (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem Sm_congr {a a' L F N : PTm n} (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] Sm a L F N ≐ Sm a' L F N :=
  congrAp2 (sumF gB) (.eqRefl _) (congrPair h (.eqRefl _))

theorem Sm_succ (a L F N : PTm n) : Γ ⊢[PRAAx] Sm a L F (succ N) ≐ Sm a L F N + term a L F N :=
  (sum_succ' gB N _).eqTrans (congrAdd (.eqRefl _) (g_at _ _ _ _))

/-! ## The base: `Sm(1) ≤ F` -/

theorem eq_zero_of_le_zero {x : PTm n} (h : Γ ⊢[PRAAx] le x zero) : Γ ⊢[PRAAx] x ≐ zero :=
  (monus_zero x).eqSymm.eqTrans h

theorem quo_one (F : PTm n) : Γ ⊢[PRAAx] quo F one ≐ F :=
  quo_eq (congrSucc (pred_succ _).eqSymm) (q := F) (r := zero) (by ipra_ring) (le_refl _)

theorem two_add (x : PTm n) : Γ ⊢[PRAAx] two + x ≐ succ (succ x) := by ipra_ring

alias pos_of_two_le := Common.pos_of_two_le

theorem term_one_big {L F m : PTm n} (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx] term one L F m ≐ zero := by
  have r : Γ ⊢[PRAAx] rem (pw one L) m ≐ one := (congrAp2 remF (pw_one_base L) (.eqRefl _)).eqTrans
    (rem_eq' (pos_of_two_le hm) (q := zero) (r := one) (by ipra_ring) hm)
  exact term_ndvd ((congrEqb r (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ (a := zero) Prf.hyp0))))

theorem sgm_succ (N F : PTm n) : Γ ⊢[PRAAx] sg (monus (succ N) one) * F ≐ sg N * F :=
  congrMul (congrSg ((succ_monus_succ _ _).eqTrans (monus_zero _))) (.eqRefl _)

section Base

variable {N L F : PTm n} (ih : Γ ⊢[PRAAx] le (Sm one L F N) (sg (monus N one) * F))
include ih

theorem base_zero (h0 : Γ ⊢[PRAAx] N ≐ zero) :
    Γ ⊢[PRAAx] le (Sm one L F (succ N)) (sg (monus (succ N) one) * F) := by
  have r0 : Γ ⊢[PRAAx] sg (monus N one) * F ≐ zero :=
    (congrMul ((congrSg ((congrMonus h0 (.eqRefl _)).eqTrans (zero_monus _))).eqTrans sg_zero) (.eqRefl _)).eqTrans
      (zero_mul _)
  have S0 := eq_zero_of_le_zero (le_congr (.eqRefl _) r0 ih)
  exact le_zero_of ((Sm_succ _ _ _ _).eqTrans ((congrAdd S0 (term_zero h0)).eqTrans (add_zero _)))

theorem base_one (h1 : Γ ⊢[PRAAx] N ≐ one) :
    Γ ⊢[PRAAx] le (Sm one L F (succ N)) (sg (monus (succ N) one) * F) := by
  have r0 : Γ ⊢[PRAAx] sg (monus N one) * F ≐ zero :=
    (congrMul ((congrSg ((congrMonus h1 (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _)))).eqTrans
      sg_zero) (.eqRefl _)).eqTrans (zero_mul _)
  have S0 := eq_zero_of_le_zero (le_congr (.eqRefl _) r0 ih)
  have t : Γ ⊢[PRAAx] le (term one L F N) F :=
    le_congr (.eqRefl _) ((congrAp2 quoF (.eqRefl _) h1).eqTrans (quo_one F)) (term_le_quo _ _ _ _)
  have eR : Γ ⊢[PRAAx] sg (monus (succ N) one) * F ≐ F :=
    (sgm_succ N F).eqTrans ((congrMul ((congrSg h1).eqTrans (sg_succ _)) (.eqRefl _)).eqTrans (one_mul _))
  exact le_congr ((Sm_succ _ _ _ _).eqTrans ((congrAdd S0 (.eqRefl _)).eqTrans (zero_add _))).eqSymm eR.eqSymm t

theorem base_big (h2 : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] le (Sm one L F (succ N)) (sg (monus (succ N) one) * F) := by
  have eR : Γ ⊢[PRAAx] sg (monus (succ N) one) * F ≐ F :=
    (sgm_succ N F).eqTrans ((congrMul ((congrSg (pos_of_two_le h2)).eqTrans (sg_succ _)) (.eqRefl _)).eqTrans
      (one_mul _))
  have b : Γ ⊢[PRAAx] le (sg (monus N one) * F) F :=
    le_congr (.eqRefl _) (one_mul _) (le_mul_mono (sg_le_one _) (le_refl F))
  exact le_congr ((Sm_succ _ _ _ _).eqTrans ((congrAdd (.eqRefl _) (term_one_big h2)).eqTrans (add_zero _))).eqSymm
    eR.eqSymm (le_trans ih b)

theorem base_step : Γ ⊢[PRAAx] le (Sm one L F (succ N)) (sg (monus (succ N) one) * F) :=
  .orE (zero_or_succ N) (base_zero ih.wk Prf.hyp0)
    (.orE (zero_or_succ (pred N)) (base_one ih.wk.wk (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))
      (base_big ih.wk.wk (le_of_eq_add (d := pred (pred N))
        (Prf.hyp1.eqTrans ((congrSucc Prf.hyp0).eqTrans (two_add _).eqSymm)))))

end Base

/-- Variables: `0 = N`, `1 = L`, `2 = F`. -/
private abbrev baseF : Fm PTm 3 :=
  le (Sm one (var 1) (var 2) (var 0)) (sg (monus (var 0) one) * var 2)

private theorem base₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] baseF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
  · exact le_zero_of (sum_zero _ _)
  · exact base_step Prf.hyp0

/-- `Sm(1) ≤ F`: only `m = 1` is `1`-smooth. -/
theorem base_le (L F N : PTm n) : Γ ⊢[PRAAx] le (Sm one L F N) F := by
  have i := inst (Γ := Γ) base₀ (![N, L, F] : Fin 3 → PTm n)
  simp at i
  exact le_trans i (le_congr (.eqRefl _) (one_mul _) (le_mul_mono (sg_le_one _) (le_refl F)))

/-! ## The prime step, summed -/

/-- The parameter `⟨p, ⟨a, ⟨L, F⟩⟩⟩` of the bodies below. -/
abbrev zz (p a L F : PTm n) : PTm n := pairT p (par a L F)

theorem shift_zz (p a L F : PTm n) :
    Syn.shift (zz p a L F) = zz (Syn.shift p) (Syn.shift a) (Syn.shift L) (Syn.shift F) := by simp [Syn.shift]

theorem zz_p (p a L F : PTm n) : Γ ⊢[PRAAx] fstT (zz p a L F) ≐ p := fst_pair _ _
theorem zz_a (p a L F : PTm n) : Γ ⊢[PRAAx] fstT (sndT (zz p a L F)) ≐ a :=
  (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem zz_L (p a L F : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (zz p a L F))) ≐ L :=
  (congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem zz_F (p a L F : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (zz p a L F))) ≐ F :=
  (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

/-- `t_{ap}(m)`. -/
abbrev bAP : PTm 2 :=
  term (fstT (sndT (var 1)) * fstT (var 1)) (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
/-- `t_a(m)`. -/
abbrev bA : PTm 2 :=
  term (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
/-- `[p ∣ m] t_{ap}(m)`. -/
abbrev bT : PTm 2 := eqb (rem (var 0) (fstT (var 1))) zero * bAP
/-- `[p ∣ m] t_{ap}(m/p)`. -/
abbrev bR : PTm 2 :=
  eqb (rem (var 0) (fstT (var 1))) zero *
    term (fstT (sndT (var 1)) * fstT (var 1)) (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
      (quo (var 0) (fstT (var 1)))

theorem inst2_bAP (m y : PTm n) : inst2 bAP m y =
    term (fstT (sndT y) * fstT y) (fstT (sndT (sndT y))) (sndT (sndT (sndT y))) m := by simp [inst2]
theorem inst2_bA (m y : PTm n) : inst2 bA m y =
    term (fstT (sndT y)) (fstT (sndT (sndT y))) (sndT (sndT (sndT y))) m := by simp [inst2]
theorem inst2_bT (m y : PTm n) : inst2 bT m y = eqb (rem m (fstT y)) zero *
    term (fstT (sndT y) * fstT y) (fstT (sndT (sndT y))) (sndT (sndT (sndT y))) m := by simp [inst2]
theorem inst2_bR (m y : PTm n) : inst2 bR m y = eqb (rem m (fstT y)) zero *
    term (fstT (sndT y) * fstT y) (fstT (sndT (sndT y))) (sndT (sndT (sndT y))) (quo m (fstT y)) := by
  simp [inst2]

theorem bAP_at (p a L F m : PTm n) : Γ ⊢[PRAAx] inst2 bAP m (zz p a L F) ≐ term (a * p) L F m := by
  rw [inst2_bAP]
  exact congrTerm (congrMul (zz_a _ _ _ _) (zz_p _ _ _ _)) (zz_L _ _ _ _) (zz_F _ _ _ _) (.eqRefl _)

theorem bA_at (p a L F m : PTm n) : Γ ⊢[PRAAx] inst2 bA m (zz p a L F) ≐ term a L F m := by
  rw [inst2_bA]
  exact congrTerm (zz_a _ _ _ _) (zz_L _ _ _ _) (zz_F _ _ _ _) (.eqRefl _)

theorem bT_at (p a L F m : PTm n) :
    Γ ⊢[PRAAx] inst2 bT m (zz p a L F) ≐ eqb (rem m p) zero * term (a * p) L F m := by
  rw [inst2_bT]
  exact congrMul (congrEqb (congrAp2 remF (.eqRefl _) (zz_p _ _ _ _)) (.eqRefl _))
    (congrTerm (congrMul (zz_a _ _ _ _) (zz_p _ _ _ _)) (zz_L _ _ _ _) (zz_F _ _ _ _) (.eqRefl _))

theorem bR_at (p a L F m : PTm n) :
    Γ ⊢[PRAAx] inst2 bR m (zz p a L F) ≐ eqb (rem m p) zero * term (a * p) L F (quo m p) := by
  rw [inst2_bR]
  exact congrMul (congrEqb (congrAp2 remF (.eqRefl _) (zz_p _ _ _ _)) (.eqRefl _))
    (congrTerm (congrMul (zz_a _ _ _ _) (zz_p _ _ _ _)) (zz_L _ _ _ _) (zz_F _ _ _ _)
      (congrAp2 quoF (.eqRefl _) (zz_p _ _ _ _)))

theorem ri_at (p a L F m : PTm n) :
    Γ ⊢[PRAAx] inst2 (riB gB) m (zz p (a * p) L F) ≐ eqb (rem m p) zero * term (a * p) L F (quo m p) := by
  rw [inst2_riB, inst2_g]
  exact congrMul (congrEqb (congrAp2 remF (.eqRefl _) (zz_p _ _ _ _)) (.eqRefl _))
    (congrTerm (zz_a _ _ _ _) (zz_L _ _ _ _) (zz_F _ _ _ _) (congrAp2 quoF (.eqRefl _) (zz_p _ _ _ _)))

section PrimeStep

variable {p a L F : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n)
include hp

theorem sAP : Γ ⊢[PRAAx] ap2 (sumF bAP) N (zz p a L F) ≐ Sm (a * p) L F N := by
  refine sum_congr_bounded bAP gB (zz p a L F) (par (a * p) L F) N (.allI (.impI ?_))
  rw [shift_zz, shift_par, AnalyticNumberTheory.SumPhi.shift_mul']
  exact (bAP_at _ _ _ _ _).eqTrans (g_at _ _ _ _).eqSymm

theorem sA : Γ ⊢[PRAAx] ap2 (sumF bA) N (zz p a L F) ≐ Sm a L F N := by
  refine sum_congr_bounded bA gB (zz p a L F) (par a L F) N (.allI (.impI ?_))
  rw [shift_zz, shift_par]
  exact (bA_at _ _ _ _ _).eqTrans (g_at _ _ _ _).eqSymm

theorem sR : Γ ⊢[PRAAx] ap2 (sumF bR) N (zz p a L F) ≐ ap2 (sumF (riB gB)) N (zz p (a * p) L F) := by
  refine sum_congr_bounded bR (riB gB) (zz p a L F) (zz p (a * p) L F) N (.allI (.impI ?_))
  rw [shift_zz, shift_zz, AnalyticNumberTheory.SumPhi.shift_mul']
  exact (bR_at _ _ _ _ _).eqTrans (ri_at _ _ _ _ _).eqSymm

theorem leA : Γ ⊢[PRAAx] le (ap2 (sumF bAP) N (zz p a L F))
    (ap2 (sumF bA) N (zz p a L F) + ap2 (sumF bT) N (zz p a L F)) :=
  le_congr (.eqRefl _) (sum_add bA bT N _)
    (Analysis.PowerSums.sum_le bAP (addBody bA bT) (zz p a L F) N (.allI (.impI (by
      rw [inst2_addBody, shift_zz]
      exact le_congr (bAP_at _ _ _ _ _).eqSymm (congrAdd (bA_at _ _ _ _ _).eqSymm (bT_at _ _ _ _ _).eqSymm)
        (ptA (AnalyticNumberTheory.Fermat.prime_shift hp).wk)))))

/-- The multiplier `p` read from the parameter. -/
abbrev cP : PTm 1 := fstT (var 0)

theorem leB : Γ ⊢[PRAAx] le (p * ap2 (sumF bT) N (zz p a L F)) (ap2 (sumF bR) N (zz p a L F)) := by
  have ec : Syn.subst ![zz p a L F] (cP : PTm 1) = fstT (zz p a L F) := by simp
  have e := Analysis.PowerSums.sum_mul_param (Γ := Γ) cP bT N (zz p a L F)
  rw [ec] at e
  refine le_congr (e.eqTrans (congrMul (zz_p _ _ _ _) (.eqRefl _))) (.eqRefl _) ?_
  refine Analysis.PowerSums.sum_le (Analysis.PowerSums.mulParam cP bT) bR (zz p a L F) N (.allI (.impI ?_))
  rw [Analysis.PowerSums.inst2_mulParam, shift_zz]
  have ec' : Syn.subst ![zz (Syn.shift p) (Syn.shift a) (Syn.shift L) (Syn.shift F)] (cP : PTm 1) =
      fstT (zz (Syn.shift p) (Syn.shift a) (Syn.shift L) (Syn.shift F)) := by simp
  rw [ec']
  exact le_congr (congrMul (zz_p _ _ _ _) (bT_at _ _ _ _ _)).eqSymm (bR_at _ _ _ _ _).eqSymm
    (ptB (AnalyticNumberTheory.GcdFiber.shift_pos (prime_eq_succ_pred hp)).wk)

/-- `p · Sm(ap) ≤ p · Sm(a) + Sm(ap)`. -/
theorem prime_step : Γ ⊢[PRAAx] le (p * Sm (a * p) L F N) (p * Sm a L F N + Sm (a * p) L F N) := by
  have h1 : Γ ⊢[PRAAx] le (Sm (a * p) L F N) (Sm a L F N + ap2 (sumF bT) N (zz p a L F)) :=
    le_congr (sAP hp N) (congrAdd (sA hp N) (.eqRefl _)) (leA hp N)
  have h2 : Γ ⊢[PRAAx] le (p * ap2 (sumF bT) N (zz p a L F)) (Sm (a * p) L F N) :=
    le_trans (leB hp N) (le_congr (sR hp N).eqSymm (.eqRefl _) (reindex_le gB N (prime_eq_succ_pred hp)))
  refine le_trans (le_mul_mono (le_refl p) h1) (le_congr ?_ (.eqRefl _) (add_le_add (le_refl (p * Sm a L F N)) h2))
  ipra_ring

end PrimeStep

/-! ## The step at an arbitrary index and the main induction -/

alias mul_one' := Common.mul_one_right

theorem gen_step_prime {y a L F N : PTm n} (hI : Γ ⊢[PRAAx] isP y ≐ one) :
    Γ ⊢[PRAAx] le (dBt y * Sm (a * pBt y) L F N) (pBt y * Sm a L F N) := by
  have hp := prime_of_isP hI
  have ps := prime_step (a := a) (L := L) (F := F) hp N
  have c : Γ ⊢[PRAAx] le (pred y * Sm (a * y) L F N) (y * Sm a L F N) := by
    refine le_of_eq_add (d := monus (y * Sm a L F N + Sm (a * y) L F N) (y * Sm (a * y) L F N)) ?_
    ipra_lc natEq (eq_add_of_le ps) + Groth.ι (IPRA.Q.mk Γ (Sm (a * y) L F N)) * natEq (prime_eq_succ_pred hp)
  exact le_congr (congrMul (dBt_one hI) (Sm_congr (congrMul (.eqRefl _) (pBt_one hI)))).eqSymm
    (congrMul (pBt_one hI) (.eqRefl _)).eqSymm c

theorem gen_step {y a L F N : PTm n} :
    Γ ⊢[PRAAx] le (dBt y * Sm (a * pBt y) L F N) (pBt y * Sm a L F N) :=
  .orE (isP_01 y)
    (le_congr (congrMul (dBt_zero Prf.hyp0) (Sm_congr ((congrMul (.eqRefl _) (pBt_zero Prf.hyp0)).eqTrans
        (mul_one' _)))).eqSymm
      (congrMul (pBt_zero Prf.hyp0) (.eqRefl _)).eqSymm (le_refl _))
    (gen_step_prime Prf.hyp0)

theorem main_step {y L F N : PTm n} (ih : Γ ⊢[PRAAx] le (Sm (A y) L F N * Dn y) (F * A y)) :
    Γ ⊢[PRAAx] le (Sm (A (succ y)) L F N * Dn (succ y)) (F * A (succ y)) := by
  have gs := gen_step (Γ := Γ) (y := y) (a := A y) (L := L) (F := F) (N := N)
  have m₁ := le_mul_mono gs (le_refl (Dn y))
  have m₂ := le_mul_mono (le_refl (pBt y)) ih
  have eL : Γ ⊢[PRAAx] Sm (A (succ y)) L F N * Dn (succ y) ≐ dBt y * Sm (A y * pBt y) L F N * Dn y :=
    (congrMul (Sm_congr (A_succ y)) (Dn_succ y)).eqTrans (by ipra_ring)
  have eM : Γ ⊢[PRAAx] pBt y * Sm (A y) L F N * Dn y ≐ pBt y * (Sm (A y) L F N * Dn y) := by
    ipra_ring
  have eR : Γ ⊢[PRAAx] pBt y * (F * A y) ≐ F * A (succ y) :=
    (by ipra_ring : Γ ⊢[PRAAx] pBt y * (F * A y) ≐ F * (A y * pBt y)).eqTrans
      (congrMul (.eqRefl _) (A_succ y).eqSymm)
  exact le_congr eL.eqSymm eR (le_trans (le_congr (.eqRefl _) eM m₁) m₂)

/-- Variables: `0 = y`, `1 = L`, `2 = F`, `3 = N`. -/
private abbrev mainF : Fm PTm 4 :=
  le (Sm (A (var 0)) (var 1) (var 2) (var 3) * Dn (var 0)) (var 2 * A (var 0))

private theorem main₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] mainF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
  · have eA : ([] : List (Fm PTm 3)) ⊢[PRAAx] A (zero : PTm 3) ≐ one := prod_zero _ _
    have eD : ([] : List (Fm PTm 3)) ⊢[PRAAx] Dn (zero : PTm 3) ≐ one := prod_zero _ _
    exact le_congr (congrMul (Sm_congr eA) eD).eqSymm (congrMul (.eqRefl _) eA).eqSymm
      (le_mul_mono (base_le _ _ _) (le_refl _))
  · exact main_step Prf.hyp0

/-- `Sm(A(y)) · D(y) ≤ F · A(y)`. -/
theorem main (y L F N : PTm n) : Γ ⊢[PRAAx] le (Sm (A y) L F N * Dn y) (F * A y) := by
  have i := inst (Γ := Γ) main₀ (![y, L, F, N] : Fin 4 → PTm n)
  simpa using i

/-! ## The comparison `H_n ≤ E_n` -/

open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (hB inst2_h)

theorem shift_A_succ (m : PTm n) : Syn.shift (A (succ m)) = A (succ (Syn.shift m)) := by simp [Syn.shift]

/-- All of `1, …, m` are smooth for the primorial: `∑_{i<m} ⌊F/(i+1)⌋ ≤ Sm(A(m+1))`. -/
theorem harmonic_le_Sm (m F : PTm n) :
    Γ ⊢[PRAAx] le (Harmonic.S m F) (Sm (A (succ m)) m F (succ m)) := by
  have e : Γ ⊢[PRAAx] Harmonic.S m F ≐ ap2 (sumF (shiftBody gB)) m (par (A (succ m)) m F) := by
    refine sum_congr_bounded hB (shiftBody gB) F (par (A (succ m)) m F) m (.allI (.impI ?_))
    rw [inst2_h, inst2_shiftBody, shift_par, shift_A_succ]
    have hs : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx]
        (succ (var 0) : PTm (n + 1)) ≐ succ (pred (succ (var 0))) := congrSucc (pred_succ _).eqSymm
    exact ((g_at _ _ _ _).eqTrans (term_pos hs (smooth_all hs Prf.hyp0))).eqSymm
  exact le_congr e.eqSymm (.eqRefl _)
    (le_of_eq_add (d := inst2 gB zero (par (A (succ m)) m F)) ((sum_shift gB m _).eqTrans (add_comm _ _)))

/-- `lem:euler-domination`: `(∑_{i=1}^{m} ⌊F/i⌋) · DenE_m ≤ F · ProdP_m`; with `F = m!` this is
`NumH_m · DenE_m ≤ Fact_m · ProdP_m`, i.e. `H_m ≤ E_m`. -/
theorem euler_domination (m F : PTm n) : Γ ⊢[PRAAx] le (Harmonic.S m F * DenE m) (F * ProdP m) :=
  le_trans (le_mul_mono (harmonic_le_Sm m F) (le_refl _)) (main (succ m) m F (succ m))

/-! ## Positivity of `DenE` -/

theorem dBt_pos (N : PTm n) : Γ ⊢[PRAAx] dBt N ≐ succ (pred (dBt N)) := by
  refine .orE (isP_01 N) ?_ ?_
  · exact eq_succ_pred (dBt_zero Prf.hyp0)
  · exact eq_succ_pred ((dBt_one Prf.hyp0).eqTrans
      ((congrPred (prime_eq_succ_succ (prime_of_isP Prf.hyp0))).eqTrans (pred_succ _)))

theorem Dn_pos_step {N : PTm n} (ih : Γ ⊢[PRAAx] Dn N ≐ succ (pred (Dn N))) :
    Γ ⊢[PRAAx] Dn (succ N) ≐ succ (pred (Dn (succ N))) :=
  eq_succ_pred ((Dn_succ N).eqTrans (pos_mul ih (dBt_pos N)))

private abbrev dposF : Fm PTm 1 := Dn (var 0) ≐ succ (pred (Dn (var 0)))

private theorem Dn_pos₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] dposF := by
  ipra_ind [subst_ap2]
  · exact eq_succ_pred (prod_zero _ _)
  · exact Dn_pos_step Prf.hyp0

theorem Dn_pos (N : PTm n) : Γ ⊢[PRAAx] Dn N ≐ succ (pred (Dn N)) := by
  have h := inst (Γ := Γ) Dn_pos₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## The harmonic upper bound and the main theorem -/

/-- `cor:harmonic-upper`: `NumP_m ≤ k · ProdP_m → ∑_{i=1}^{m} ⌊F/i⌋ ≤ 4^k · F`; with `F = m!`,
`NumH_m ≤ 4^k · Fact_m`. -/
theorem harmonic_upper {m k : PTm n} (F : PTm n) (h : Γ ⊢[PRAAx] le (NumP m) (k * ProdP m)) :
    Γ ⊢[PRAAx] le (Harmonic.S m F) (pw (two * two) k * F) := by
  have ed := euler_domination (Γ := Γ) m F
  have sb := le_mul_mono (le_refl F) (sum_bounds_product h)
  have hD := Dn_pos (Γ := Γ) (succ m)
  have c : Γ ⊢[PRAAx] le (DenE m * Harmonic.S m F) (DenE m * (pw (two * two) k * F)) := by
    refine le_congr (mul_comm _ _) ?_ (le_trans ed sb)
    ipra_ring
  exact mul_le_cancel (le_congr (congrMul hD (.eqRefl _)) (congrMul hD (.eqRefl _)) c)

/-- The witness `Wit(k) = 2^{2·4^k}`. -/
abbrev Wit (k : PTm n) : PTm n := pw two (two * pw (two * two) k)

/-- `thm:main`: `∑_{p ≤ n} 1/p > k` for `n = Wit(k)`, as `k · ProdP_n < NumP_n`. -/
theorem prime_reciprocal_at (k : PTm n) : Γ ⊢[PRAAx] lt (k * ProdP (Wit k)) (NumP (Wit k)) := by
  refine .orE (lt_or_le (k * ProdP (Wit k)) (NumP (Wit k))) Prf.hyp0 ?_
  have hu := harmonic_upper (fact (Wit k)) (Prf.hyp0 : (le (NumP (Wit k)) (k * ProdP (Wit k)) :: Γ) ⊢[PRAAx] _)
  have hd := Harmonic.harmonic_dyadic (Γ := le (NumP (Wit k)) (k * ProdP (Wit k)) :: Γ) (pw (two * two) k)
  have hF := fact_pos (Γ := le (NumP (Wit k)) (k * ProdP (Wit k)) :: Γ) (Wit k)
  have c := le_trans hd hu
  refine not_succ_le_self (pw (two * two) k * fact (Wit k) + pred (fact (Wit k))) _ ?_
  refine le_trans (le_congr ?_ (.eqRefl _) c) (le_of_eq_add (d := pred (fact (Wit k))) (.eqRefl _))
  ipra_lc natEq hF

/-- `thm:main`, variable `0 = k`. -/
abbrev primeReciprocalFormula : Fm PTm 1 := lt (var 0 * ProdP (Wit (var 0))) (NumP (Wit (var 0)))

theorem prime_reciprocal : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 primeReciprocalFormula :=
  closeUniv 1 (prime_reciprocal_at _)

end LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination
