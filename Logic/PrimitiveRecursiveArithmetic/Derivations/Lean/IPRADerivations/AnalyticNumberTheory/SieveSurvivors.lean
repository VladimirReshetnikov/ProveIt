import IPRADerivations.AnalyticNumberTheory.LegendreSieve
import IPRADerivations.AnalyticNumberTheory.PrimeRank
import IPRADerivations.AnalyticNumberTheory.SieveCriterion
import IPRADerivations.AnalyticNumberTheory.ValuationAdd

/-!
# The survivors of the sieve, and Legendre's formula for `π`

Packets: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, Corollary
`an:sievepi` ("For `X ≥ 2` and `z = ⌊√X⌋`, `π(X) = S(X, z) + π(z) − 1`"), and
`analytic-number-theory/prime-counting-ipra`, `sections/sieve.tex` (Legendre's formula).

`S(x, z)` is the number of `1 ≤ m ≤ x` coprime to the primorial `P(z) = ∏_{p ≤ z} p`
(`PrimorialUpper.pri`, `LegendreSieve.coB`). The packet's argument: "A composite `n ≤ X` has a prime factor at
most `√n ≤ z` […]. Thus the survivors are exactly `1` and the primes `z < p ≤ X`. All comparisons can use
squares, without real square roots."

* `dvd_pri`, `le_of_dvd_pri`: a prime `q` divides `P(z)` exactly when `q ≤ z` (`PrimorialUpper.val_pri`);
* `surv_small`, `surv_prime`, `surv_comp`: for `m ≥ 2`, `[gcd(m, P(z)) = 1]` is `0` when `m ≤ z`, `1` when `m`
  is a prime above `z`, and `0` when `m` is composite below `(z + 1)²` (its least prime factor `ℓ` has
  `ℓ² ≤ m < (z + 1)²`, `SieveCriterion.lpf_sq_le`);
* `survivors`: for `x < (z + 1)²`, `S(x, z) + π(min(x, z)) = [x ≥ 1] + π(x)`, by induction on `x`;
* **`sieve_pi`**: for `1 ≤ x`, `z ≤ x < (z + 1)²`: `S(x, z) + π(z) = 1 + π(x)`;
* **`sieve_pi_sqrt`** (`an:sievepi`): the same at `z = ⌊√x⌋`;
* **`legendre_pi`**: with `LegendreSieve.legendre_sieve`,
  `∑_{d ≤ x, d ∣ P(z)} μ⁺(d) ⌊x/d⌋ + π(z) = 1 + π(x) + ∑_{d ≤ x, d ∣ P(z)} μ⁻(d) ⌊x/d⌋` at `z = ⌊√x⌋`, that is
  `π(x) = ∑_{d ∣ P(√x)} μ(d) ⌊x/d⌋ + π(√x) − 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveSurvivors

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos not_dvd_one)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd (le_val_of_dvd dvd_of_le_val)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (lpf_prime' lpf_dvd' one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveCriterion (lpf_sq_le prime_of_lpf_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialUpper (pri pri_pos val_pri)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank (pc pc_zero pc_succ isP_small congrPc)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB)
open LeanProofs.IPRA.AnalyticNumberTheory.LegendreSieve (wB coB inst2_coB legendre_sieve)
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The prime divisors of the primorial -/

theorem sz_alg {z q d : PTm n} (e : Γ ⊢[PRAAx] z ≐ q + d) : Γ ⊢[PRAAx] succ z ≐ q + succ d := by
  ipra_lc natEq e

/-- A prime `q ≤ z` divides `P(z)`. -/
theorem dvd_pri {q z : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h : Γ ⊢[PRAAx] le q z) : Γ ⊢[PRAAx] dvd q (pri z) := by
  have hq2 := prime_two hq
  have m1 : Γ ⊢[PRAAx] monus (succ z) q ≐ succ (monus z q) := monus_of_eq (sz_alg (eq_add_of_le h))
  have v : Γ ⊢[PRAAx] val q (pri z) ≐ one := (val_pri hq z).eqTrans ((congrSg m1).eqTrans (sg_succ _))
  have d := dvd_of_le_val (m := pri z) (t := one) hq2 (le_congr (.eqRefl _) v.eqSymm (le_refl one))
  exact (congrAp2 remF (.eqRefl _) (pw_one q).eqSymm).eqTrans d

/-- A prime divisor of `P(z)` is at most `z`. -/
theorem le_of_dvd_pri {q z : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h : Γ ⊢[PRAAx] dvd q (pri z)) :
    Γ ⊢[PRAAx] le q z := by
  have hq2 := prime_two hq
  have d1 : Γ ⊢[PRAAx] dvd (pw q one) (pri z) := (congrAp2 remF (.eqRefl _) (pw_one q)).eqTrans h
  have l := le_val_of_dvd hq2 (pri_pos z) d1
  refine .orE (lt_or_le z q) ?_ Prf.hyp0
  have hl : (lt z q :: Γ) ⊢[PRAAx] monus (succ z) q ≐ zero := Prf.hyp0
  have v0 : (lt z q :: Γ) ⊢[PRAAx] val q (pri z) ≐ zero :=
    (val_pri hq.wk z).eqTrans ((congrSg hl).eqTrans sg_zero)
  exact lt_zero_absurd _ (le_congr (.eqRefl _) v0 l.wk)

/-- A common prime divisor makes the coprimality bit `0`. -/
theorem not_coprime {m P q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h1 : Γ ⊢[PRAAx] dvd q m)
    (h2 : Γ ⊢[PRAAx] dvd q P) : Γ ⊢[PRAAx] eqb (gcd m P) one ≐ zero := by
  have hq2 := prime_two hq
  refine eqb_of_ne (.impI ?_)
  have hg : ((gcd m P ≐ one) :: Γ) ⊢[PRAAx] gcd m P ≐ one := Prf.hyp0
  exact .impE (not_dvd_one hq2.wk) (dvd_congr hg (gcd_greatest' (p_pos hq2).wk h1.wk h2.wk))

/-! ## The three kinds of `m ≥ 2` -/

/-- `2 ≤ m ≤ z` is not a survivor. -/
theorem surv_small {m z : PTm n} (h2 : Γ ⊢[PRAAx] le two m) (hmz : Γ ⊢[PRAAx] le m z) :
    Γ ⊢[PRAAx] eqb (gcd m (pri z)) one ≐ zero := by
  have hq := lpf_prime' h2
  have hd := lpf_dvd' h2
  have hl : Γ ⊢[PRAAx] le (lpf m) m := dvd_le' (p_pos (prime_two hq)) hd (p_pos h2)
  exact not_coprime hq hd (dvd_pri hq (le_trans hl hmz))

/-- A prime above `z` is a survivor. -/
theorem surv_prime {m z : PTm n} (hp : Γ ⊢[PRAAx] prime m) (hz : Γ ⊢[PRAAx] lt z m) :
    Γ ⊢[PRAAx] eqb (gcd m (pri z)) one ≐ one := by
  refine eqb_of_eq (gcd_prime hp (.impI ?_))
  have l := le_of_dvd_pri hp.wk (Prf.hyp0 (Γ := Γ) (φ := dvd m (pri z)))
  exact lt_irrefl z _ (le_trans hz.wk l)

/-- A composite `m < (z + 1)²` is not a survivor. -/
theorem surv_comp {m z : PTm n} (h2 : Γ ⊢[PRAAx] le two m) (hI : Γ ⊢[PRAAx] isP m ≐ zero)
    (hB : Γ ⊢[PRAAx] lt m (succ z * succ z)) : Γ ⊢[PRAAx] eqb (gcd m (pri z)) one ≐ zero := by
  have hne : Γ ⊢[PRAAx] neg (lpf m ≐ m) :=
    .impI (one_ne_zero _ ((isP_of_prime (prime_of_lpf_eq h2.wk Prf.hyp0)).eqSymm.eqTrans hI.wk))
  have sq := lpf_sq_le h2 hne
  have hq := lpf_prime' h2
  have hqz : Γ ⊢[PRAAx] le (lpf m) z := by
    refine .orE (lt_or_le z (lpf m)) ?_ Prf.hyp0
    have hl : (lt z (lpf m) :: Γ) ⊢[PRAAx] le (succ z) (lpf m) := Prf.hyp0
    have sq' := sq.wk (ψ := lt z (lpf m))
    have hB' := hB.wk (ψ := lt z (lpf m))
    have bad : (lt z (lpf m) :: Γ) ⊢[PRAAx] le one zero := by
      ipra_le sl hB' + sl sq' + sl hl * (𝔞 (lpf m) + 𝔞 z + 1)
    exact lt_zero_absurd _ bad
  exact not_coprime hq (lpf_dvd' h2) (dvd_pri hq hqz)

/-! ## The minimum and the step -/

/-- `min(a, b)`. -/
abbrev mn (a b : PTm n) : PTm n := monus a (monus a b)

theorem mn_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] mn a b ≐ a :=
  (congrMonus (.eqRefl a) h).eqTrans (monus_zero a)

theorem mn_ge {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx] mn a b ≐ b :=
  monus_of_eq ((eq_add_of_le h).eqTrans (add_comm _ _))

theorem pc_one : Γ ⊢[PRAAx] pc (one : PTm n) ≐ zero :=
  (pc_succ zero).eqTrans ((congrAdd pc_zero (isP_small (le_refl one))).eqTrans (zero_add zero))

theorem pt0_alg {T M' E I M : PTm n} (a : Γ ⊢[PRAAx] T ≐ one) (b : Γ ⊢[PRAAx] M' ≐ zero)
    (c : Γ ⊢[PRAAx] E ≐ one) (d : Γ ⊢[PRAAx] I ≐ zero) (e : Γ ⊢[PRAAx] M ≐ zero) :
    Γ ⊢[PRAAx] T + M' ≐ (E + I) + M := by
  ipra_lc natEq a + natEq b - natEq c - natEq d - natEq e

theorem pt1_alg {T I M' M E Z : PTm n} (a : Γ ⊢[PRAAx] T ≐ I) (b : Γ ⊢[PRAAx] M' ≐ Z)
    (c : Γ ⊢[PRAAx] E ≐ zero) (d : Γ ⊢[PRAAx] M ≐ Z) : Γ ⊢[PRAAx] T + M' ≐ (E + I) + M := by
  ipra_lc natEq a + natEq b - natEq c - natEq d

theorem pt2_alg {T M' px I E M : PTm n} (a : Γ ⊢[PRAAx] T ≐ zero) (b : Γ ⊢[PRAAx] M' ≐ px + I)
    (c : Γ ⊢[PRAAx] E ≐ zero) (d : Γ ⊢[PRAAx] M ≐ px) : Γ ⊢[PRAAx] T + M' ≐ (E + I) + M := by
  ipra_lc natEq a + natEq b - natEq c - natEq d

/-- The term at `m = x + 1`: `[gcd(m, P(z)) = 1] + π(min(m, z)) = [m = 1] + [m prime] + π(min(m − 1, z))`
for `m < (z + 1)²`. -/
theorem pt_step {x z : PTm n} (hB : Γ ⊢[PRAAx] lt (succ x) (succ z * succ z)) :
    Γ ⊢[PRAAx] eqb (gcd (succ x) (pri z)) one + pc (mn (succ x) z) ≐
      (eqb (succ x) one + isP (succ x)) + pc (mn x z) := by
  refine .orE (zero_or_succ x) ?_ ?_
  · -- `m = 1`
    let C : List (Fm PTm n) := (x ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] x ≐ zero := Prf.hyp0
    have e1 : C ⊢[PRAAx] succ x ≐ one := congrSucc h0
    have hpos : C ⊢[PRAAx] succ x ≐ succ (pred (succ x)) := congrSucc (pred_succ x).eqSymm
    have T1 : C ⊢[PRAAx] eqb (gcd (succ x) (pri z)) one ≐ one :=
      eqb_of_eq (eq_one_of_dvd_one (gcd_pos hpos) (dvd_congr e1 (Prf.andE₁ (gcd_dvd' (b := pri z) hpos))))
    have E1 : C ⊢[PRAAx] eqb (succ x) one ≐ one := eqb_of_eq e1
    have I0 : C ⊢[PRAAx] isP (succ x) ≐ zero := isP_small (le_congr e1.eqSymm (.eqRefl _) (le_refl one))
    have M0 : C ⊢[PRAAx] pc (mn x z) ≐ zero :=
      (congrPc ((congrMonus h0 (.eqRefl _)).eqTrans (zero_monus _))).eqTrans pc_zero
    have M1 : C ⊢[PRAAx] pc (mn (succ x) z) ≐ zero := by
      refine .orE (zero_or_succ z) ?_ ?_
      · have z0 : ((z ≐ zero) :: C) ⊢[PRAAx] z ≐ zero := Prf.hyp0
        have a : ((z ≐ zero) :: C) ⊢[PRAAx] mn (succ x) z ≐ zero :=
          (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) z0).eqTrans (monus_zero _))).eqTrans (monus_self _)
        exact (congrPc a).eqTrans pc_zero
      · have zp : ((z ≐ succ (pred z)) :: C) ⊢[PRAAx] z ≐ succ (pred z) := Prf.hyp0
        have l : ((z ≐ succ (pred z)) :: C) ⊢[PRAAx] le (succ x) z :=
          le_congr e1.wk.eqSymm (.eqRefl _) (one_le_pos zp)
        exact (congrPc ((mn_le l).eqTrans e1.wk)).eqTrans pc_one
    exact pt0_alg T1 M1 E1 I0 M0
  · -- `m ≥ 2`
    let C : List (Fm PTm n) := (x ≐ succ (pred x)) :: Γ
    have hx : C ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
    have h2 : C ⊢[PRAAx] le two (succ x) := (succ_monus_succ _ _).eqTrans (one_le_pos hx)
    have E0 : C ⊢[PRAAx] eqb (succ x) one ≐ zero := eqb_zero_of_gt h2
    refine .orE (lt_or_le z (succ x)) ?_ ?_
    · -- `z < m`
      let D : List (Fm PTm n) := lt z (succ x) :: C
      have hz : D ⊢[PRAAx] lt z (succ x) := Prf.hyp0
      have lzx : D ⊢[PRAAx] le z x := (succ_monus_succ z x).eqSymm.eqTrans hz
      have ma : D ⊢[PRAAx] mn (succ x) z ≐ z := mn_ge (le_of_lt hz)
      have mb : D ⊢[PRAAx] mn x z ≐ z := mn_ge lzx
      have TI : D ⊢[PRAAx] eqb (gcd (succ x) (pri z)) one ≐ isP (succ x) := by
        refine .orE (isP_01 (succ x)) ?_ ?_
        · exact (surv_comp h2.wk.wk Prf.hyp0 hB.wk.wk.wk).eqTrans Prf.hyp0.eqSymm
        · exact (surv_prime (prime_of_isP Prf.hyp0) hz.wk).eqTrans Prf.hyp0.eqSymm
      exact pt1_alg TI (congrPc ma) E0.wk (congrPc mb)
    · -- `m ≤ z`
      let D : List (Fm PTm n) := le (succ x) z :: C
      have hl : D ⊢[PRAAx] le (succ x) z := Prf.hyp0
      have T0 := surv_small h2.wk hl
      have ma : D ⊢[PRAAx] pc (mn (succ x) z) ≐ pc x + isP (succ x) :=
        (congrPc (mn_le hl)).eqTrans (pc_succ x)
      have mb : D ⊢[PRAAx] pc (mn x z) ≐ pc x := congrPc (mn_le (le_trans (le_succ_self x) hl))
      exact pt2_alg T0 ma E0.wk mb

theorem sg_step (x : PTm n) : Γ ⊢[PRAAx] sg x + eqb (succ x) one ≐ one := by
  refine .orE (zero_or_succ x) ?_ ?_
  · have h0 : ((x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp0
    exact (congrAdd ((congrSg h0).eqTrans sg_zero) (eqb_of_eq (congrSucc h0))).eqTrans (zero_add one)
  · have hx : ((x ≐ succ (pred x)) :: Γ) ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
    exact (congrAdd ((congrSg hx).eqTrans (sg_succ _))
      (eqb_zero_of_gt ((succ_monus_succ _ _).eqTrans (one_le_pos hx)))).eqTrans (add_zero one)

theorem fin_alg {U' U s1 T M' E I M sx px px' : PTm n} (a : Γ ⊢[PRAAx] U' ≐ U + s1 * T)
    (b : Γ ⊢[PRAAx] s1 ≐ one) (c : Γ ⊢[PRAAx] T + M' ≐ (E + I) + M) (d : Γ ⊢[PRAAx] U + M ≐ sx + px)
    (e : Γ ⊢[PRAAx] sx + E ≐ one) (f : Γ ⊢[PRAAx] px' ≐ px + I) : Γ ⊢[PRAAx] U' + M' ≐ s1 + px' := by
  have a' := natEq a; have b' := natEq b; have c' := natEq c; have d' := natEq d; have e' := natEq e
  ipra_lc a' + (𝔞 T - 1) * b' + c' + d' + e' - natEq f

/-! ## The induction on `x` -/

theorem surv_zero {z : PTm n} :
    Γ ⊢[PRAAx] ap2 (sumF coB) (succ zero) (pri z) + pc (mn zero z) ≐ sg zero + pc zero := by
  have ss := sum_succ' (Γ := Γ) coB zero (pri z)
  rw [inst2_coB] at ss
  have U0 : Γ ⊢[PRAAx] ap2 (sumF coB) (succ zero) (pri z) ≐ zero :=
    ss.eqTrans ((congrAdd (sum_zero coB (pri z)) (zero_mul_l sg_zero _)).eqTrans (zero_add zero))
  exact congrAdd (U0.eqTrans sg_zero.eqSymm) (congrPc (zero_monus _))

theorem surv_step {x z : PTm n} (hB : Γ ⊢[PRAAx] lt (succ x) (succ z * succ z))
    (ih : Γ ⊢[PRAAx] ap2 (sumF coB) (succ x) (pri z) + pc (mn x z) ≐ sg x + pc x) :
    Γ ⊢[PRAAx] ap2 (sumF coB) (succ (succ x)) (pri z) + pc (mn (succ x) z) ≐ sg (succ x) + pc (succ x) := by
  have ss := sum_succ' (Γ := Γ) coB (succ x) (pri z)
  rw [inst2_coB] at ss
  exact fin_alg ss (sg_succ x) (pt_step hB) ih (sg_step x) (pc_succ x)

/-- Variables: `0 = x`, `1 = z`. -/
abbrev survF : Fm PTm 2 :=
  lt (var 0) (succ (var 1) * succ (var 1)) ⟶
    (ap2 (sumF coB) (succ (var 0)) (pri (var 1)) + pc (mn (var 0) (var 1)) ≐ sg (var 0) + pc (var 0))

theorem surv_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] survF := by
  ipra_ind (⟨lt_QF _ _, trivial⟩) [subst_lt, subst_ap2]
  · exact .impI surv_zero
  · exact .impI (surv_step Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))

/-- For `x < (z + 1)²`: `S(x, z) + π(min(x, z)) = [x ≥ 1] + π(x)`. -/
theorem survivors {x z : PTm n} (hB : Γ ⊢[PRAAx] lt x (succ z * succ z)) :
    Γ ⊢[PRAAx] ap2 (sumF coB) (succ x) (pri z) + pc (mn x z) ≐ sg x + pc x := by
  have i := inst (Γ := Γ) surv_open (![x, z] : Fin 2 → PTm n)
  simp only [survF, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at i
  exact .impE i hB

/-! ## Legendre's formula -/

/-- **The survivors of the sieve**: for `1 ≤ x` and `z ≤ x < (z + 1)²`, `S(x, z) + π(z) = 1 + π(x)`. -/
theorem sieve_pi {x z : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hzx : Γ ⊢[PRAAx] le z x)
    (hB : Γ ⊢[PRAAx] lt x (succ z * succ z)) :
    Γ ⊢[PRAAx] ap2 (sumF coB) (succ x) (pri z) + pc z ≐ one + pc x :=
  (congrAdd (.eqRefl _) (congrPc (mn_ge hzx)).eqSymm).eqTrans
    ((survivors hB).eqTrans (congrAdd (sg_pos (pos_of_one_le hx)) (.eqRefl _)))

theorem sq_succ (s : PTm n) : Γ ⊢[PRAAx] (s + one) * (s + one) ≐ succ s * succ s := by
  ipra_ring

/-- **`an:sievepi`**: for `x ≥ 1` and `z = ⌊√x⌋`, `S(x, z) + π(z) = 1 + π(x)`. -/
theorem sieve_pi_sqrt {x : PTm n} (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] ap2 (sumF coB) (succ x) (pri (isqrt x)) + pc (isqrt x) ≐ one + pc x :=
  sieve_pi hx (isqrt_le_self x) (lt_congr (.eqRefl _) (sq_succ _) (lt_isqrt_succ_sq x))

theorem comb {A S Bn Pz R : PTm n} (h1 : Γ ⊢[PRAAx] A ≐ S + Bn) (h2 : Γ ⊢[PRAAx] S + Pz ≐ R) :
    Γ ⊢[PRAAx] A + Pz ≐ R + Bn := by
  ipra_lc natEq h1 + natEq h2

/-- **Legendre's formula for `π`**: at `z = ⌊√x⌋`, `x ≥ 1`,
`∑_{d ≤ x} [d ∣ P(z)] μ⁺(d) ⌊x/d⌋ + π(z) = 1 + π(x) + ∑_{d ≤ x} [d ∣ P(z)] μ⁻(d) ⌊x/d⌋`. -/
theorem legendre_pi {x : PTm n} (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] ap2 (sumF (RB (wB aPB) one)) (succ x) (pairT x (pri (isqrt x))) + pc (isqrt x) ≐
      (one + pc x) + ap2 (sumF (RB (wB aNB) one)) (succ x) (pairT x (pri (isqrt x))) :=
  comb (legendre_sieve x (pri (isqrt x))) (sieve_pi_sqrt hx)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveSurvivors
