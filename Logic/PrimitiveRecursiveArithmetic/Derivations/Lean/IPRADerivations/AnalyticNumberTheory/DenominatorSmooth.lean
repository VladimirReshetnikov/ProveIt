import IPRADerivations.AnalyticNumberTheory.DenominatorModulus

/-!
# The left endpoint of the denominator bound: `H_q(z) ≤ S_{A_q(z)}(z)`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the proof of
`eq:sieve-denominator`: every `n ≤ z` coprime to `q` is a product of primes `p ≤ z` with `p ∤ q`.

With `A_q(y) = ∏_{p ≤ y, gcd(p, q) = 1} p` (`DenominatorModulus.Aq`):

* `prime_dvd_Aq`: a prime `p ≤ y` with `gcd(p, q) = 1` divides `A_q(y)`;
* `Aq_dvd_mono`: `A_q(y) ∣ A_q(y')` for `y ≤ y'`;
* `sm_core`, `sm_step`, **`smooth_coprime`**: `m ≥ 1` and `gcd(m, q) = 1` give `m ∣ A_q(m)^m`, by strong
  induction through the least prime factor (as `Smooth.smooth_self`, with the coprimality carried as a bit of
  the violation);
* **`dvd_Aq_pow`**: for `1 ≤ m ≤ z` coprime to `q`, `m ∣ A_q(z)^z`;
* `sum_le2`: comparison of two bounded sums with different parameters;
* **`Hq_le`**: `H_q(z) = ∑_{1 ≤ m ≤ z} [gcd(m, q) = 1] ⌊F/m⌋ ≤ ∑_{1 ≤ m ≤ z} [m ∣ A_q(z)^z] ⌊F/m⌋`.

With `DenominatorModulus.smooth_le_totient` (at `L = z`, `F = z!`) this gives
`H_q(z) ≤ ∑_{d ≤ z} [d ∣ A_q(z)] ⌊z!/φ(d)⌋` (**`Hq_le_G`**).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DenominatorSmooth

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_of_prime pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd (dvd_of_le_val)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg congrEqb' zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (PE XE inst2_XE val_PE)
open LeanProofs.IPRA.AnalyticNumberTheory.Smooth (dvd_mul_mul pw_dvd_base pw_dvd_exp K_eq lpf_two K_split
  cof_pos cof_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveSurvivors (sz_alg)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (Sm gB par g_at term term_pos le_zero_of)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientSumStep (Gs)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorModulus (Aq Aq_pos Aq_succ smooth_le_totient)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Divisibility in the modulus -/

/-- A prime `p ≤ y` with `gcd(p, q) = 1` divides `A_q(y)`. -/
theorem prime_dvd_Aq {p y q : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p q ≐ one)
    (hpy : Γ ⊢[PRAAx] le p y) : Γ ⊢[PRAAx] dvd p (Aq y q) := by
  have hp2 := prime_two hp
  have m1 : Γ ⊢[PRAAx] monus (succ y) p ≐ succ (monus y p) := monus_of_eq (sz_alg (eq_add_of_le hpy))
  have e := val_PE hp totBody (succ y) q
  rw [inst2_XE, inst2_tot] at e
  have v : Γ ⊢[PRAAx] val p (Aq y q) ≐ one :=
    e.eqTrans ((congrMul ((congrMul (isP_of_prime hp) (eqb_of_eq hc)).eqTrans (one_mul one))
      ((congrSg m1).eqTrans (sg_succ _))).eqTrans (one_mul one))
  have d := dvd_of_le_val (m := Aq y q) (t := one) hp2 (le_congr (.eqRefl _) v.eqSymm (le_refl one))
  exact (congrAp2 remF (.eqRefl _) (pw_one p).eqSymm).eqTrans d

theorem Aq_dvd_step {y d q : PTm n} (ih : Γ ⊢[PRAAx] dvd (Aq y q) (Aq (y + d) q)) :
    Γ ⊢[PRAAx] dvd (Aq y q) (Aq (y + succ d) q) :=
  dvd_congr ((Aq_succ (y + d) q).eqSymm.eqTrans
    (congrAp2 (prodF (PE totBody)) (congrSucc (add_succ y d).eqSymm) (.eqRefl _)))
    (dvd_mul' (Aq_pos y q) _ ih)

/-- Variables: `0 = d`, `1 = y`, `2 = q`. -/
abbrev monoF : Fm PTm 3 :=
  dvd (ap2 (prodF (PE totBody)) (succ (var 1)) (var 2)) (ap2 (prodF (PE totBody)) (succ (var 1 + var 0)) (var 2))

theorem mono_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] monoF := by
  ipra_ind [subst_ap2]
  · exact dvd_congr (congrAp2 (prodF (PE totBody)) (congrSucc (add_zero (var 0)).eqSymm) (.eqRefl _))
      (dvd_self' (Aq_pos (var 0) (var 1)))
  · exact Aq_dvd_step (Prf.hyp0 (Γ := []) (φ := monoF))

/-- `A_q(y) ∣ A_q(y')` for `y ≤ y'`. -/
theorem Aq_dvd_mono {y y' : PTm n} (q : PTm n) (h : Γ ⊢[PRAAx] le y y') :
    Γ ⊢[PRAAx] dvd (Aq y q) (Aq y' q) := by
  have i := inst (Γ := Γ) mono_open (![monus y' y, y, q] : Fin 3 → PTm n)
  simp only [monoF, Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at i
  exact dvd_congr (congrAp2 (prodF (PE totBody)) (congrSucc (eq_add_of_le h).eqSymm) (.eqRefl _)) i

/-! ## Peeling the least prime factor -/

/-- `K ≥ 2`, `gcd(K, q) = 1`, and the cofactor `m = K/ℓ(K)` with `m ∣ A_q(m)^m`, give `K ∣ A_q(K)^K`. -/
theorem sm_core {K q : PTm n} (hK : Γ ⊢[PRAAx] le two K) (hc : Γ ⊢[PRAAx] gcd K q ≐ one)
    (hm : Γ ⊢[PRAAx] dvd (quo K (lpf K)) (pw (Aq (quo K (lpf K)) q) (quo K (lpf K)))) :
    Γ ⊢[PRAAx] dvd K (pw (Aq K q) K) := by
  have split := lpf_two hK
  have hp := split.andE₁
  have hpPos := prime_eq_succ_pred hp
  have hpK := dvd_le' hpPos split.andE₂ (eq_succ_pred (K_eq hK))
  have hcp := coprime_dvd_left hpPos split.andE₂ hc
  exact Smooth.dvd_pow_of_lpf_and_cofactor hK (Aq_pos _ _) (Aq_pos _ _)
    (prime_dvd_Aq hp hcp hpK) hm (Aq_dvd_mono q (le_of_lt (cof_lt hK)))

/-! ## The strong induction -/

/-- The violation `[m ≥ 1][gcd(m, q) = 1][m ∤ A_q(m)^m]`, over `0 = m`, `1 = q`. -/
abbrev vB : PTm 2 :=
  sg (var 0) * (eqb (gcd (var 0) (var 1)) one *
    sg (rem (pw (ap2 (prodF (PE totBody)) (succ (var 0)) (var 1)) (var 0)) (var 0)))

theorem inst2_v (m q : PTm n) :
    inst2 vB m q = sg m * (eqb (gcd m q) one * sg (rem (pw (Aq m q) m) m)) := by
  simp only [inst2, PTm.subst_mul, PTm.subst_monus, subst_eqb, subst_ex2, subst_ap2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem bits_alg {s b X : PTm n} (hs : Γ ⊢[PRAAx] s ≐ one) (hb : Γ ⊢[PRAAx] b ≐ one)
    (h : Γ ⊢[PRAAx] s * (b * X) ≐ zero) : Γ ⊢[PRAAx] X ≐ zero := by
  ipra_lc natEq h - 𝔞 b * 𝔞 X * natEq hs - 𝔞 X * natEq hb

theorem of_viol {m q : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hc : Γ ⊢[PRAAx] gcd m q ≐ one)
    (h : Γ ⊢[PRAAx] sg m * (eqb (gcd m q) one * sg (rem (pw (Aq m q) m) m)) ≐ zero) :
    Γ ⊢[PRAAx] dvd m (pw (Aq m q) m) :=
  sg_zero_inv (bits_alg ((congrSg hm).eqTrans (sg_succ _)) (eqb_of_eq hc) h)

theorem viol_of {m q : PTm n} (h : Γ ⊢[PRAAx] dvd m (pw (Aq m q) m)) :
    Γ ⊢[PRAAx] sg m * (eqb (gcd m q) one * sg (rem (pw (Aq m q) m) m)) ≐ zero :=
  (congrMul (.eqRefl _) ((congrMul (.eqRefl _) ((congrSg h).eqTrans sg_zero)).eqTrans (mul_zero _))).eqTrans
    (mul_zero _)

theorem two_alg {K P Q : PTm n} (h1 : Γ ⊢[PRAAx] K ≐ succ P) (h2 : Γ ⊢[PRAAx] P ≐ succ Q) :
    Γ ⊢[PRAAx] K ≐ two + Q := by
  ipra_lc natEq h1 + natEq h2

theorem sm_step {K q : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) K q ≐ zero) :
    Γ ⊢[PRAAx] sg K * (eqb (gcd K q) one * sg (rem (pw (Aq K q) K) K)) ≐ zero := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _
  · let C : List (Fm PTm n) := (K ≐ succ (pred K)) :: Γ
    have hKp : C ⊢[PRAAx] K ≐ succ (pred K) := Prf.hyp0
    refine .orE (eqb_cases (gcd K q) one) ?_ ?_
    · exact (congrMul (.eqRefl _) (zero_mul_l Prf.hyp0 _)).eqTrans (mul_zero _)
    · let D : List (Fm PTm n) := (eqb (gcd K q) one ≐ one) :: C
      have hc : D ⊢[PRAAx] gcd K q ≐ one := eq_of_eqb Prf.hyp0
      refine .orE (zero_or_succ (pred K)) ?_ ?_
      · -- `K = 1`
        have e1 : ((pred K ≐ zero) :: D) ⊢[PRAAx] K ≐ one := hKp.wk.wk.eqTrans (congrSucc Prf.hyp0)
        exact viol_of (dvd_congr_left e1.eqSymm (dvd_of_eq' (congrSucc (pred_succ _).eqSymm)
          (w := pw (Aq K q) K) (one_mul _).eqSymm))
      · -- `K ≥ 2`
        let E : List (Fm PTm n) := (pred K ≐ succ (pred (pred K))) :: D
        have hK : E ⊢[PRAAx] le two K := le_of_eq_add (two_alg hKp.wk.wk Prf.hyp0)
        have mpos := cof_pos hK
        have z := sum_zero_elim vB ih.wk.wk.wk (cof_lt hK)
        rw [inst2_v] at z
        have dmK : E ⊢[PRAAx] dvd (quo K (lpf K)) K :=
          dvd_of_eq' mpos ((K_split hK).eqTrans (mul_comm _ _))
        have hcm : E ⊢[PRAAx] gcd (quo K (lpf K)) q ≐ one := coprime_dvd_left mpos dmK hc.wk
        exact viol_of (sm_core hK hc.wk (of_viol mpos hcm z))

/-- **Every `m ≥ 1` coprime to `q` divides `A_q(m)^m`**. -/
theorem smooth_coprime {m q : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hc : Γ ⊢[PRAAx] gcd m q ≐ one) :
    Γ ⊢[PRAAx] dvd m (pw (Aq m q) m) := by
  have h := strong_ind (Γ := Γ) vB (fun N x hS => by rw [inst2_v]; exact sm_step hS) m q
  rw [inst2_v] at h
  exact of_viol hm hc h

/-- **For `1 ≤ m ≤ z` coprime to `q`, `m ∣ A_q(z)^z`**. -/
theorem dvd_Aq_pow {m z q : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hc : Γ ⊢[PRAAx] gcd m q ≐ one)
    (hmz : Γ ⊢[PRAAx] le m z) : Γ ⊢[PRAAx] dvd m (pw (Aq z q) z) :=
  dvd_trans' hm (pw_pos' (Aq_pos _ _) _)
    (dvd_trans' hm (pw_pos' (Aq_pos _ _) _) (smooth_coprime hm hc)
      (pw_dvd_base _ (Aq_pos _ _) (Aq_dvd_mono q hmz)))
    (pw_dvd_exp (Aq_pos _ _) hmz)

/-! ## The comparison of the sums -/

/-- Comparison of two bounded sums with different parameters. -/
theorem sum_le2 (f g : PTm 2) (x y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N y) := by
  exact sum_le_params f g x y N h

/-- `[m ≥ 1][gcd(m, q) = 1] ⌊F/m⌋`, over `0 = m`, `1 = ⟨q, F⟩`. -/
abbrev hqB : PTm 2 := sg (var 0) * (eqb (gcd (var 0) (fstT (var 1))) one * quo (sndT (var 1)) (var 0))

theorem inst2_hq (m y : PTm n) :
    inst2 hqB m y = sg m * (eqb (gcd m (fstT y)) one * quo (sndT y) m) := by
  simp only [inst2, PTm.subst_mul, PTm.subst_monus, subst_eqb, subst_ex2, subst_ap2, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem hq_at (m q F : PTm n) :
    Γ ⊢[PRAAx] inst2 hqB m (pairT q F) ≐ sg m * (eqb (gcd m q) one * quo F m) := by
  rw [inst2_hq]
  exact congrMul (.eqRefl _) (congrMul
    (congrEqb' (LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep.congrGcd (.eqRefl _) (fst_pair q F))
      (.eqRefl _)) (congrAp2 quoF (snd_pair q F) (.eqRefl _)))

/-- `H_q(N) = ∑_{m < N} [m ≥ 1][gcd(m, q) = 1] ⌊F/m⌋`. -/
abbrev Hq (q F N : PTm n) : PTm n := ap2 (sumF hqB) N (pairT q F)

/-- The term of `H_q` at `m ≤ z` is at most the term of the smooth sum for `A_q(z)^z`. -/
theorem hq_le_term {m z q F : PTm n} (hmz : Γ ⊢[PRAAx] le m z) :
    Γ ⊢[PRAAx] le (sg m * (eqb (gcd m q) one * quo F m)) (term (Aq z q) z F m) := by
  refine .orE (zero_or_succ m) ?_ ?_
  · exact le_zero_of (zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _)
  · let C : List (Fm PTm n) := (m ≐ succ (pred m)) :: Γ
    have hm : C ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
    refine .orE (eqb_cases (gcd m q) one) ?_ ?_
    · exact le_zero_of ((congrMul (.eqRefl _) (zero_mul_l Prf.hyp0 _)).eqTrans (mul_zero _))
    · let D : List (Fm PTm n) := (eqb (gcd m q) one ≐ one) :: C
      have b1 : D ⊢[PRAAx] eqb (gcd m q) one ≐ one := Prf.hyp0
      have hd := dvd_Aq_pow hm.wk (eq_of_eqb b1) hmz.wk.wk
      have eL : D ⊢[PRAAx] sg m * (eqb (gcd m q) one * quo F m) ≐ quo F m :=
        (congrMul ((congrSg hm.wk).eqTrans (sg_succ _)) ((congrMul b1 (.eqRefl _)).eqTrans (one_mul _))).eqTrans
          (one_mul _)
      exact le_congr eL.eqSymm (term_pos hm.wk hd).eqSymm (le_refl _)

/-- **`H_q(z) ≤ S_{A_q(z)}(z)`** with the exponent `L = z`. -/
theorem Hq_le (q F z : PTm n) : Γ ⊢[PRAAx] le (Hq q F (succ z)) (Sm (Aq z q) z F (succ z)) := by
  refine sum_le2 hqB gB (pairT q F) (EulerDomination.par (Aq z q) z F) (succ z) (.allI (.impI ?_))
  have s1 : Syn.shift (pairT q F) = pairT (Syn.shift q) (Syn.shift F) := by simp [Syn.shift]
  have s2 : Syn.shift (EulerDomination.par (Aq z q) z F) = EulerDomination.par (Aq (Syn.shift z) (Syn.shift q)) (Syn.shift z) (Syn.shift F) := by
    simp [Syn.shift]
  have ss : Syn.shift (succ z) = succ (Syn.shift z) := by simp [Syn.shift]
  rw [s1, s2]
  have hlt : (lt (var 0) (Syn.shift (succ z)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (succ (Syn.shift z)) := by
    have h0 : (lt (var 0) (Syn.shift (succ z)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (Syn.shift (succ z)) := Prf.hyp0
    rw [ss] at h0
    exact h0
  have hle : (lt (var 0) (Syn.shift (succ z)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift z) :=
    (succ_monus_succ _ _).eqSymm.eqTrans hlt
  exact le_congr (hq_at _ _ _).eqSymm (g_at _ _ _ _).eqSymm (hq_le_term hle)

/-- **`H_q(z) ≤ ∑_{d ≤ z} [d ∣ A_q(z)] ⌊z!/φ(d)⌋`**. -/
theorem Hq_le_G (q z : PTm n) : Γ ⊢[PRAAx] le (Hq q (fact z) (succ z)) (Gs (Aq z q) z (succ z)) :=
  le_trans (Hq_le q (fact z) z) (smooth_le_totient z q z (le_refl z))

end LeanProofs.IPRA.AnalyticNumberTheory.DenominatorSmooth
