import IPRADerivations.AnalyticNumberTheory.DirichletLeibniz

/-!
# The weighted von Mangoldt function at prime powers

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:log-zeta-coeff`.
For primes `p, q` and `a ≥ 1`:

* `val_pw_prime`: `v_q(p^a) = a [p = q]`;
* `ppI_pw`: `p^a` is a positive power of `q` exactly when `q = p`;
* `lam_pw`, `lam_pw'`: `Λ_w(p^a) = w(p)`;
* `lw_pw`: `L_w(p^a) = a w(p)`;
* `log_zeta_coeff`: `L_w(p^a) = a Λ_w(p^a)`, the cross-multiplied form of `(D_w H)(p^a) = Λ_w(p^a)`
  for the coefficient `H(p^a) = 1/a` of the formal Dirichlet logarithm of zeta. (Off prime powers
  `H` and `Λ_w` both vanish by definition.)

Theorem `thm:twist`, in coefficient form: for a completely multiplicative `f`,
`((f Λ_w) * f)(m) = L_w(m) f(m)` for `m ≥ 1` (`twist`), i.e. `D_w F = (f Λ_w) * F` for the Euler
product `F = f`, so the weighted logarithmic derivative of `F` has coefficients `f(n) Λ_w(n)`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimePowerMangoldt

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `v_q(p^j) = j [p = q]` for primes `p, q`. -/
theorem val_pw_prime {q p : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hp : Γ ⊢[PRAAx] prime p) (j : PTm n) :
    Γ ⊢[PRAAx] val q (pw p j) ≐ j * eqb p q := by
  have hq2 := prime_two hq; have hp2 := prime_two hp
  have qpos := ValuationMul.p_pos hq2; have ppos := ValuationMul.p_pos hp2
  refine .orE (eq_or_ne p q) ?_ ?_
  · let C : List (Fm PTm n) := (p ≐ q) :: Γ
    have e : C ⊢[PRAAx] p ≐ q := Prf.hyp0
    refine (congrVal e.eqSymm (.eqRefl _)).eqTrans ((val_pw j hp2.wk).eqTrans ?_)
    refine .eqTrans ?_ (congrMul (.eqRefl _) (eqb_of_eq e)).eqSymm
    ipra_ring
  · let C : List (Fm PTm n) := neg (p ≐ q) :: Γ
    have z : C ⊢[PRAAx] val q (pw p j) ≐ zero := by
      refine ValuationMul.val_unique hq2.wk (Valuation.pw_pos' ppos.wk j)
        ((one_mul _).eqSymm.eqTrans (congrMul (pw_zero q).eqSymm (.eqRefl (pw p j)))) (.impI ?_)
      let D : List (Fm PTm n) := dvd q (pw p j) :: C
      have d1 : D ⊢[PRAAx] dvd q p := FactorVector.prime_dvd_pw hq.wk.wk Prf.hyp0
      have eN := eq_of_dvd' qpos.wk.wk d1
      have cpos := pos_of_eq_mul ppos.wk.wk eN
      have vm := ValuationMul.val_mul hq.wk.wk qpos.wk.wk cpos
      have vqq : D ⊢[PRAAx] val q q ≐ one := (val_pp hq.wk.wk hq.wk.wk).eqTrans (eqb_of_eq (.eqRefl _))
      have nq : D ⊢[PRAAx] neg (q ≐ p) := Order.ne_symm Prf.hyp1
      have vqp : D ⊢[PRAAx] val q p ≐ zero := (val_pp hq.wk.wk hp.wk.wk).eqTrans (eqb_of_ne nq)
      have s : D ⊢[PRAAx] succ (val q (quo p q)) ≐ zero :=
        (show D ⊢[PRAAx] succ (val q (quo p q)) ≐ one + val q (quo p q) by ipra_ring).eqTrans
          ((congrAdd vqq.eqSymm (.eqRefl _)).eqTrans (vm.eqSymm.eqTrans ((ValuationMul.val_congr q eN).eqSymm.eqTrans vqp)))
      exact succ_ne_zero' _ s
    exact z.eqTrans ((congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (mul_zero _)).eqSymm

/-- For primes `p, q` and `a ≥ 1`: `p^a` is a positive power of `q` exactly when `p = q`. -/
theorem ppI_pw {q p a : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hp : Γ ⊢[PRAAx] prime p)
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) : Γ ⊢[PRAAx] ppI q (pw p a) ≐ eqb p q := by
  have v := val_pw_prime hq hp a
  refine .orE (eq_or_ne p q) ?_ ?_
  · let C : List (Fm PTm n) := (p ≐ q) :: Γ
    have e : C ⊢[PRAAx] p ≐ q := Prf.hyp0
    have v' : C ⊢[PRAAx] val q (pw p a) ≐ a :=
      v.wk.eqTrans ((congrMul (.eqRefl _) (eqb_of_eq e)).eqTrans (by ipra_ring))
    have s1 : C ⊢[PRAAx] sg (val q (pw p a)) ≐ one := (congrSg (v'.eqTrans ha.wk)).eqTrans (sg_succ _)
    have e1 : C ⊢[PRAAx] eqb (pw q (val q (pw p a))) (pw p a) ≐ one :=
      eqb_of_eq (Combinatorics.BinomialTheorem.congrPw e.eqSymm v')
    exact (congrMul s1 e1).eqTrans ((by ipra_ring : C ⊢[PRAAx] one * one ≐ one).eqTrans
      (eqb_of_eq e).eqSymm)
  · let C : List (Fm PTm n) := neg (p ≐ q) :: Γ
    have v' : C ⊢[PRAAx] val q (pw p a) ≐ zero :=
      v.wk.eqTrans ((congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (mul_zero _))
    exact (zero_mul_l ((congrSg v').eqTrans sg_zero) _).eqTrans (eqb_of_ne Prf.hyp0).eqSymm

/-- `p < p^a + 1` for `a ≥ 1`. -/
theorem p_lt_pw {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] lt p (succ (pw p a)) := by
  have hp2 := prime_two hp; have ppos := ValuationMul.p_pos hp2
  have l1 : Γ ⊢[PRAAx] le one a := le_of_eq_add (d := pred a) (ha.eqTrans (by ipra_ring))
  have d : Γ ⊢[PRAAx] dvd p (pw p a) := dvd_congr_left (pw_one p) (WeightedMangoldt.pw_dvd_pw hp2 l1)
  exact (succ_monus_succ _ _).eqTrans (dvd_le' ppos d (Valuation.pw_pos' ppos a))

section Weighted

variable (w : PTm 2)

/-- `[q prime] w(q, y)`, over `0 = q`, `1 = y`. -/
abbrev iwB : PTm 2 := isP (var 0) * w

theorem inst2_iwB (q y : PTm n) : inst2 (iwB w) q y = isP q * inst2 w q y := by simp [inst2]

/-- `Λ_w(p^a) = [p prime] w(p)` for a prime `p` and `a ≥ 1`. -/
theorem lam_pw {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (y : PTm n) :
    Γ ⊢[PRAAx] Lam w (pw p a) y ≐ isP p * inst2 w p y := by
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have ha' := shift_pos ha
  have hpw : Syn.shift (pw p a) = pw (Syn.shift p) (Syn.shift a) := by simp [Syn.shift]
  refine (sum_congr_bounded (lamB w) (dB (iwB w)) _ (pairT p y) _ (.allI (.impI ?_))).eqTrans
    ((sum_delta (iwB w) (p_lt_pw hp ha)).eqTrans (by rw [inst2_iwB]; exact .eqRefl _))
  rw [inst2_lam, inst2_dB, shift_pairT, shift_pairT, inst2_iwB, hpw]
  refine (congrMul (congrMul (.eqRefl _) (congrPpI (.eqRefl _) (fst_pair _ _))) (congrInst2 w (.eqRefl _) (snd_pair _ _))).eqTrans
    (.eqTrans ?_ (congrMul (congrEqb' (fst_pair _ _) (.eqRefl _))
      (congrMul (.eqRefl _) (congrInst2 w (.eqRefl _) (snd_pair _ _)))).eqSymm)
  refine .orE (Valuation.isP_01 (var 0)) ?_ ?_
  · exact (zero_mul_l (zero_mul_l Prf.hyp0 _) _).eqTrans
      ((congrMul (.eqRefl _) (zero_mul_l Prf.hyp0 _)).eqTrans (mul_zero _)).eqSymm
  · refine (congrMul (congrMul (.eqRefl _) (ppI_pw (Valuation.prime_of_isP Prf.hyp0) hp'.wk.wk ha'.wk.wk)) (.eqRefl _)).eqTrans ?_
    ipra_ring

/-- `Λ_w(p^a) = w(p)` for a prime `p` and `a ≥ 1`. -/
theorem lam_pw' {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (y : PTm n) :
    Γ ⊢[PRAAx] Lam w (pw p a) y ≐ inst2 w p y :=
  (lam_pw w hp ha y).eqTrans ((congrMul (Valuation.isP_of_prime hp) (.eqRefl _)).eqTrans (one_mul _))

/-- `L_w(p^a) = a [p prime] w(p)` for a prime `p` and `a ≥ 1`. -/
theorem lw_pw {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (y : PTm n) :
    Γ ⊢[PRAAx] Lw w (pw p a) y ≐ a * (isP p * inst2 w p y) := by
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have hpw : Syn.shift (pw p a) = pw (Syn.shift p) (Syn.shift a) := by simp [Syn.shift]
  refine (sum_scale (ellB w) (dB (iwB w)) (succ (pw p a)) a (pairT p y) (pairT (pw p a) y) (.allI (.impI ?_))).eqTrans
    (congrMul (.eqRefl _) ((sum_delta (iwB w) (p_lt_pw hp ha)).eqTrans (by rw [inst2_iwB]; exact .eqRefl _)))
  rw [inst2_ell, inst2_dB, shift_pairT, shift_pairT, inst2_iwB, hpw]
  refine (congrMul (congrMul (.eqRefl _) (congrVal (.eqRefl _) (fst_pair _ _))) (congrInst2 w (.eqRefl _) (snd_pair _ _))).eqTrans
    (.eqTrans ?_ (congrMul (.eqRefl _) (congrMul (congrEqb' (fst_pair _ _) (.eqRefl _))
      (congrMul (.eqRefl _) (congrInst2 w (.eqRefl _) (snd_pair _ _))))).eqSymm)
  refine .orE (Valuation.isP_01 (var 0)) ?_ ?_
  · exact (zero_mul_l (zero_mul_l Prf.hyp0 _) _).eqTrans
      ((congrMul (.eqRefl _) ((congrMul (.eqRefl _) (zero_mul_l Prf.hyp0 _)).eqTrans (mul_zero _))).eqTrans (mul_zero _)).eqSymm
  · refine (congrMul (congrMul (.eqRefl _) (val_pw_prime (Valuation.prime_of_isP Prf.hyp0) hp'.wk.wk _)) (.eqRefl _)).eqTrans ?_
    ipra_ring

/-- `thm:log-zeta-coeff`: `L_w(p^a) = a Λ_w(p^a)` for a prime `p` and `a ≥ 1`, i.e.
`(D_w H)(p^a) = Λ_w(p^a)` for `H(p^a) = 1/a`. -/
theorem log_zeta_coeff {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (y : PTm n) :
    Γ ⊢[PRAAx] Lw w (pw p a) y ≐ a * Lam w (pw p a) y :=
  (lw_pw w hp ha y).eqTrans (congrMul (.eqRefl _) (lam_pw w hp ha y).eqSymm)

end Weighted

section Twist

variable (w f : PTm 2)

/-- `f(d, y) Λ_w(d)`, over `0 = d`, `1 = y`. -/
abbrev fLB : PTm 2 := f * ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) zero)

theorem inst2_fLB (d y : PTm n) : inst2 (fLB w f) d y = inst2 f d y * Lam w d zero := by simp [inst2]

/-- `thm:twist`: for `f` completely multiplicative, `∑_{d ∣ m} f(d) Λ_w(d) f(m/d) = L_w(m) f(m)`
for `m ≥ 1`. Complete multiplicativity is the hypothesis `hf`, available in every extension of the
shifted context. -/
theorem twist {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hf : ∀ (D : List (Fm PTm (n + 1))) (a b : PTm (n + 1)), Γ.map Fm.shift ⊆ D →
      (D ⊢[PRAAx] inst2 f (a * b) (Syn.shift y) ≐ inst2 f a (Syn.shift y) * inst2 f b (Syn.shift y))) :
    Γ ⊢[PRAAx] DirichletLeibniz.conv (fLB w f) f m y ≐ Lw w m zero * inst2 f m y := by
  have hs : Syn.shift (inst2 f m y) = inst2 f (Syn.shift m) (Syn.shift y) := MobiusInversion.shift_inst2 f m y
  have hz : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  have sc : Γ ⊢[PRAAx] DirichletLeibniz.conv (fLB w f) f m y ≐
      inst2 f m y * ap2 (sumF (WeightedMangoldt.DB w)) (succ m) (pairT m zero) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [hs, shift_pairT, shift_pairT, hz]
    refine (DirichletLeibniz.cv_at _ _ _ _ _).eqTrans
      (.eqTrans ?_ (congrMul (.eqRefl _) (FactorialLambda.DB_at w _ _ _)).eqSymm)
    rw [inst2_fLB]
    let Δ0 : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift
    refine .orE (zero_or_succ (var 0)) ?_ ?_
    · have s0 : ((var 0 ≐ zero) :: Δ0) ⊢[PRAAx] sg (var 0) ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (zero_mul_l (zero_mul_l s0 _) _).eqTrans
        ((congrMul (.eqRefl _) (zero_mul_l (zero_mul_l s0 _) _)).eqTrans (mul_zero _)).eqSymm
    · refine .orE (eq_or_ne (rem (Syn.shift m) (var 0)) zero) ?_ ?_
      · let C : List (Fm PTm (n + 1)) :=
          (rem (Syn.shift m) (var 0) ≐ zero) :: (var 0 ≐ succ (pred (var 0))) :: Δ0
        have hd : C ⊢[PRAAx] var 0 ≐ succ (pred (var 0)) := Prf.hyp1
        have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd (var 0) (Syn.shift m))
        have mf := hf C (var 0) (quo (Syn.shift m) (var 0))
          (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
        have fm := (congrInst2 f eN (.eqRefl _)).eqTrans mf
        refine .eqTrans ?_ (congrMul fm.eqSymm (.eqRefl _))
        ipra_ring
      · let C : List (Fm PTm (n + 1)) :=
          neg (rem (Syn.shift m) (var 0) ≐ zero) :: (var 0 ≐ succ (pred (var 0))) :: Δ0
        have zz : C ⊢[PRAAx] sg (var 0) * eqb (rem (Syn.shift m) (var 0)) zero ≐ zero :=
          (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
        exact (zero_mul_l zz _).eqTrans ((congrMul (.eqRefl _) (zero_mul_l zz _)).eqTrans (mul_zero _)).eqSymm
  exact (sc.eqTrans (congrMul (.eqRefl _) (lambda_divsum w hm))).eqTrans (mul_comm _ _)

end Twist

end LeanProofs.IPRA.AnalyticNumberTheory.PrimePowerMangoldt
