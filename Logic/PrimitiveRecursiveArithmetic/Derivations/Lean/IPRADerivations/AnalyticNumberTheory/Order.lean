import IPRADerivations.AnalyticNumberTheory.Euler

/-!
# The multiplicative order

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Corollary
`cor:order-divides` and Theorem `thm:order-am1`.

For `gcd(a, n) = 1`, the order `ord(a, n) = μ + 1`, where `μ` is the least `i < φ(n)` with
`a^{i+1} ≡ 1 (mod n)` (bounded search; Euler's theorem supplies `i = φ(n) − 1`). Then:

* `order_cong`, `order_minimal`: `a^{ord} ≡ 1`, and `a^{i+1} ≢ 1` for `i + 1 < ord`;
* `order_dvd_totient` (`cor:order-divides`): `ord ∣ φ(n)`, by dividing `φ(n) = ord·q + s`;
* `zsigmondy` (`thm:order-am1`): for `a > 1`, `m ≥ 1`, `m ∣ φ(aᵐ − 1)`, since the order of `a`
  modulo `aᵐ − 1` is exactly `m`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Order

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot pred_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb rem_small rem_lt N_pos rem_one euler_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `[a^{i+1} ≢ 1 (mod N)]`, over `0 = i`, `1 = ⟨a, N⟩`. -/
abbrev ordBody : PTm 2 :=
  monus one (eqb (rem (pw (fstT (var 1)) (succ (var 0))) (sndT (var 1))) (rem one (sndT (var 1))))

/-- `μ`, and `ord(a, N) = μ + 1`. -/
abbrev mu (a N : PTm n) : PTm n := Search.mu ordBody (phi N) (pairT a N)
abbrev ord (a N : PTm n) : PTm n := succ (mu a N)

/-- The body evaluated. -/
abbrev ordVal (i a N : PTm n) : PTm n := monus one (eqb (rem (pw a (succ i)) N) (rem one N))

theorem ord_at (i a N : PTm n) : Γ ⊢[PRAAx] inst2 ordBody i (pairT a N) ≐ ordVal i a N := by
  have e : inst2 ordBody i (pairT a N) = monus one (eqb (rem (pw (fstT (pairT a N)) (succ i)) (sndT (pairT a N)))
      (rem one (sndT (pairT a N)))) := by simp [inst2]
  rw [e]
  exact congrMonus (.eqRefl _) (congrEqb (congrAp2 remF (congrPw (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
    (congrAp2 remF (.eqRefl _) (snd_pair _ _)))

theorem ordVal_zero {i a N : PTm n} (h : Γ ⊢[PRAAx] rem (pw a (succ i)) N ≐ rem one N) :
    Γ ⊢[PRAAx] ordVal i a N ≐ zero :=
  (congrMonus (.eqRefl _) (eqb_of_eq h)).eqTrans (monus_self _)

theorem cong_of_ordVal {i a N : PTm n} (h : Γ ⊢[PRAAx] ordVal i a N ≐ zero) :
    Γ ⊢[PRAAx] rem (pw a (succ i)) N ≐ rem one N := by
  refine .orE (eq_or_ne (rem (pw a (succ i)) N) (rem one N)) Prf.hyp0 ?_
  refine succ_ne_zero' _ (a := zero) (.eqTrans ?_ h.wk)
  exact ((monus_zero _).eqSymm.eqTrans (congrMonus (.eqRefl _) (eqb_of_ne Prf.hyp0).eqSymm))

/-- Powers respect congruence. -/
theorem pw_rem_congr {x y N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (h : Γ ⊢[PRAAx] rem x N ≐ rem y N)
    (q : PTm n) : Γ ⊢[PRAAx] rem (pw x q) N ≐ rem (pw y q) N := by
  have hall : Γ ⊢[PRAAx] Fm.all (rem (pw (Syn.shift x) (var 0)) (Syn.shift N) ≐ rem (pw (Syn.shift y) (var 0)) (Syn.shift N)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact congrAp2 remF ((pw_zero _).eqTrans (pw_zero _).eqSymm) (.eqRefl _)
    · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hN' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift N ≐ succ (pred (Syn.shift N)) := by
        have e := hN.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_pred, ConciseIPRA.PTm.subst_succ] at e
        exact e
      have h' : Γ.map Fm.shift ⊢[PRAAx] rem (Syn.shift x) (Syn.shift N) ≐ rem (Syn.shift y) (Syn.shift N) := by
        have e := h.shift
        simp only [Fm.shift, Fm.subst_eq, subst_ap2] at e
        exact e
      refine (congrAp2 remF (pw_succ _ _) (.eqRefl _)).eqTrans (.eqTrans ?_ (congrAp2 remF (pw_succ _ _) (.eqRefl _)).eqSymm)
      refine (rem_mul_congr _ hN'.wk Prf.hyp0).eqTrans ?_
      refine (congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans ((rem_mul_congr _ hN'.wk h'.wk).eqTrans ?_)
      exact congrAp2 remF (mul_comm _ _) (.eqRefl _)
  have h2 := Prf.allE q hall
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact h2

private theorem pw_one₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] pw one (var 0) ≐ one := by
  ipra_ind [subst_ap2]
  · exact pw_zero _
  · exact (pw_succ _ _).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _))

theorem pw_one_base (q : PTm n) : Γ ⊢[PRAAx] pw one q ≐ one := by
  have h := inst (Γ := Γ) pw_one₀ (![q] : Fin 1 → PTm n)
  simpa using h

/-- `gcd(a, b) ≥ 1` for `b ≥ 1`. -/
theorem gcd_pos_right {a b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] gcd a b ≐ succ (pred (gcd a b)) := by
  refine .orE (zero_or_succ (gcd a b)) ?_ Prf.hyp0
  have c := Prf.andE₂ (common_at (Γ := (gcd a b ≐ zero) :: Γ) a b b (succ b))
  have d₁ := dvd_congr Prf.hyp0.eqSymm (dvd_zero (Γ := (gcd a b ≐ zero) :: Γ) b)
  have d₂ := dvd_congr (terminates_at a b).eqSymm (dvd_zero (Γ := (gcd a b ≐ zero) :: Γ) b)
  have hbb := Prf.andE₂ (Prf.impE c (.andI d₁ d₂))
  exact not_succ_le_self b _ (dvd_le hbb hb.wk)

theorem gcd_eq_one_of_dvd {a b : PTm n} (hg : Γ ⊢[PRAAx] gcd a b ≐ succ (pred (gcd a b)))
    (h : Γ ⊢[PRAAx] a ≐ one ⋎ (b ≐ one)) : Γ ⊢[PRAAx] gcd a b ≐ one := by
  have hd := gcd_dvd_at hg
  refine eq_one_of_dvd_one hg (.orE h ?_ ?_)
  · exact dvd_congr Prf.hyp0 (Prf.andE₁ hd).wk
  · exact dvd_congr Prf.hyp0 (Prf.andE₂ hd).wk

/-! ## The order -/

/-- A unit below `N` makes `φ(N) ≥ 1`. -/
theorem phi_pos_of {N j : PTm n} (hj : Γ ⊢[PRAAx] lt j N) (hg : Γ ⊢[PRAAx] gcd j N ≐ one) :
    Γ ⊢[PRAAx] phi N ≐ succ (pred (phi N)) := by
  have t := term_le_sum totBody (x := N) hj
  rw [inst2_tot] at t
  have w := eq_add_of_le t
  exact AnalyticNumberTheory.Primes.eq_succ_pred (y := monus (phi N) (eqb (gcd j N) one))
    ((w.eqTrans (congrAdd (eqb_of_eq hg) (.eqRefl _))).eqTrans (by ipra_ring))

section Spec

variable {a N : PTm n} (ha : Γ ⊢[PRAAx] gcd a N ≐ one) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include hN

/-- `φ(N) ≥ 1`. -/
theorem phi_pos : Γ ⊢[PRAAx] phi N ≐ succ (pred (phi N)) := by
  refine .orE (zero_or_succ (pred N)) ?_ ?_
  · have e : ((pred N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ one := hN.wk.eqTrans (congrSucc Prf.hyp0)
    refine phi_pos_of (j := zero) (lt_congr (.eqRefl _) e.eqSymm (zero_lt_succ _)) ?_
    exact gcd_eq_one_of_dvd (gcd_pos_right hN.wk) (.orI₂ e)
  · have h2 : ((pred N ≐ succ (pred (pred N))) :: Γ) ⊢[PRAAx] lt one N :=
      le_of_eq_add (d := pred (pred N)) (hN.wk.eqTrans ((congrSucc Prf.hyp0).eqTrans
        (by ipra_ring)))
    exact phi_pos_of h2 (gcd_eq_one_of_dvd (gcd_pos (congrSucc (pred_succ _).eqSymm)) (.orI₁ (.eqRefl _)))

include ha

/-- The search finds `μ < φ(N)`. -/
theorem mu_found : Γ ⊢[PRAAx] lt (mu a N) (phi N) ⋏ ((inst2 ordBody (mu a N) (pairT a N) ≐ zero) ⋏
    le (mu a N) (pred (phi N))) := by
  have hp := phi_pos hN
  have e := euler_at ha hN
  refine Search.search_found (f := ordBody) ((ord_at _ _ _).eqTrans (ordVal_zero ?_)) (pred_lt hp)
  exact (congrAp2 remF (congrPw (.eqRefl _) hp.eqSymm) (.eqRefl _)).eqTrans e

/-- `a^{ord} ≡ 1 (mod N)`. -/
theorem order_cong : Γ ⊢[PRAAx] rem (pw a (ord a N)) N ≐ rem one N :=
  cong_of_ordVal ((ord_at _ _ _).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ (mu_found ha hN))))

omit ha in
/-- `a^{i+1} ≢ 1 (mod N)` for `i < μ`. -/
theorem order_minimal {i : PTm n} (hi : Γ ⊢[PRAAx] lt i (mu a N)) :
    Γ ⊢[PRAAx] neg (rem (pw a (succ i)) N ≐ rem one N) :=
  .impI (.impE (Search.search_minimal (f := ordBody) hi).wk ((ord_at _ _ _).eqTrans (ordVal_zero Prf.hyp0)))

/-- `cor:order-divides`: `ord(a, N) ∣ φ(N)`. -/
theorem order_dvd_totient : Γ ⊢[PRAAx] dvd (ord a N) (phi N) := by
  have d := div_mod (Γ := Γ) (phi N) (mu a N)
  have eφ := Prf.andE₁ d
  -- `a^φ ≡ a^s` with `s = φ mod ord`.
  have hs : Γ ⊢[PRAAx] rem (pw a (rem (phi N) (ord a N))) N ≐ rem one N := by
    have e₁ : Γ ⊢[PRAAx] pw a (phi N) ≐ pw (pw a (ord a N)) (quo (phi N) (ord a N)) * pw a (rem (phi N) (ord a N)) :=
      (congrPw (.eqRefl _) eφ).eqTrans ((pw_add _ _ _).eqTrans (congrMul (pw_mul _ _ _).eqSymm (.eqRefl _)))
    have e₂ := pw_rem_congr hN (order_cong ha hN) (quo (phi N) (ord a N))
    have e₃ := rem_mul_congr (pw a (rem (phi N) (ord a N))) hN e₂
    refine .eqTrans ?_ (euler_at ha hN)
    refine (congrAp2 remF ((one_mul _).eqSymm.eqTrans (congrMul (pw_one_base (quo (phi N) (ord a N))).eqSymm (.eqRefl _))) (.eqRefl _)).eqTrans ?_
    exact e₃.eqSymm.eqTrans (congrAp2 remF e₁.eqSymm (.eqRefl _))
  -- `s = 0`, by minimality.
  refine .orE (zero_or_succ (rem (phi N) (ord a N))) Prf.hyp0 ?_
  refine .botE _ (.impE (order_minimal (a := a) hN.wk (i := pred (rem (phi N) (ord a N))) ?_) ?_)
  · have l := Prf.andE₂ d
    exact (succ_monus_succ _ _).eqSymm.eqTrans (le_congr (congrSucc Prf.hyp0) (.eqRefl _) l.wk)
  · exact (congrAp2 remF (congrPw (.eqRefl _) Prf.hyp0.eqSymm) (.eqRefl _)).eqTrans hs.wk

end Spec

/-- `cor:order-divides`; variables `0 = a`, `1 = n`. -/
abbrev orderFormula : Fm PTm 2 :=
  gcd (var 0) (var 1) ≐ one ⟶ (var 1 ≐ succ (pred (var 1))) ⟶
    (rem (pw (var 0) (ord (var 0) (var 1))) (var 1) ≐ rem one (var 1)) ⋏ dvd (ord (var 0) (var 1)) (phi (var 1))

theorem order_divides_totient : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 orderFormula :=
  closeUniv 2 (.impI (.impI (.andI (order_cong Prf.hyp1 Prf.hyp0) (order_dvd_totient Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.AnalyticNumberTheory.Order

export_ipra AnalyticNumberTheory.Order (gcd_pos_right order_cong pw_one_base pw_rem_congr)
