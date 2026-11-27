import IPRADerivations.AnalyticNumberTheory.PowerResidue

/-!
# The involution `x ↦ a x⁻¹` on the units modulo a prime

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"A square test from
an involution", "Pair product":

  "For `a ∈ U`, let `T(x) = rem_p(a x⁻¹)`. This is the unique unit `y` with `x y ≡ a`, so `T(T(x)) = x`. Its
  fixed points are exactly the square roots of `a`."

Here `p` is a prime, `gcd(a, p) = 1`, and `T(x) = res x p a = (x⁻¹ a) mod p` with the inverse of
`AnalyticNumberTheory/PowerResidue`. On the indices `i < p − 1` (for `x = i + 1`) the map is
`σ(i) = T(i + 1) − 1` (`sB`, over `0 = i`, `1 = ⟨p, a⟩`). This module derives:

* `unit_of_lt`: `gcd(x, p) = 1` for `1 ≤ x < p`;
* `T_pos`, `T_T`: `T(x) ≥ 1` and `T(T(x)) = x` for a unit `x < p`;
* `round`: `σ(σ(i)) = i` for `i < p − 1`;
* `unit_perm`: the hypotheses `rangeAll`, `invAll`, `retAll` of `Core/Permutation` for `σ` as its own inverse,
  which are the hypotheses of `Foundations/InvolutionPairing`;
* `pair_mul`: `(i + 1)(σ(i) + 1) ≡ a (mod p)` for `i < p − 1`;
* `fixed_sq`: a fixed point `σ(i) = i` gives `(i + 1)² ≡ a (mod p)`.

Wilson's product, Euler's criterion and the pair-product congruence `eq:pair` are not derived in this module.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.UnitInvolution

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (shift_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (inv res res_spec res_unique res_lt res_cop)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Substitution and congruence for `res` -/

theorem subst_res {m : ℕ} (σ : Fin n → PTm m) (D q b : PTm n) :
    Syn.subst σ (res D q b) = res (Syn.subst σ D) (Syn.subst σ q) (Syn.subst σ b) := by
  ipra_ind_simp [subst_eqb, subst_ex2, subst_ap2, Bezout.subst_cur]

/-- `res` over `0 = D`, `1 = q`, `2 = b`. -/
abbrev res3 : PTm 3 := res (var 0) (var 1) (var 2)

theorem inst3_res3 (D q b : PTm n) : inst3 res3 D q b = res D q b := by
  simp only [inst3, subst_res]
  simp

theorem congrRes {D D' q q' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] D ≐ D') (h₂ : Γ ⊢[PRAAx] q ≐ q')
    (h₃ : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] res D q b ≐ res D' q' b' := by
  have e := congrInst3 res3 h₁ h₂ h₃
  rw [inst3_res3 D q b, inst3_res3 D' q' b'] at e
  exact e

/-! ## Units below a prime -/

/-- `gcd(x, p) = 1` for a prime `p` and `1 ≤ x < p`. -/
theorem unit_of_lt {p x : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hx1 : Γ ⊢[PRAAx] x ≐ succ (pred x))
    (hxp : Γ ⊢[PRAAx] lt x p) : Γ ⊢[PRAAx] gcd x p ≐ one := by
  have nd : Γ ⊢[PRAAx] neg (dvd p x) :=
    .impI (succ_ne_zero' _ (hx1.wk.eqSymm.eqTrans ((rem_small hxp.wk).eqSymm.eqTrans Prf.hyp0)))
  exact gcd_comm_one hx1 (gcd_prime hp nd)

alias mul_one_r := Common.mul_one_right

/-- `T(x) ≥ 1` for a unit `x`, when `gcd(p, a) = 1`. -/
theorem T_pos {p a x : PTm n} (hq : Γ ⊢[PRAAx] le two p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (hu : Γ ⊢[PRAAx] gcd x p ≐ one) : Γ ⊢[PRAAx] res x p a ≐ succ (pred (res x p a)) := by
  have hp1 := p_pos hq
  refine .orE (zero_or_succ (res x p a)) ?_ Prf.hyp0
  have s : ((res x p a ≐ zero) :: Γ) ⊢[PRAAx] rem (x * res x p a) p ≐ rem a p := res_spec hq.wk hu.wk
  have z : ((res x p a ≐ zero) :: Γ) ⊢[PRAAx] rem a p ≐ zero :=
    s.eqSymm.eqTrans ((congrAp2 remF ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans
      (rem_zero _))
  have d : ((res x p a ≐ zero) :: Γ) ⊢[PRAAx] dvd p (a * one) :=
    (congrAp2 remF (mul_one_r a) (.eqRefl _)).eqTrans z
  have e := eq_one_of_dvd_one hp1.wk (gauss hp1.wk hc.wk d)
  exact not_succ_le_self one _ (le_congr (.eqRefl _) e hq.wk)

/-- `T(T(x)) = x` for a unit `x < p`. -/
theorem T_T {p a x : PTm n} (hq : Γ ⊢[PRAAx] le two p) (ha : Γ ⊢[PRAAx] gcd a p ≐ one)
    (hu : Γ ⊢[PRAAx] gcd x p ≐ one) (hxp : Γ ⊢[PRAAx] lt x p) :
    Γ ⊢[PRAAx] res (res x p a) p a ≐ x :=
  (res_unique hq (res_cop hq hu ha) hxp
    ((congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans (res_spec hq hu))).eqSymm

/-! ## Order facts -/

/-- `t − 1 < p − 1` for `t < p`, `p ≥ 2`. -/
theorem pred_lt_pred {t p : PTm n} (hq : Γ ⊢[PRAAx] le two p) (ht : Γ ⊢[PRAAx] lt t p) :
    Γ ⊢[PRAAx] lt (pred t) (pred p) := by
  have hp1 := p_pos hq
  have l : Γ ⊢[PRAAx] le two (succ (pred p)) := le_congr (.eqRefl _) hp1 hq
  refine .orE (zero_or_succ t) ?_ ?_
  · exact lt_congr ((congrPred Prf.hyp0).eqTrans pred_zero).eqSymm (.eqRefl _)
      (Order.le_of_lt_succ l.wk)
  · have h : ((t ≐ succ (pred t)) :: Γ) ⊢[PRAAx] le (succ (succ (pred t))) (succ (pred p)) :=
      le_congr (congrSucc Prf.hyp0) hp1.wk ht.wk
    exact Order.le_of_lt_succ h

/-- `i + 1 < p` for `i < p − 1`. -/
theorem succ_lt_of {i p : PTm n} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hi : Γ ⊢[PRAAx] lt i (pred p)) :
    Γ ⊢[PRAAx] lt (succ i) p :=
  le_congr (.eqRefl _) hp1.eqSymm (Order.succ_le_succ hi)

/-! ## The involution on indices -/

section Index

variable {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
  (ha : Γ ⊢[PRAAx] gcd a p ≐ one)
include hp

/-- `i + 1` is a unit for `i < p − 1`. -/
theorem unit_idx {i : PTm n} (hi : Γ ⊢[PRAAx] lt i (pred p)) : Γ ⊢[PRAAx] gcd (succ i) p ≐ one :=
  unit_of_lt hp (congrSucc (pred_succ _).eqSymm) (succ_lt_of (p_pos (prime_two hp)) hi)

include hc ha

/-- `σ(σ(i)) = i` for `i < p − 1`. -/
theorem round {i : PTm n} (hi : Γ ⊢[PRAAx] lt i (pred p)) :
    Γ ⊢[PRAAx] pred (res (succ (pred (res (succ i) p a))) p a) ≐ i := by
  have hq := prime_two hp
  have hu := unit_idx hp hi
  have tp := T_pos hq hc hu
  have tt := T_T hq ha hu (succ_lt_of (p_pos hq) hi)
  exact (congrPred ((congrRes tp.eqSymm (.eqRefl _) (.eqRefl _)).eqTrans tt)).eqTrans (pred_succ _)

omit ha in
/-- `(i + 1)(σ(i) + 1) ≡ a (mod p)` for `i < p − 1`. -/
theorem pair_mul {i : PTm n} (hi : Γ ⊢[PRAAx] lt i (pred p)) :
    Γ ⊢[PRAAx] rem (succ i * succ (pred (res (succ i) p a))) p ≐ rem a p := by
  have hq := prime_two hp
  have hu := unit_idx hp hi
  exact (congrAp2 remF (congrMul (.eqRefl _) (T_pos hq hc hu).eqSymm) (.eqRefl _)).eqTrans (res_spec hq hu)

omit ha in
/-- A fixed point of `σ` is a square root of `a`: `σ(i) = i` gives `(i + 1)² ≡ a (mod p)`. -/
theorem fixed_sq {i : PTm n} (hi : Γ ⊢[PRAAx] lt i (pred p))
    (e : Γ ⊢[PRAAx] i ≐ pred (res (succ i) p a)) : Γ ⊢[PRAAx] rem (succ i * succ i) p ≐ rem a p :=
  (congrAp2 remF (congrMul (.eqRefl _) (congrSucc e)) (.eqRefl _)).eqTrans (pair_mul hp hc hi)

end Index

/-! ## The body and the permutation hypotheses -/

/-- `σ(i) = T(i + 1) − 1` over `0 = i`, `1 = ⟨p, a⟩`. -/
abbrev sB : PTm 2 := pred (res (succ (var 0)) (fstT (var 1)) (sndT (var 1)))

theorem inst2_sB (i y : PTm n) : inst2 sB i y = pred (res (succ i) (fstT y) (sndT y)) := by
  simp only [inst2, subst_res, LeanProofs.IPRA.PTm.subst_pred]
  simp

theorem s_at (i p a : PTm n) : Γ ⊢[PRAAx] inst2 sB i (pairT p a) ≐ pred (res (succ i) p a) := by
  rw [inst2_sB]
  exact congrPred (congrRes (.eqRefl _) (fst_pair _ _) (snd_pair _ _))

/-- `σ(σ(i)) = i` for the body. -/
theorem s_round {p a i : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (ha : Γ ⊢[PRAAx] gcd a p ≐ one) (hi : Γ ⊢[PRAAx] lt i (pred p)) :
    Γ ⊢[PRAAx] inst2 sB (inst2 sB i (pairT p a)) (pairT p a) ≐ i :=
  (s_at _ p a).eqTrans ((congrPred (congrRes (congrSucc (s_at i p a)) (.eqRefl _) (.eqRefl _))).eqTrans
    (round hp hc ha hi))

/-- The hypotheses of `Core/Permutation` and `Foundations/InvolutionPairing` for `σ` on `[0, p − 1)`. -/
theorem unit_perm {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (ha : Γ ⊢[PRAAx] gcd a p ≐ one) :
    (Γ ⊢[PRAAx] Permutation.rangeAll sB (pred p) (pairT p a)) ∧
      (Γ ⊢[PRAAx] Permutation.invAll sB sB (pred p) (pairT p a)) ∧
      (Γ ⊢[PRAAx] Permutation.retAll sB sB (pred p) (pairT p a)) := by
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have hq' := prime_two hp'
  have hc' := shift_cop hc
  have ha' := shift_cop ha
  have sM : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  refine ⟨?_, ?_, ?_⟩
  · refine .allI ?_
    simp only [shift_pairT]
    rw [sM]
    exact lt_congr (s_at _ _ _).eqSymm (.eqRefl _) (pred_lt_pred hq' (res_lt hq'))
  · refine .allI (.impI (.andI ?_ ?_))
    · simp only [shift_pairT]
      rw [sM]
      exact lt_congr (s_at _ _ _).eqSymm (.eqRefl _) (pred_lt_pred hq'.wk (res_lt hq'.wk))
    · simp only [shift_pairT]
      rw [sM]
      exact s_round hp'.wk hc'.wk ha'.wk Prf.hyp0
  · refine .allI (.impI ?_)
    simp only [shift_pairT]
    rw [sM]
    exact s_round hp'.wk hc'.wk ha'.wk Prf.hyp0

end LeanProofs.IPRA.DiophantineNumberTheory.UnitInvolution
