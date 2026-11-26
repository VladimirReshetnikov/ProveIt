import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Core.Header

/-!
# The order of a residue divides exactly the exponents of the identity

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:order`
(and `chapters/quadratic.tex`, Lemma `qr:orders`, first assertion): for `gcd(a, N) = 1` and `d = ord(a, N)`,
`a^t ≡ 1 (mod N)` exactly when `d ∣ t`.

`Order.order_dvd_totient` is the case `t = φ(N)`; its argument uses of `φ` only that `a^{φ(N)} ≡ 1`.

* **`order_dvd_of_pow`**: `a^t ≡ 1 (mod N)` gives `ord(a, N) ∣ t` (divide `t` by the order; the power at the
  remainder is `1`, and the remainder is below the order, so it is `0` by `Order.order_minimal`);
* **`pow_of_order_dvd`**: `ord(a, N) ∣ t` gives `a^t ≡ 1 (mod N)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.OrderDivides

open_ipra
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (rem_mul_congr pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (mu ord order_cong order_minimal pw_rem_congr pw_one_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Spec

variable {a N : PTm n} (ha : Γ ⊢[PRAAx] gcd a N ≐ one) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include ha hN

/-- `a^t ≡ 1 (mod N)` gives `ord(a, N) ∣ t`. -/
theorem order_dvd_of_pow {t : PTm n} (ht : Γ ⊢[PRAAx] rem (pw a t) N ≐ rem one N) :
    Γ ⊢[PRAAx] dvd (ord a N) t := by
  have d := div_mod (Γ := Γ) t (mu a N)
  have et := Prf.andE₁ d
  -- `a^t ≡ a^s` with `s = t mod ord`.
  have hs : Γ ⊢[PRAAx] rem (pw a (rem t (ord a N))) N ≐ rem one N := by
    have e₁ : Γ ⊢[PRAAx] pw a t ≐ pw (pw a (ord a N)) (quo t (ord a N)) * pw a (rem t (ord a N)) :=
      (congrPw (.eqRefl _) et).eqTrans ((pw_add _ _ _).eqTrans (congrMul (pw_mul _ _ _).eqSymm (.eqRefl _)))
    have e₂ := pw_rem_congr hN (order_cong ha hN) (quo t (ord a N))
    have e₃ := rem_mul_congr (pw a (rem t (ord a N))) hN e₂
    refine .eqTrans ?_ ht
    refine (congrAp2 remF ((one_mul _).eqSymm.eqTrans
      (congrMul (pw_one_base (quo t (ord a N))).eqSymm (.eqRefl _))) (.eqRefl _)).eqTrans ?_
    exact e₃.eqSymm.eqTrans (congrAp2 remF e₁.eqSymm (.eqRefl _))
  -- `s = 0`, by minimality.
  refine .orE (zero_or_succ (rem t (ord a N))) Prf.hyp0 ?_
  refine .botE _ (.impE (order_minimal (a := a) hN.wk (i := pred (rem t (ord a N))) ?_) ?_)
  · have l := Prf.andE₂ d
    exact (succ_monus_succ _ _).eqSymm.eqTrans (le_congr (congrSucc Prf.hyp0) (.eqRefl _) l.wk)
  · exact (congrAp2 remF (congrPw (.eqRefl _) Prf.hyp0.eqSymm) (.eqRefl _)).eqTrans hs.wk

/-- `ord(a, N) ∣ t` gives `a^t ≡ 1 (mod N)`. -/
theorem pow_of_order_dvd {t : PTm n} (hd : Γ ⊢[PRAAx] dvd (ord a N) t) :
    Γ ⊢[PRAAx] rem (pw a t) N ≐ rem one N := by
  have e := eq_of_dvd hd
  have e₁ : Γ ⊢[PRAAx] pw a t ≐ pw (pw a (ord a N)) (quo t (ord a N)) :=
    (congrPw (.eqRefl _) e).eqTrans (pw_mul _ _ _).eqSymm
  have e₂ := pw_rem_congr hN (order_cong ha hN) (quo t (ord a N))
  exact (congrAp2 remF e₁ (.eqRefl _)).eqTrans (e₂.eqTrans (congrAp2 remF (pw_one_base _) (.eqRefl _)))

end Spec

end LeanProofs.IPRA.AnalyticNumberTheory.OrderDivides
