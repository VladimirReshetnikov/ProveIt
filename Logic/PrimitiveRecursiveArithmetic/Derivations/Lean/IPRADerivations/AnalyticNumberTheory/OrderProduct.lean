import IPRADerivations.AnalyticNumberTheory.OrderOfPower
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.DiophantineNumberTheory.ModularCertificate

/-!
# The order of a product with coprime orders

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`, Lemma
`qr:orders`, the last assertion: "If `u, v` have coprime orders `s, t`, respectively, then `uv` has order
`st`. … `(uv)^{st} = 1`. If `(uv)^k = 1`, raising to `t` gives `u^{kt} = 1`, hence `s ∣ kt`. Coprimality
gives `s ∣ k` by Bézout. Similarly `t ∣ k`, and therefore `st ∣ k`."

It holds for every modulus `M ≥ 1` and units `u, v ≥ 1` (`gcd(u, M) = gcd(v, M) = 1`):

* `rem_cancel`: `xy ≡ 1` and `y ≡ 1` give `x ≡ 1`; `rem_mul_one`: `x ≡ 1`, `y ≡ 1` give `xy ≡ 1`;
* `ord_mul_dvd`: `ord(uv) ∣ st`;
* `pow_u_one`: `(uv)^k ≡ 1` gives `u^{k t} ≡ 1`;
* `mul_dvd_of_coprime`: `s ∣ e`, `t ∣ e`, `gcd(s, t) = 1` give `st ∣ e`;
* **`ord_mul_coprime`**: `ord(uv, M) = ord(u, M) · ord(v, M)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.OrderProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (ord order_cong pw_rem_congr pw_one_base)
open LeanProofs.IPRA.AnalyticNumberTheory.OrderDivides (order_dvd_of_pow pow_of_order_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_mul_congr2)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_le' gcd_comm_one coprime_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.ConicGcd (dvd_of_coprime_pair)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `x · 1 = x`. -/
theorem mul_one' (x : PTm n) : Γ ⊢[PRAAx] x * one ≐ x := (mul_comm _ _).eqTrans (one_mul _)

/-- `xy ≡ 1` and `y ≡ 1` give `x ≡ 1`. -/
theorem rem_cancel {x y M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hxy : Γ ⊢[PRAAx] rem (x * y) M ≐ rem one M) (hy : Γ ⊢[PRAAx] rem y M ≐ rem one M) :
    Γ ⊢[PRAAx] rem x M ≐ rem one M :=
  (congrAp2 remF (mul_one' x).eqSymm (.eqRefl _)).eqTrans
    ((rem_mul_congr2 hM (.eqRefl (rem x M)) hy).eqSymm.eqTrans hxy)

/-- `x ≡ 1` and `y ≡ 1` give `xy ≡ 1`. -/
theorem rem_mul_one {x y M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hx : Γ ⊢[PRAAx] rem x M ≐ rem one M) (hy : Γ ⊢[PRAAx] rem y M ≐ rem one M) :
    Γ ⊢[PRAAx] rem (x * y) M ≐ rem one M :=
  (rem_mul_congr2 hM hx hy).eqTrans (congrAp2 remF (mul_one' one) (.eqRefl _))

/-- `s ∣ e`, `t ∣ e` and `gcd(s, t) = 1` give `st ∣ e`. -/
theorem mul_dvd_of_coprime {s t e : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (hse : Γ ⊢[PRAAx] dvd s e) (hte : Γ ⊢[PRAAx] dvd t e) (hst : Γ ⊢[PRAAx] gcd s t ≐ one) :
    Γ ⊢[PRAAx] dvd (s * t) e := by
  have E := eq_of_dvd' hs hse
  have h1 : Γ ⊢[PRAAx] dvd t (quo e s * s) :=
    (congrAp2 remF ((mul_comm _ _).eqTrans E.eqSymm) (.eqRefl _)).eqTrans hte
  have h2 : Γ ⊢[PRAAx] dvd t (quo e s * t) := dvd_of_eq' ht (mul_comm _ _)
  have te := dvd_of_coprime_pair ht h1 h2 hst
  have E2 := natEq (eq_of_dvd' ht te)
  have E1 := natEq E
  refine dvd_of_eq' (pos_mul hs ht) (w := quo (quo e s) t) ?_
  apply deriveNat; ipra_simps
  linear_combination E1 + 𝔞 s * E2

section Units

variable {u v M : PTm n} (hu0 : Γ ⊢[PRAAx] u ≐ succ (pred u)) (hv0 : Γ ⊢[PRAAx] v ≐ succ (pred v))
  (hu : Γ ⊢[PRAAx] gcd u M ≐ one) (hv : Γ ⊢[PRAAx] gcd v M ≐ one) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
include hu0 hv0 hu hv hM

theorem cop_uv : Γ ⊢[PRAAx] gcd (u * v) M ≐ one :=
  gcd_comm_one (pos_mul hu0 hv0) (coprime_mul hM (gcd_comm_one hM hu) (gcd_comm_one hM hv))

/-- `(uv)^k ≡ 1` gives `u^{k t} ≡ 1` for `t = ord(v)`. -/
theorem pow_u_one (k : PTm n) (hk : Γ ⊢[PRAAx] rem (pw (u * v) k) M ≐ rem one M) :
    Γ ⊢[PRAAx] rem (pw u (k * ord v M)) M ≐ rem one M := by
  have ht : Γ ⊢[PRAAx] ord v M ≐ succ (pred (ord v M)) := congrSucc (pred_succ _).eqSymm
  have r := (pw_rem_congr hM hk (ord v M)).eqTrans (congrAp2 remF (pw_one_base _) (.eqRefl _))
  have r2 : Γ ⊢[PRAAx] rem (pw u (k * ord v M) * pw v (k * ord v M)) M ≐ rem one M :=
    (congrAp2 remF ((pw_mul_base u v _).eqSymm.eqTrans (pw_mul _ k _).eqSymm) (.eqRefl _)).eqTrans r
  have hvv : Γ ⊢[PRAAx] rem (pw v (k * ord v M)) M ≐ rem one M :=
    pow_of_order_dvd hv hM (dvd_of_eq' ht (mul_comm _ _))
  exact rem_cancel hM r2 hvv

/-- `ord(uv) ∣ ord(u) ord(v)`. -/
theorem ord_mul_dvd : Γ ⊢[PRAAx] dvd (ord (u * v) M) (ord u M * ord v M) := by
  have hs : Γ ⊢[PRAAx] ord u M ≐ succ (pred (ord u M)) := congrSucc (pred_succ _).eqSymm
  have ht : Γ ⊢[PRAAx] ord v M ≐ succ (pred (ord v M)) := congrSucc (pred_succ _).eqSymm
  have cu := pow_of_order_dvd hu hM (dvd_of_eq' hs (.eqRefl (ord u M * ord v M)))
  have cv := pow_of_order_dvd hv hM (dvd_of_eq' ht (mul_comm (ord u M) (ord v M)))
  have c : Γ ⊢[PRAAx] rem (pw (u * v) (ord u M * ord v M)) M ≐ rem one M :=
    (congrAp2 remF (pw_mul_base u v _) (.eqRefl _)).eqTrans (rem_mul_one hM cu cv)
  exact order_dvd_of_pow (cop_uv hu0 hv0 hu hv hM) hM c

end Units

/-- **`qr:orders`, the product**: if `gcd(ord(u), ord(v)) = 1` then `ord(uv, M) = ord(u, M) ord(v, M)`. -/
theorem ord_mul_coprime {u v M : PTm n} (hu0 : Γ ⊢[PRAAx] u ≐ succ (pred u)) (hv0 : Γ ⊢[PRAAx] v ≐ succ (pred v))
    (hu : Γ ⊢[PRAAx] gcd u M ≐ one) (hv : Γ ⊢[PRAAx] gcd v M ≐ one) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hst : Γ ⊢[PRAAx] gcd (ord u M) (ord v M) ≐ one) :
    Γ ⊢[PRAAx] ord (u * v) M ≐ ord u M * ord v M := by
  have hs : Γ ⊢[PRAAx] ord u M ≐ succ (pred (ord u M)) := congrSucc (pred_succ _).eqSymm
  have ht : Γ ⊢[PRAAx] ord v M ≐ succ (pred (ord v M)) := congrSucc (pred_succ _).eqSymm
  have he : Γ ⊢[PRAAx] ord (u * v) M ≐ succ (pred (ord (u * v) M)) := congrSucc (pred_succ _).eqSymm
  have huv := cop_uv hu0 hv0 hu hv hM
  have ce := order_cong huv hM
  -- `s ∣ e`
  have cu := pow_u_one hu0 hv0 hu hv hM _ ce
  have se1 : Γ ⊢[PRAAx] dvd (ord u M) (ord (u * v) M * ord v M) := order_dvd_of_pow hu hM cu
  have se2 : Γ ⊢[PRAAx] dvd (ord u M) (ord (u * v) M * ord u M) := dvd_of_eq' hs (mul_comm _ _)
  have se := dvd_of_coprime_pair hs se1 se2 (gcd_comm_one ht hst)
  -- `t ∣ e`, by symmetry
  have ce' : Γ ⊢[PRAAx] rem (pw (v * u) (ord (u * v) M)) M ≐ rem one M :=
    (congrAp2 remF (congrAp2 powF (.eqRefl _) (mul_comm v u)) (.eqRefl _)).eqTrans ce
  have cv := pow_u_one hv0 hu0 hv hu hM _ ce'
  have te1 : Γ ⊢[PRAAx] dvd (ord v M) (ord (u * v) M * ord u M) := order_dvd_of_pow hv hM cv
  have te2 : Γ ⊢[PRAAx] dvd (ord v M) (ord (u * v) M * ord v M) := dvd_of_eq' ht (mul_comm _ _)
  have te := dvd_of_coprime_pair ht te1 te2 hst
  have ste := mul_dvd_of_coprime hs ht se te hst
  exact le_antisymm (dvd_le' he (ord_mul_dvd hu0 hv0 hu hv hM) (pos_mul hs ht)) (dvd_le' (pos_mul hs ht) ste he)

end LeanProofs.IPRA.AnalyticNumberTheory.OrderProduct
