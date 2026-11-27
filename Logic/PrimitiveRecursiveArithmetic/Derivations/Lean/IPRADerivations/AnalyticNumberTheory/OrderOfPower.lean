import IPRADerivations.AnalyticNumberTheory.OrderDivides
import IPRADerivations.AnalyticNumberTheory.PlusPower
import IPRADerivations.DiophantineNumberTheory.ConicGcd

/-!
# The order of a power

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`, Corollary
`qr:primitive-count`, the first formula: `ord(g^k) = N / gcd(N, k)` for an element `g` of order `N`.

It holds for every modulus and every unit, not only for a primitive root modulo a prime: for `a ≥ 1` with
`gcd(a, M) = 1`, `M ≥ 1`, `k ≥ 1`, `O = ord(a, M)` and `d = gcd(k, O)`,

    ord(a^k, M) = O / d                                                   (**`ord_pow`**).

The proof is the packet's: "The equation `(g^k)^j = 1` is equivalent to `N ∣ k j`. Dividing by `d = gcd(N, k)`
and using coprimality shows that this is equivalent to `N/d ∣ j`."

* `cop_power`: `gcd(a^k, M) = 1`;
* `(a^k)^{O/d} = a^{(k/d) O} ≡ 1`, so `ord(a^k) ∣ O/d` (`OrderDivides.order_dvd_of_pow`);
* `a^{k e} ≡ 1` for `e = ord(a^k)`, so `O ∣ k e`, hence `O/d ∣ (k/d) e` and `O/d ∣ e` because
  `gcd(k/d, O/d) = 1` (`Coprime.coprime_quotients`, `ConicGcd.dvd_of_coprime_pair`);
* `ord_pow_mul`: `ord(a^k, M) · gcd(k, O) = O`;
* `ord_pow_coprime`: if `gcd(k, O) = 1` then `ord(a^k, M) = O` (the powers with exponent coprime to the order
  have the full order; for a primitive root these are the primitive roots).

The count `φ(N)` of primitive roots and the solution count of `x^k = b` are not derived.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.OrderOfPower

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul quo_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (ord order_cong)
open LeanProofs.IPRA.AnalyticNumberTheory.OrderDivides (order_dvd_of_pow pow_of_order_dvd)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `gcd(a, M) = 1` gives `gcd(a^k, M) = 1`, for `a, M ≥ 1`. -/
theorem cop_power {a M : PTm n} (ha0 : Γ ⊢[PRAAx] a ≐ succ (pred a)) (ha : Γ ⊢[PRAAx] gcd a M ≐ one)
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (k : PTm n) : Γ ⊢[PRAAx] gcd (pw a k) M ≐ one :=
  gcd_comm_one (pw_pos' ha0 k) (cop_pow hM (gcd_comm_one hM ha) k)

theorem ku_alg {k d K O u : PTm n} (eK : Γ ⊢[PRAAx] k ≐ d * K) (eO : Γ ⊢[PRAAx] O ≐ d * u) :
    Γ ⊢[PRAAx] k * u ≐ O * K := by
  ipra_lc 𝔞 u * natEq eK - 𝔞 K * natEq eO

theorem cancel_alg {k d K O u e q : PTm n} (eK : Γ ⊢[PRAAx] k ≐ d * K) (eO : Γ ⊢[PRAAx] O ≐ d * u)
    (eq1 : Γ ⊢[PRAAx] k * e ≐ O * q) : Γ ⊢[PRAAx] d * (e * K) ≐ d * (u * q) := by
  ipra_lc -𝔞 e * natEq eK + natEq eq1 + 𝔞 q * natEq eO

/-- **The order of a power**: `ord(a^k, M) = ord(a, M) / gcd(k, ord(a, M))`. -/
theorem ord_pow {a M k : PTm n} (ha0 : Γ ⊢[PRAAx] a ≐ succ (pred a)) (ha : Γ ⊢[PRAAx] gcd a M ≐ one)
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] ord (pw a k) M ≐ quo (ord a M) (gcd k (ord a M)) := by
  have hO : Γ ⊢[PRAAx] ord a M ≐ succ (pred (ord a M)) := congrSucc (pred_succ _).eqSymm
  have hE : Γ ⊢[PRAAx] ord (pw a k) M ≐ succ (pred (ord (pw a k) M)) := congrSucc (pred_succ _).eqSymm
  have hd := gcd_pos (B := ord a M) hk
  have hdd := gcd_dvd' (b := ord a M) hk
  have eK := eq_of_dvd' hd (Prf.andE₁ hdd)
  have eO := eq_of_dvd' hd (Prf.andE₂ hdd)
  have hu := pos_of_eq_mul hO eO
  have hak := cop_power ha0 ha hM k
  -- `ord(a^k) ∣ O/d`
  have d1 : Γ ⊢[PRAAx] dvd (ord a M) (k * quo (ord a M) (gcd k (ord a M))) := dvd_of_eq' hO (ku_alg eK eO)
  have c1 : Γ ⊢[PRAAx] rem (pw (pw a k) (quo (ord a M) (gcd k (ord a M)))) M ≐ rem one M :=
    (congrAp2 remF (pw_mul a k _) (.eqRefl _)).eqTrans (pow_of_order_dvd ha hM d1)
  have eu : Γ ⊢[PRAAx] dvd (ord (pw a k) M) (quo (ord a M) (gcd k (ord a M))) := order_dvd_of_pow hak hM c1
  -- `O/d ∣ ord(a^k)`
  have c2 : Γ ⊢[PRAAx] rem (pw a (k * ord (pw a k) M)) M ≐ rem one M :=
    (congrAp2 remF (pw_mul a k _).eqSymm (.eqRefl _)).eqTrans (order_cong hak hM)
  have d2 : Γ ⊢[PRAAx] dvd (ord a M) (k * ord (pw a k) M) := order_dvd_of_pow ha hM c2
  have eq1 := eq_of_dvd' hO d2
  have h1 : Γ ⊢[PRAAx] dvd (quo (ord a M) (gcd k (ord a M))) (ord (pw a k) M * quo k (gcd k (ord a M))) :=
    dvd_of_eq' hu (Combinatorics.BinomialIdentities.mul_cancel hd (cancel_alg eK eO eq1))
  have h2 : Γ ⊢[PRAAx] dvd (quo (ord a M) (gcd k (ord a M)))
      (ord (pw a k) M * quo (ord a M) (gcd k (ord a M))) := dvd_of_eq' hu (mul_comm _ _)
  have ue := dvd_of_coprime_pair hu h1 h2 (coprime_quotients (c := ord a M) hk)
  exact le_antisymm (dvd_le' hE eu hu) (dvd_le' hu ue hE)

theorem mul_alg {E O d u : PTm n} (e : Γ ⊢[PRAAx] E ≐ u) (eO : Γ ⊢[PRAAx] O ≐ d * u) :
    Γ ⊢[PRAAx] E * d ≐ O := by
  ipra_lc 𝔞 d * natEq e - natEq eO

/-- `ord(a^k, M) · gcd(k, ord(a, M)) = ord(a, M)`. -/
theorem ord_pow_mul {a M k : PTm n} (ha0 : Γ ⊢[PRAAx] a ≐ succ (pred a)) (ha : Γ ⊢[PRAAx] gcd a M ≐ one)
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] ord (pw a k) M * gcd k (ord a M) ≐ ord a M :=
  mul_alg (ord_pow ha0 ha hM hk)
    (eq_of_dvd' (gcd_pos (B := ord a M) hk) (Prf.andE₂ (gcd_dvd' (b := ord a M) hk)))

/-- If `gcd(k, ord(a, M)) = 1` then `a^k` has the order of `a`. -/
theorem ord_pow_coprime {a M k : PTm n} (ha0 : Γ ⊢[PRAAx] a ≐ succ (pred a)) (ha : Γ ⊢[PRAAx] gcd a M ≐ one)
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (hc : Γ ⊢[PRAAx] gcd k (ord a M) ≐ one) : Γ ⊢[PRAAx] ord (pw a k) M ≐ ord a M :=
  (ord_pow ha0 ha hM hk).eqTrans ((congrAp2 quoF (.eqRefl _) hc).eqTrans (quo_one _))

end LeanProofs.IPRA.AnalyticNumberTheory.OrderOfPower
