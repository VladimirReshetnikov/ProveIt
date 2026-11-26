import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Coprimality to a modulus `q ≥ 1`

Infrastructure for `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`,
`thm:finite-sieve`, which is stated for every modulus `q ≥ 1`.

`AnalyticNumberTheory/Euler` proves the closure of the units modulo `N` under products and factors for `N ≥ 2`
(`cop_mul`, `cop_of_mul`), where `gcd(x, N) = 1` forces `x ≥ 1`. Here the same facts are derived for a modulus
`q ≥ 1`, with no positivity hypothesis on the other argument, so that the sieve also covers `q = 1`:

* `pos_of_one_le`, `two_le_of_ne`: `q ≥ 1` as `q = (q − 1) + 1`, and `q ≥ 1`, `q ≠ 1` give `q ≥ 2`;
* `cop_symm`: `gcd(q, x) = 1` gives `gcd(x, q) = 1`;
* `cop_mul`: `gcd(d, q) = gcd(e, q) = 1` gives `gcd(d e, q) = 1`;
* `cop_of_mul`: `gcd(a i, q) = 1` gives `gcd(i, q) = 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_greatest' eq_one_of_dvd_one dvd_mul' gcd_comm_one
  coprime_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `q ≥ 1` in the form `q = (q − 1) + 1`. -/
alias pos_of_one_le := Common.pos_of_one_le

/-- `q ≥ 1` and `q ≠ 1` give `q ≥ 2`. -/
theorem two_le_of_ne {q : PTm n} (hq : Γ ⊢[PRAAx] le one q) (hne : Γ ⊢[PRAAx] neg (q ≐ one)) :
    Γ ⊢[PRAAx] le two q := by
  refine .orE (lt_or_le one q) Prf.hyp0 ?_
  exact .botE _ (Prf.impE (hne.wk (ψ := le q one)) (le_antisymm Prf.hyp0 (hq.wk (ψ := le q one))))

/-- `gcd(q, x) = 1` gives `gcd(x, q) = 1`, for `q ≥ 1` and any `x`. -/
theorem cop_symm {x q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (h : Γ ⊢[PRAAx] gcd q x ≐ one) :
    Γ ⊢[PRAAx] gcd x q ≐ one := by
  have g := gcd_pos_right (a := x) hq
  have dg := gcd_dvd_at g
  exact eq_one_of_dvd_one g (dvd_congr h (gcd_greatest' g (Prf.andE₂ dg) (Prf.andE₁ dg)))

/-- `gcd(d, q) = gcd(e, q) = 1` gives `gcd(d e, q) = 1`, for `q ≥ 1`. -/
theorem cop_mul {d e q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hd : Γ ⊢[PRAAx] gcd d q ≐ one)
    (he : Γ ⊢[PRAAx] gcd e q ≐ one) : Γ ⊢[PRAAx] gcd (d * e) q ≐ one :=
  cop_symm hq (coprime_mul hq (gcd_comm_one hq hd) (gcd_comm_one hq he))

/-- `gcd(a i, q) = 1` gives `gcd(i, q) = 1`, for `q ≥ 1`. -/
theorem cop_of_mul {a i q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (h : Γ ⊢[PRAAx] gcd (a * i) q ≐ one) : Γ ⊢[PRAAx] gcd i q ≐ one := by
  have g := gcd_pos_right (a := i) hq
  have dg := gcd_dvd_at g
  have dai := dvd_congr (mul_comm _ _) (dvd_mul' g a (Prf.andE₁ dg))
  exact eq_one_of_dvd_one g (dvd_congr h (gcd_greatest' g dai (Prf.andE₂ dg)))

end LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus
