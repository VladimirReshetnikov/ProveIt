import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.DiophantineNumberTheory.ModularCertificate

/-!
# The Frobenius identity for two numbers

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem
`el:binomial`, second assertion: `(x + y)^p ≡ x^p + y^p (mod p)` for a prime `p`.

The divisibility `p ∣ C(p, k)` for `0 < k < p` is `Fermat.prime_dvd_binom`, and the case `y = 1` of the
congruence is `Fermat.freshman`. For two natural numbers the congruence follows from Fermat's little theorem
`Fermat.fermat_at`, `a^p ≡ a (mod p)`, applied to `x + y`, `x` and `y`:

* **`frobenius`**: `(x + y)^p mod p = (x^p + y^p) mod p`.

The coefficientwise identity for finite polynomials modulo `p` is not derived.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.FrobeniusSum

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- **Frobenius**: `(x + y)^p ≡ x^p + y^p (mod p)` for a prime `p`. -/
theorem frobenius {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (x y : PTm n) :
    Γ ⊢[PRAAx] rem (pw (x + y) p) p ≐ rem (pw x p + pw y p) p :=
  (fermat_at hp (x + y)).eqTrans
    (rem_add_congr (p_pos (prime_two hp)) (fermat_at hp x).eqSymm (fermat_at hp y).eqSymm)

end LeanProofs.IPRA.AnalyticNumberTheory.FrobeniusSum
