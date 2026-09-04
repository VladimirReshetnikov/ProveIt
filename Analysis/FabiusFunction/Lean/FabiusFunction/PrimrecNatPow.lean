import Mathlib.Computability.Partrec

/-!
# Primitive recursiveness of natural exponentiation, in curried form

Mathlib proves `Nat.Primrec.pow` for the *uncurried* power function
(`Nat.Primrec (Nat.unpaired (· ^ ·))`); every dyadic evaluator in this
development needs the curried two-argument form instead, and four modules
had each restated it privately.  It lives here once.

* `primrec₂_nat_pow` — `Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ)`.
* `computable₂_nat_pow` — its `Computable₂` shadow.
-/

set_option autoImplicit false

namespace Fabius

/-- Natural exponentiation is primitive recursive in both arguments. -/
theorem primrec₂_nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- Natural exponentiation is computable in both arguments. -/
theorem computable₂_nat_pow : Computable₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  primrec₂_nat_pow.to_comp

end Fabius
