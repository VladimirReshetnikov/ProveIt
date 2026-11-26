import IPRADerivations.Core.Integers

/-!
# The normal form `u″ + Q u = 0` of the hypergeometric equation

Packet: `analysis/hypergeometric_ipra_2026-11-16`, `sections/05_ode.tex`, Proposition `prop:q-form`
("Elimination of the first derivative"): with `y = v u`, `v = z^{−c/2} (1 − z)^{(c−a−b−1)/2}`, the
equation `y″ + P y′ + R y = 0` (`P = (c − (a + b + 1) z)/(z (1 − z))`, `R = −ab/(z (1 − z))`) becomes
`u″ + Q u = 0` with

`Q(z) = (z² [1 − (a − b)²] + z [2c (a + b − 1) − 4ab] + c (2 − c)) / (4 z² (1 − z)²)`.

"The coefficient of `u′` is `2v′/v + P`, which vanishes because
`v′/v = −c/(2z) − (1 + a + b − c)/(2(z − 1)) = −P/2`. The remaining coefficient is `R − P′/2 − P²/4`.
Clearing the denominator `4z²(1 − z)²` and expanding yields the displayed numerator. This is a polynomial
identity".

With integer terms `a`, `b`, `c`, `z` (signed, `Core/Integers`):

* `gauge`: `−c (1 − z) + (1 + a + b − c) z = −(c − (a + b + 1) z)`, i.e. `v′/v = −P/2` multiplied by
  `2z(1 − z)`;
* `Pn`, `dPn`: the numerator `c − (a + b + 1) z` of `P` and the numerator
  `−(a + b + 1) z (1 − z) − (c − (a + b + 1) z)(1 − 2z)` of `P′` over `(z(1 − z))²` (quotient rule);
* `q_form`: `−4ab z (1 − z) − 2 dPn − Pn² = z² (1 − (a − b)²) + z (2c (a + b − 1) − 4ab) + c (2 − c)`,
  i.e. `4z²(1 − z)² (R − P′/2 − P²/4)` equals the printed numerator of `Q`.

The differential calculus (that `v u` transforms the equation in this way) is the reading of the two
identities; it is not formalized.
-/

namespace LeanProofs.IPRA.Analysis.HypergeometricQForm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `v′/v = −P/2`, multiplied by `2z(1 − z)`. -/
theorem gauge (a b c z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (-c * (ZT.natLit 1 - z) + (ZT.natLit 1 + a + b - c) * z)
      (-(c - (a + b + ZT.natLit 1) * z)) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit]
    push_cast
    ring)

/-- The numerator of `P = (c − (a + b + 1) z) / (z (1 − z))`. -/
def Pn (a b c z : ZT n) : ZT n := c - (a + b + ZT.natLit 1) * z

/-- The numerator of `P′` over `(z (1 − z))²`, by the quotient rule. -/
def dPn (a b c z : ZT n) : ZT n :=
  -(a + b + ZT.natLit 1) * (z * (ZT.natLit 1 - z)) - Pn a b c z * (ZT.natLit 1 - ZT.natLit 2 * z)

/-- `prop:q-form`: `4z²(1 − z)² (R − P′/2 − P²/4)` is the printed numerator of `Q`. -/
theorem q_form (a b c z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (-(ZT.natLit 4 * a * b) * (z * (ZT.natLit 1 - z)) - ZT.natLit 2 * dPn a b c z -
        Pn a b c z * Pn a b c z)
      (z * z * (ZT.natLit 1 - (a - b) * (a - b)) +
        z * (ZT.natLit 2 * c * (a + b - ZT.natLit 1) - ZT.natLit 4 * a * b) +
        c * (ZT.natLit 2 - c)) :=
  ZT.derive (by
    simp only [dPn, Pn, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit]
    push_cast
    ring)

end LeanProofs.IPRA.Analysis.HypergeometricQForm
