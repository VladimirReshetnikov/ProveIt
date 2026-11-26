import IPRADerivations.Core.Integers

/-!
# Pullback certificates for the Euler and Pfaff transformations

Packet: `analysis/hypergeometric_ipra_2026-11-16`, `sections/07_transformations.tex`, Lemma
`lem:pullback-certificate` and its uses in Theorem `thm:euler-transform` and Theorem `thm:pfaff`: for
`g(z) = p(z) v(φ(z))` with `v` a solution of the source equation `L_{A,B,C} v = 0`, differentiating
twice and eliminating `v″` gives `L_{a,b,c} g = R₀ v(φ) + R₁ v′(φ)`, and "clearing all denominators turns
`R₀ = R₁ = 0` into polynomial identities".

With `L_{a,b,c} y = z(1 − z) y″ + (c − (a + b + 1) z) y′ − ab y` and integer terms `a`, `b`, `c`, `z`:

**Euler**, `φ(z) = z`, `p = (1 − z)^s`, `s = c − a − b`, source parameters `(c − a, c − b, c)`
(`p′/p = −s/(1 − z)`, `p″/p = s(s − 1)/(1 − z)²`):

* `euler_R1`: `−2sz − (c − (A + B + 1) z) + (c − (a + b + 1) z) = 0`, the coefficient of `p v′`;
* `euler_R0`: `z s (s − 1) + AB (1 − z) − s (c − (a + b + 1) z) − ab (1 − z) = 0`, the coefficient of
  `p v` multiplied by `1 − z`.

**Pfaff**, `φ(z) = z/(z − 1)`, `p = (1 − z)^{−a}`, source parameters `(a, c − b, c)`
(`p′/p = a/(1 − z)`, `p″/p = a(a + 1)/(1 − z)²`, `φ′ = −1/(1 − z)²`, `φ″ = −2/(1 − z)³`,
`φ(1 − φ) = −z/(1 − z)²`):

* `pfaff_R0`: `z a (a + 1) − a (c − b) + a (c − (a + b + 1) z) − ab (1 − z) = 0`, the coefficient of
  `p v` multiplied by `1 − z`;
* `pfaff_R1`: `−2(a + 1) z + c (1 − z) + (a + (c − b) + 1) z − c + (a + b + 1) z = 0`, the coefficient of
  `p v′` multiplied by `(1 − z)²`.

The second Pfaff transformation is the same certificate with `a` and `b` exchanged. The symbolic chain
rule that produces the residuals, and the uniqueness of the normalized solution that turns the
certificates into the transformation formulas, are the reading of these identities; they are not
formalized here.
-/

namespace LeanProofs.IPRA.Analysis.PullbackCertificates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Euler: the coefficient of `p v′` vanishes. -/
theorem euler_R1 (a b c z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (-(ZT.natLit 2 * (c - a - b) * z) - (c - ((c - a) + (c - b) + ZT.natLit 1) * z) +
        (c - (a + b + ZT.natLit 1) * z))
      (ZT.natLit 0) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit]
    push_cast
    ring)

/-- Euler: the coefficient of `p v`, multiplied by `1 − z`, vanishes. -/
theorem euler_R0 (a b c z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (z * (c - a - b) * ((c - a - b) - ZT.natLit 1) + (c - a) * (c - b) * (ZT.natLit 1 - z) -
        (c - a - b) * (c - (a + b + ZT.natLit 1) * z) - a * b * (ZT.natLit 1 - z))
      (ZT.natLit 0) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit]
    push_cast
    ring)

/-- Pfaff: the coefficient of `p v`, multiplied by `1 − z`, vanishes. -/
theorem pfaff_R0 (a b c z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (z * a * (a + ZT.natLit 1) - a * (c - b) + a * (c - (a + b + ZT.natLit 1) * z) -
        a * b * (ZT.natLit 1 - z))
      (ZT.natLit 0) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit]
    push_cast
    ring)

/-- Pfaff: the coefficient of `p v′`, multiplied by `(1 − z)²`, vanishes. -/
theorem pfaff_R1 (a b c z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (-(ZT.natLit 2 * (a + ZT.natLit 1) * z) + c * (ZT.natLit 1 - z) +
        (a + (c - b) + ZT.natLit 1) * z - c + (a + b + ZT.natLit 1) * z)
      (ZT.natLit 0) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, ZT.toZ_natLit]
    push_cast
    ring)

end LeanProofs.IPRA.Analysis.PullbackCertificates
