# A bounded degree obstruction for residual shears

The [independent review](../../reviews/frontier13-low-degree-shear-obstruction-independent-audit/README.md)
reconstructed the leading supports and fixed-beta coefficient and checked the
bounded-degree noncancellation argument. The scope below remains essential.

The 13-variable degree-36 square-sum equation is a sum of four integer
residual squares. Write its residuals as `A0`, `A1`, `S = g72`, and
`N = auxResidual`. Their witness degrees, treating the four ports as
coefficients, are respectively **15, 13, 10, 18**.

Consider the zero-set-preserving shear

```text
N' = N + H0*A0 + H1*A1 + HS*S,
P' = A0² + A1² + S² + (N')².
```

Here the multipliers are arbitrary integer-coefficient polynomials in the
13 witnesses, possibly with polynomial dependence on the fixed ports, subject
only to the witness-degree bounds

```text
deg(H0) <= 3,    deg(H1) <= 5,    deg(HS) <= 8.
```

For integer assignments, `P'=0` iff all four sheared residuals vanish, which
is equivalent to `A0=A1=S=N=0`; hence it has the same integer zero set as
the original four-square equation. This elementary equivalence is not a Lean
theorem in this packet.

The exact sparse computation in `check.py` verifies that every top-degree
monomial of `A0`, `A1` and `S` contains `eta` or `zeta`. It also verifies
that the coefficient of the degree-18 witness monomial

```text
J^8 * f^6 * X^2 * Y^2
```

in `N` is **exactly `beta^8`**, with no other port contribution at that
witness monomial. This monomial contains neither `eta` nor `zeta`. Because
the stated multiplier bounds give `deg(H0*A0) <= 18`,
`deg(H1*A1) <= 18` and `deg(HS*S) <= 18`, their degree-18 terms must come
from the leading parts of the respective residuals. Every such term still
contains `eta` or `zeta`, so none can change the displayed coefficient.
The recorded actual beta bytes are checked to be `2^94517 - 1`, hence that
coefficient remains nonzero after specializing all four actual ports.
Consequently `deg(N') = 18`. The other residuals have degree at most 15,
so `(N')²` is the only degree-36 contribution to `P'`; it is nonzero over
the integer polynomial ring. Thus **`deg(P') = 36`** after the actual port
specialization, and the usual positive-variable shift preserves that degree.

This is a bounded obstruction, not a general lower bound. It does not exclude
higher-degree multipliers whose high terms cancel across several shears,
changing the other residuals, non-shear transformations, alternative
variables, a different polynomial with the same zero set, or lower degree by
another construction. It does not claim an iPRA derivation or global
minimality. The connection between the saved beta bytes and the displayed
fixed-port recipe inherits the existing [independent finite binding review](../../reviews/frontier13-pdf-historical-lean-binding-independent-audit/README.md),
including its manually transcribed decoder/rank boundary.

The checker pins the graph, port metadata and independent binding receipt;
reconstructs the residuals exactly as sparse integer polynomials; verifies
the original four-square wiring; checks a concrete maximum-degree shear; and
rejects three graph mutations. The arbitrary-multiplier conclusion is the
degree/support argument above, not a finite enumeration of multipliers.
Optimized Python is rejected. `run.py` records actual subprocess exits and
refuses to overwrite its receipt; run `check.py` directly for a read-only
rerun. Independent review of this new obstruction is required before relying
on it.
