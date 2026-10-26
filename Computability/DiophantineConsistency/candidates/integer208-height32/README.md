# A 208-integer quartic for Con(ZFC) with coefficient height 2^32

One explicit polynomial P = Σ rᵢ² in 208 unrestricted integer variables,
the sum of squares of 148 quadratic residuals, with exact degree 4, 5,987
collected terms and coefficient height 2^32 = 4,294,967,296. ZFC proves
that P has no integer zero if and only if Con(ZFC), by the argument below.

The residuals are in `equation.json` and the construction certificate in
`certificate.json`. `verify.py` rebuilds the equation from its parent and
checks every figure; `CHECKS.json` records its output.

## What it improves

It is wave-24 package 191's principal 208-integer quartic with smaller
coefficients:

| Quartic | Variables | Residuals | Terms | Height |
|---|---:|---:|---:|---:|
| 191's `principal208` (parent) | 208 | 148 | 5,987 | 2^44 |
| **this equation** | **208** | **148** | **5,987** | **2^32** |

It equals the parent on the first three measures and has a coefficient
height 4,096 times lower, so it dominates the parent outright. It keeps the
fewest variables of any direct ℤ quartic in the
[collection's frontier](../../con-zfc-diophantine-forms/README.md#combined-frontier-waves-525-intake-findings)
after wave 25.

Against the nearest frontier points it is a Pareto point:

| Quartic | Variables | Residuals | Terms | Height |
|---|---:|---:|---:|---:|
| 190's 209 (two forms) | 209 | 149 | 5,486 and 6,654 | 2^32 and 2^30 |
| 195's 209 | 209 | 149 | 5,278 | 2^46 |
| 189's 209 | 209 | 150 | 5,283 | about 2.75·10^11 |

It does not dominate these; it has one fewer variable and residual, and
more terms.

**Not a size improvement.** The variable, residual and term counts are
unchanged from 191's. Only the coefficients are smaller. It is not a
significantly smaller equation in the sense of fewer unknowns or terms.

## Construction

1. **Rescale F.** In the parent, the residual labelled
   `growth_pell.divisibility` is
   F − 2^20·(1 + 2z)(1 + 2h), where F is `growth.F`, z is
   `horizon.affine_parameter` and h is `growth_pell.odd_half`. Substitute
   F = 64·f in every residual, where f is the new variable `growth.f`, and
   divide each residual by the gcd of its coefficients.
2. **Row operations.** Apply 487 elementary operations rᵢ := rᵢ + c·rⱼ
   (i ≠ j, small integers c), listed in `certificate.json`. A greedy search
   chose them: each one lowers the coefficient height of Σ rᵢ² and adds no
   term.

The scale 64 was chosen by search:
- pure rescaling was tried at every power of two up to 2^20;
- the row search was run at scales 64, 128, 256, 1,024 and 4,096.

Larger scales raise the height of the rows that contain F faster than they
lower the divisibility row. After rescaling, the divisibility row is
f − 2^14 − 2^15·z − 2^15·h − 2^16·zh. The remaining height 2^32 comes only
from products of that row's own coefficients: (2^16)² on z²h²,
2·2^15·2^16 on zh² and on z²h, and 2·2^14·2^16 + 2·2^15·2^15 on zh.

## Why it has the same theorem

Let Z be the set of integer zeros of 191's residual system, and Z' that of
this one.

- **Rescaling.** Every point of Z satisfies F = 2^20(1 + 2z)(1 + 2h), so
  64 | F. Hence x ↦ (x with F replaced by F/64) is a bijection from Z onto
  the zeros of the rescaled system. Dividing a residual by a nonzero
  integer constant does not change its zeros.
- **Row operations.** Each step replaces the residual vector by its image
  under an elementary integer matrix, which is invertible over ℤ, so the
  common zero set does not change.
- **Sum of squares.** Over the integers Σ rᵢ² = 0 if and only if every
  rᵢ = 0.

So P has an integer zero if and only if 191's quartic has one. The bijection
is elementary and formalizable in PA. Package 191's ordinary proof that its
quartic has no integer zero if and only if Con(ZFC) is therefore inherited
unchanged. That proof uses the C222 calibration through
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. This equation adds
no new mathematics and needs nothing beyond 191's argument, which this
repository's intake reviewed (wave 24) but did not formalize.

## Verification

From the repository root:

```sh
py -I Computability/DiophantineConsistency/candidates/integer208-height32/verify.py
```

The script:
- pins the parent by SHA-256;
- checks the divisibility row as a polynomial identity at random rational
  points;
- rebuilds the residuals from the parent and the certificate, and checks
  them against `equation.json`;
- re-expands the sum of squares and checks 208 variables (all occurring),
  148 residuals, residual degree at most 2, total degree 4, 5,987 terms and
  height 2^32.

It writes nothing unless given `--write`.

## Credit and provenance

- **Parent:** wave-24 package 191,
  [`191-sparse-syntax-weighted-transport`](../../con-zfc-diophantine-forms/191-sparse-syntax-weighted-transport/).
- **Scaling device:** wave-24 package 190 scales F in its own 209s.
- **The observation:** the intake dossier for 190–191 noticed that the
  scaling applies to 191's 208 and measured 208 / 148 / 5,987 /
  30,413,860,158. The wave-24 section lists it as further question 1.
- **This candidate's work:** the row-operation search that lowers the
  height to 2^32 while keeping 5,987 terms, the certificate and the
  verifier.

Prepared 25 October 2026 by the intake session (Claude) for Vladimir
Reshetnikov.
