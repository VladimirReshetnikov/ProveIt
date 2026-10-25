# Integral endpoint maps for the strict-horizon source

## Scope

This component starts with the complete strict-horizon quadratic system
in `direct/source/equation.json`. Its source has 239
unrestricted integer coordinates and 176 residuals. The change in
arithmetic semantics (strict ranges, common denominator, linear radius,
growth base, and affine radix) is proved separately by the source report.
The present argument supplies complete integral transformations from that
literal source to two smaller quartics.

| Endpoint | Variables over Z | Rows | Degree | Terms | Height | Residual height |
|---|---:|---:|---:|---:|---:|---:|
| Strict source | 239 | 176 | 4 | 5138 | 128446 | 256 |
| Principal | 236 | 173 | 4 | 4876 | 7968 | 64 |
| Dense companion | 235 | 172 | 4 | 12566 | 7968 | 64 |

All counts refer to the full collected polynomial, not uncollected
sum-of-squares syntax. Every final coordinate occurs in the polynomial.

## The six coordinate shears

The source metadata names are retained. Each substitution replaces an old
coordinate by its new coordinate plus the indicated linear expression:

| Target | Added expression |
|---|---|
| mul.40 | -2 crt.encoded.a -2 crt.encoded.b |
| mul.53 | -8 add.50 |
| mul.148 | -8 add.145 |
| mul.137 | -4 crt.encoded.a -5 crt.encoded.c -2 mul.64 -mul.75 |
| mul.75 | -crt.encoded.a -crt.encoded.c |
| mul.64 | -crt.encoded.b -crt.encoded.c |

These are the inherited factorial-free endpoint shears, transported by
semantic coordinate names. A target never occurs in its own added
expression, so each shear has determinant one and an integral inverse.
They are applied in the displayed order. The inverse applies the
negated shears in reverse order; this matters because the maps need not
commute.

## Row operations and monic projections

Five preliminary integer row operations expose affine equations defining
`add.145`, `mul.346`, and `base4.T`. The dense companion additionally
eliminates `add.380`. The exact row numbers and new restoration
polynomials are in each endpoint's `certificate.json`.

Every projection has an actual current residual of the form

    x-p(other coordinates)=0

or its negative, with p an integral affine polynomial not containing x.
Substitute x=p in every row and delete that coordinate and defining row.
Any integer zero of the projected system has a unique integral extension,
and substitution sends every original integer zero to a projected zero.
Thus this operation gives a bijection of the two complete integer zero
sets. Affineness preserves the quadratic bound on each residual.

All row operations have the form R_i <- R_i+k R_j, where i differs from
j and k is a fixed integer. They are inverted by R_i <- R_i-k R_j,
in reverse operation order. They preserve the simultaneous zero set,
although the resulting sum-of-squares polynomial generally changes.

After the projections, 33 final row operations are used for the principal
endpoint and 35 for the dense endpoint. Together with the five initial
operations, this gives 38 or 40 reversible row operations. They lower
the coefficient height of the collected quartic from 128446 to 7968.

## Exact transport through original row identities

The original factorial-free affine certificates used numeric positions
that changed when the strict-horizon source removed its obsolete
successor power request. The constructor does not guess a common offset.
It builds the complete map

    original raw row
      -> factored row
      -> retained projected row
      -> projected endpoint row

for both the old and new systems. Original raw row identities transport
every operation. Every monic replacement is then recomputed from the
actual current new row, rather than reusing an old formula at a guessed
coordinate index.

One inherited final row operation used the removed successor-power row
(original raw row 239) as an input. That operation is omitted and recorded
explicitly. Omitting a row-basis improvement does not alter the source
equations or their zero set; the remaining displayed operations are all
individually invertible on the new source.

## The final theorem

For either endpoint, let P be the sum of the squares of its supplied
quadratic residuals. Over integers P=0 if and only if every residual is
zero. The integral maps above prove that this happens for some endpoint
tuple if and only if the strict-horizon source has an integer zero.

Composing with the separately proved source theorem and the inherited
C222/ZF/ZFC refutation calibration therefore gives

    ZFC proves: no integer zero of P iff Con(ZFC).

These are ordinary mathematical proofs formalizable in ZFC. The finite
checker authenticates the explicit polynomials and maps; it does not
stand in for their unbounded arithmetic or logical calibration.

## Independent computational audit

`code/check_endpoints.py` imports no producer modules. It independently:

1. dynamically loads the retained independent algebra checker and replays
   all 18 signed Horn and guard factorization edits from the complete raw
   strict source;
2. replays all 198 monic pivots from the complete factored strict source;
3. checks the exact translated 239-variable source;
4. verifies all six coordinate shears, preliminary and final row operations,
   and every affine restoration polynomial;
5. reconstructs all final residuals and independently collects every
   coefficient of both quartics;
6. verifies the stated degree, variable count, support, height, row height,
   and liveness of every coordinate;
7. rejects deliberately altered restoration coefficients, a noninvertible
   row operation, and an altered final residual coefficient.

Both ordinary Python and Python with optimization enabled pass. The
checker uses explicit exceptions for validation, not removable assertions.

The configurable constructor `code/build_endpoints.py` accepts `--source`, `--parent`, and
`--output`. The checker accepts `--source`, `--output`, an optional
`--factorization-checker` path, and optional `--receipt`. Rebuilding to a
fresh output directory preserves the delivered
files and allows byte-for-byte comparison.
