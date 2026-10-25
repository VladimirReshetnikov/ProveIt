# Normalized remainders for Diophantine consistency

Prepared for Vladimir Reshetnikov, 25 October 2026, with AI assistance.

The primary completed equation is an explicit integer-coefficient quartic in
**252 unrestricted integer variables**, supplied as all **182 quadratic
residuals** and as every collected coefficient. It has **5,340 monomials** and
coefficient height **128,446**. The ordinary mathematical theorem, formalizable
in ZFC, is that its lack of integer solutions is equivalent in ZFC to Con(ZFC).

This improves the pinned round-17 direct-calculus parent in all three varying
measures: 282 to 252 variables, 192 to 182 residuals, and 5,491 to 5,340
monomials. Degree four and coefficient height 128,446 are unchanged. It is a
new improvement of the direct C222 construction; it is not a claim of a global
minimum, a new complete proof-assistant endpoint, or a proof of consistency.

The mathematical idea is to replace eleven separately certified intervals by
one bound on normalized binomial remainders. Every remainder is represented
at the already available common denominator. A single sum of squares makes
all reconstructed remainders short, and the genuine binomial coefficients
make their canonical values much shorter. Congruence then recovers the exact
ordinary remainders. The construction adds three quotient coordinates and
three common bound witnesses while removing 33 private sign witnesses; three
additional range denominator products become one shared product.

## Files

- `equation/equation.json`: the entire fixed residual list, in order.
- `equation/expanded_polynomial.json`: every coefficient of their sum of squares.
- `proofs/NORMALIZED_REMAINDERS_PROOF.md`: complete proof of the new transformation,
  with the dependency order and explicit constants.
- `proofs/INDEPENDENT_REVIEW.md`: separate mathematical review.
- `data/`: exact source, source edits, guards, Horn factoring, integral projections,
  and uncentered intermediate polynomial.
- `code/`: self-contained, standard-library-only builder and independent verifier.
- `upstream/`: pinned parent inputs, source hashes, licensing, and the inherited
  arithmetic/calculus proof closure including the retained Lean interface files.

A sparse term `[c,[i,j,...]]` means `c*x_i*x_j*...`, using zero-based coordinate
indices in the adjacent variable list. A repeated index is a power; an empty
index list is a constant. The final equation is the sum of the squares of
every listed residual. There are no variable-exponent or unspecified
universal-polynomial primitives in the final JSON.

## Verify and reproduce

From any working directory, with Python 3.10 or newer:

```sh
python3 -B /path/to/code/verify.py
python3 -B -O /path/to/code/verify.py
python3 -B /path/to/code/verify.py --rebuild
```

`--rebuild` recreates both the source transformation and the final centered
equation in a temporary directory and compares all 19 emitted JSON files
byte for byte. It needs no network, repository checkout, or third-party Python
package. Use `--output PATH` to save a verification receipt; put it outside an
already sealed package when preserving that package's checksum manifest.

The independent checker imports no producer module. It reconstructs the
eleven digit edits and the new guards, uses the inherited independent Horn
checker for all 18 factoring edits, and independently checks all 205 monic
projections, the final integral translation, and the complete collected
quartic. Seven deliberately corrupted artifacts are rejected. Both ordinary
Python and optimization mode preserve all checks.

These programs verify the finite polynomial data and algebraic maps. The
unbounded Pell, factorial, CRT, and logical-calibration arguments are supplied
by the mathematical proofs, not by finite numerical sampling. The full result
is an ordinary proof with identified inherited formal interfaces, not a newly
emitted end-to-end Lean/Rocq proof term.

## Provenance

The comparison snapshot is ProveIt commit
`55d1f72aedebf892e446c90d35fa1ae37689b0f2`, including its incoming archive
`ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip`.
`upstream/SOURCE_PINS.json` contains the exact archive hash and all retained
proof-file identities. No upstream repository mutation is part of this package.

New material uses the repository's MIT No Attribution license. Inherited
material retains its notices. The mathematics, code, and exposition were
developed with AI assistance; no human review or institutional endorsement is
implied.
