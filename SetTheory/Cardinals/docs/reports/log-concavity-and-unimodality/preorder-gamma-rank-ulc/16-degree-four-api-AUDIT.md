# Independent exact positivity audit: full two-attachment input set

**Verdict: APPROVED for the positivity-certificate component of the a = 2 sector.**

Both remaining degree-four inequalities hold for every one of the 89,863 supplied
canonical gamma polynomials, for every nonnegative integer population triple:

- `4 gamma_2^2 - 9 gamma_1 gamma_3 >= 0`
- `3 gamma_3^2 - 8 gamma_2 gamma_4 >= 0`

There were no missing faces, unexplained rays, nonpositive weights, failed rational
identities, normalization errors, duplicate gamma inputs, duplicate aliases, or
unreferenced certificate targets. The checked source files are bound to this
verdict by SHA-256 digests in `receipt.json`.

## Scope

This audit starts at the complete `a2_polynomials.jsonl` data set. It establishes
the exact connection from **each** of its 89,863 gamma arrays to a positivity
proof for **both** gaps. The combinatorial claim that this data set exhausts the
full two-attachment family, and that its gamma arrays equal the directed support
counts of their representatives, is the subject of the separate kernel/coverage
audit. Combining the two audits gives the a = 2 result.

The universal first degree-four inequality is an external previously established
input; it was not needed or independently reproved here. This audit makes **no
claim about the a = 3 or a = 4 sectors**, and therefore makes no unrestricted
global degree-four theorem claim.

## Independence and arithmetic

The standalone `audit.py` was independently written for this audit. It does not
import or run the producer programs, the supplied verifier, numerical packages,
or optimization solvers. The supplied verifier source was not used to construct
it. All proof-relevant calculations use Python arbitrary-precision integers and
`fractions.Fraction`; floating point is used only to measure elapsed time.

In particular:

1. The ten input basis polynomials are directly expanded as generalized binomial
   polynomials. Their exact rational expansions verify that `G_j = 2 gamma_j`
   has integral ordinary coefficients. Both target gaps are then multiplied out
   from the input arrays; the result is exactly four times the requested gap.
2. Ordinary monomials are converted to binomial coefficients by direct finite
   differences at zero, not by the producer's Stirling-number implementation.
   Each transform column is first reconstructed from products of falling-factorial
   polynomials using `Fraction`, verifying the transform identity independently.
3. Every unresolved input is independently substituted onto all eight faces:
   `x_i = 0` if the bit is absent and `x_i = 1 + y_i` if present.
4. Every non-coefficient-positive face is independently reconstructed from its
   original gamma polynomial, checked against the unresolved-face file, and
   matched to its claimed SOS target. The gcd scale, all six variable
   permutations, canonical minimum, and selected permutation are recomputed.
5. Every fixed-library ray is expanded directly from its monomial or square
   metadata. Every rational weighted sum is exactly equal to its target.
6. Every general-square ray with metadata is independently expanded as
   `y^m q(y)^2`. A ray without metadata is accepted only if all coefficients are
   nonnegative, or if it is constructively reconstructed as a rational
   monomial-weighted binomial square. This recognition uses its three actual
   coefficients and exponents; no producer ray library is trusted for it.
7. All certificate weights are strictly positive. The smallest is `1/432`.
   Large denominators are retained exactly, including the maximum denominator
   `410036205327219186409123582014950991169020080000`.
8. Input IDs are sequential and unique; all input arrays are distinct and
   canonical under exchanging the first two populations. All primitive SOS
   target arrays are distinct and canonical under all three-variable
   permutations. Every alias and target is used exactly where required.
9. All input-file SHA-256 digests are compared before and after the audit to
   rule out changes during replay.

## Why these certificates cover the domain

A generalized binomial polynomial `binom(x_i,k)` is nonnegative for every
nonnegative integer `x_i`. Thus nonnegative binomial coefficients prove the gap
on the entire integer orthant without face subdivision.

For every other polynomial, each nonnegative integer coordinate is either zero
or at least one. The eight substitutions partition all nonnegative integer
population triples. On an active face, `y_i >= 0`. Nonnegative monomials and
nonnegative monomial multiples of polynomial squares are nonnegative there.
Positive gcd scaling and variable permutation preserve nonnegativity. Hence the
verified face identities imply the original gap inequalities everywhere in the
required domain. This is an integer-domain argument; it does not claim that the
initial binomial certificates cover arbitrary real populations.

## Verified counts

| Check | Gap 2 | Gap 3 |
| --- | ---: | ---: |
| Gamma inputs | 89,863 | 89,863 |
| Globally nonnegative binomial coefficients | 63,650 | 80,954 |
| Additional inputs with all eight ordinary-positive faces | 7,796 | 5,311 |
| Inputs requiring at least one SOS face | 18,417 | 3,598 |
| SOS faces | 31,960 | 7,999 |

Totals:

- 179,726 gap instances, covering 1,437,808 population-face instances
- 144,604 whole-orthant binomial certificates
- 241,017 explicitly checked nonnegative ordinary-coefficient faces
- 39,959 exactly linked SOS faces
- 29,215 unique primitive canonical SOS targets
- 28,881 fixed-library identities, containing 382,572 positive weighted rays
- 334 general-square identities, containing 2,213 positive weighted rays
- General rays: 434 explicitly expanded polynomial squares, 339 independently
  recognized rational binomial squares, and 1,440 nonnegative-coefficient rays

The initially coefficient-certified input totals are consequently 71,446 for
gap 2 and 86,265 for gap 3, consistent with the project README's aggregate counts.

## Exceptional interior-zero identity

The audit separately reconstructs, without reading the stored certificate terms,

`4P(y,z) = (2yz-y-z-40)^2 + 27(y+z-10)^2 + 216(y-z)^2`,

where

`P(y,z) = y^2 z^2 - yz(y+z) + 61(y^2+z^2) - 134yz - 115(y+z) + 1075`.

It verifies equality to normalized target 6481 and verifies the zero at `(5,5)`.
Its complete original-input alias list is:

- Input 32357, gap 2, face 3, scale 16, permutation 4
- Input 32357, gap 2, face 7, scale 16, permutation 4
- Input 36905, gap 2, face 3, scale 16, permutation 4

Here permutation 4 is the checked zero-based table entry `(2,0,1)` acting on
exponents. This exact identity handles the numerical degeneracy without any
strict-positivity assumption or tolerance.

## Reproduction and receipts

From this directory:

```sh
python audit.py --source ../two-attachment --output .
```

The successful reference run took 21.894 seconds. Outputs are:

- `audit.py`: the independently written, standard-library-only audit
- `audit.log`: complete successful run output
- `receipt.json`: verdict, exact counts, checked input hashes, code hash, and
  coverage-ledger hash
- `coverage_ledger.jsonl`: one record per original `(input ID, gap)`; it identifies
  the whole-orthant certificate or all eight face certificates, including exact
  target ID, scale, and permutation for every SOS face

Reference code SHA-256:
`1be003537e893c5bd514b5ab61c015612d89ad4bcbe1015954eb50fd572fb8eb`

Reference coverage-ledger SHA-256:
`6e9aae4710b84d236249ff0486edfff86115d7365b4174daf4da1f606ae9bbf7`

Reference gamma-input SHA-256:
`dbc7dc28b3c66923e3db05d0b47f00931c5d6db7d85b138fa5a7ee25a13cfed9`
