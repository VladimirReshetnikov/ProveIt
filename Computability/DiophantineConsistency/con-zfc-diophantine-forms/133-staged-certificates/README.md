# Staged Pell certificates and a product-square equation for Con(ZFC)

Research prepared for Vladimir Reshetnikov and ProveIt, 24 October 2026.

Start with **report/report.pdf**. Its editable LaTeX source is
`report/report.tex`, with three generated or separately reviewed input files.
The report prints every principal quartic residual, the complete compact
formulas, their fixed-coefficient recipe, and the new mathematical arguments.

## Results

The principal direct equation is the ordinary integer polynomial

    P239(z0,...,z238) = sum(r_j(z)^2 for j=0,...,186) = 0,

with all 239 coordinates independently nonnegative. Every residual and every
collected coefficient are supplied literally. Composing the new ordinary
proof with the retained C222/ZF/ZFC calibration establishes

> ZFC proves: P239 has no nonnegative-integer zero if and only if Con(ZFC).

The direct construction encodes the numerical C222 proof calculus. It does
not simulate K215 or instantiate Jones's universal polynomial.

| Direct equation, all degree 4 | Natural variables | Quadratic rows | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Inspected incoming common-cap baseline | 261 | 194 | 31,679 | 85,566,955 |
| **New principal** | **239** | **187** | **20,015** | **84,062,635** |
| New sparse companion | 240 | 188 | 12,836 | 84,062,620 |
| New minimum-dimension companion | 237 | 185 | 69,710 | 133,499,131 |
| New small-support companion | 255 | 203 | 5,743 | 64,214,623 |
| Inspected incoming sparse-cap baseline | 292 | 225 | 6,140 | 83,933,334 |

The 239-variable equation improves every varying metric of the 261-variable
baseline. The 255-variable equation separately improves every listed size
metric of the 292-variable sparse baseline. Lower-variable equations in other
coefficient architectures already exist; this is not a global minimum claim.

The compact branch has **ten strictly positive integer unknowns** and keeps
the entire directly indexed native coefficient tuple of its parent:

| Compact evaluator | Binary operations | Exact degree |
|---|---:|---:|
| Inspected parent | 89 | 288 |
| `compact/equation_84.json` | **84** | 436 |
| `compact/equation_85.json` | **85** | 328 |

These are operation/degree tradeoffs. The compact branch retains the native
K215 calibration. It is separate from the direct C222 branch. Its four
coefficients are fixed, fully supplied integers; the largest has 592,884 bits.

## The two mathematical changes

1. **Authenticate indices in stages.** One indexed Pell certificate bounds
   all fifteen actual indices. The first five requested indices are bounded
   directly from raw polynomial rows. Their squared-error congruence recovers
   the six powers and factorial binomial. Only then do the other ten intended
   indices become bounded, allowing a second squared-error congruence to
   authenticate them. A credited dominant-denominator observation replaces
   the common digit modulus by `N*D_x`, saving three more coordinates.
2. **Double the strong Pell pair before eliminating its roots.** The identity
   `Q = 4*Delta^2*U^2*G` makes Q a multiple of the entire combined radicand G.
   Hence one product-square equation forces G to be a square. Coprimality
   then separates its factors and restores the accepted strong/auxiliary
   interfaces. The finished polynomial is

       Q*(Z^2 - R_G*V^2) + (R_G - Z^2) = 0.

An incoming eleven-integer construction already used a product-square
equation. Classical Pell doubling is also old. The new claim is this
particular doubled-pair application, its complete proof, and the exact
84/436 and 85/328 equations, not priority for those general ideas.

## Exact files

- `direct/equations/principal239/natural/equation.json`: all 187 residuals,
  the ordered 239 coordinates, domain, and exact dimensions.
- The adjacent `expanded_polynomial.json`: all 20,015 collected coefficients.
- `direct/equations/{sparse240,minimum237,small_support255}/`: the three
  alternative projections of the same raw arithmetic graph.
- Every equation directory includes its raw source, local majorant,
  index/frame/modulus metadata, projection certificate and readable text.
- `integer_companion.json`: the literal substitution defining a degree-eight
  equation in 717 unrestricted integers with the same consistency equivalence.
- `compact/equation_84.json` and `compact/equation_85.json`: complete arithmetic
  circuits, variable order, whole coefficient binding and measured costs.
- `compact/coefficients/`: all fixed numerals, encoded as gzip-compressed
  unsigned little-endian bytes. The mask `MF` already contains its source shift.
- `direct/PROOF.md`, `compact/PROOF.md`, and the report: new ordinary proofs.
- `direct/upstream/`, `compact/provenance/`: identified inherited source
  proofs, code, theorem interfaces, notices and hashes.
- `review/` and the component review files: independent mathematical reviews
  and exact finite verification receipts.

Sparse terms are encoded as `[coefficient, [indices]]`. Repeated zero-based
indices mean repeated factors; an empty list means a constant monomial.
The direct polynomial is the sum of the squares of every listed residual.
Compact circuit operations are only binary addition, subtraction and
multiplication. No coefficient port is a quantified unknown.

## Verify offline

Python 3.10 or later and its standard library suffice. No network, original
checkout, symbolic algebra system or proof assistant is required.

    python3 -B verify_release.py
    python3 -B verify_release.py --rebuild

The first command verifies the release manifest and runs the component
algebra checks in normal and optimized Python, together with the exact
printed-residual round trip. The second also rebuilds the direct graph and
all four projected equations in a temporary directory, requiring byte-for-byte
agreement of the mathematical JSON files. A receipt can be saved outside the
released folder with `--receipt /absolute/path/replay.json`.

Individual commands from this package root:

    python3 -B direct/verify.py --rebuild --receipt /tmp/direct-replay.json
    python3 -B compact/verify.py --output /tmp/compact-replay.json
    python3 -B report/generate_residuals.py --check

To build the report, use `bash build_report.sh` with a normal TeX Live
installation. PDF bytes may differ because of TeX versions and build metadata;
the exact equation JSON files are the canonical mathematical artifacts.
Rebuilding PDF or receipt files in place can invalidate the original manifest.

To evaluate the principal equation at an explicitly supplied JSON array:

    python3 -B evaluate.py point.json

To evaluate the unrestricted-integer companion, supply 717 signed coordinates:

    python3 -B evaluate.py --integer-companion point.json

These are exact evaluators, not solvers or consistency decision procedures.

## Proof and comparison boundaries

The equivalence is an ordinary mathematical result formalizable in ZFC and
composed with named inherited calibration theorems. The packet does not
provide a newly completed Lean/Rocq or encoded object-ZFC derivation. It does
not prove Con(ZFC) or assert that a solution exists. Finite checks verify
literal algebra and certificates; they do not prove unbounded number theory
by testing finitely many cases.

The inspected ProveIt snapshot is
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`, including its incoming archives.
`PROVENANCE.json` records that pin and the comparison artifacts. Claims of
improvement refer to the stated metrics and matched constructions, not an
exhaustive literature-wide simplicity theorem.

All new research, code and exposition were prepared with AI assistance.
Independent reviews mean separately performed reviews within this workflow,
not outside human endorsements. Inherited notices remain in place; new
material follows ProveIt's MIT No Attribution terms. No repository branch
or pull request was changed.
