# Oriented power pooling and polynomial root centering

Research prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.
AI-assisted development with separately assigned mathematical and finite-algebra reviews.

Start with [the report](report/ConZFC_Oriented_Powers_2026-10-25.pdf).
Its complete editable LaTeX source is
[beside it](report/ConZFC_Oriented_Powers_2026-10-25.tex), with all required
inputs included. The appendices print the entire frozen parent equation,
all projection certificates, and the compact companion's fixed coefficient
recipe.

## Completed equations

For every delivered equation, the ordinary proof composed with the
specifically identified inherited calibration establishes in ZFC:

\[
\text{the equation has no solution in its stated domain}
\quad\Longleftrightarrow\quad\operatorname{Con}(\mathrm{ZFC}).
\]

Here consistency is syntactic consistency for the effective ZFC
presentation named in the inherited calibration. The result establishes
an equivalence; it does not establish consistency or unsolvability separately.
All coefficients are fixed independently of that question.

### Direct equations over unrestricted integers

Every coordinate in this table ranges independently over all integers.
Each literal circuit defines a sum of squares of the indicated number
of residual polynomials.

| Variables | Exact degree | Residuals | Binary operations | Coefficient bound exponent H |
|---:|---:|---:|---:|---:|
| 137 | 12 | 74 | 2,548 | 55 |
| 121 | 16 | 58 | 2,502 | 84 |
| 118 | 22 | 55 | 2,523 | 58 |
| 111 | 32 | 48 | 2,502 | 107 |
| 106 | 38 | 43 | 2,457 | 147 |
| 104 | 64 | 41 | 2,451 | 223 |
| 99 | 128 | 36 | 2,483 | 556 |
| 94 | 256 | 31 | 2,468 | 788 |
| 93 | 328 | 30 | 2,448 | 788 |
| 89 | 32,768 | 26 | 2,453 | 82,436 |
| 88 | 65,540 | 25 | 2,450 | 164,875 |
| **87** | **8,388,612** | **24** | **2,447** | **21,104,473** |

Every expanded coefficient has absolute value **strictly below 2^H**.
These are proved upper bounds, not exact coefficient heights. Every literal
integer constant in the supplied direct circuits has absolute value at most
256; this is a different measure from the expanded coefficient size.
Squares and multiplications by constants count as binary operations.
Operation counts are not bit-complexity bounds.

The 87-variable equation has the smallest dimension in this delivered
direct family and a much higher degree. The **137-variable degree-12**,
**121-variable degree-16**, **111-variable degree-32**, and
**99-variable degree-128** profiles give substantially smaller degree
budgets. This packet presents measured tradeoffs rather than a global
simplicity minimum. The literal definitions are in [equations/](equations/),
with one exact unit-pivot certificate per profile in
[certificates/](certificates/).

### Compact companions over strictly positive integers

These have a different domain and retain four large fixed coefficient ports.

| Compact circuit | Strictly positive variables | Exact degree | Binary operations |
|---|---:|---:|---:|
| Inverse correction with unsquared trace | 10 | 232 | 85 |
| Square transport with unsquared trace | 10 | 232 | 85 |
| **Polynomial root center** | **10** | **224** | **90** |

The largest fixed port has 592,884 bits. All four numerical payloads and
their finite reconstruction from a 436-character seed are supplied.
The [compact proof and artifacts](compact/README_COMPACT.md) keep the
positive domain explicit; no ten-variable unrestricted-integer result is
claimed by these companions.

## What changes mathematically

The direct construction combines seventeen signed Pell power requests at
five bases into a rational-integrality certificate. Multiplication by the
base gives all active squared-error terms a common sign, even when the
bases have different signs. The local theorem allows temporary zero bases;
the remaining arithmetic equations exclude them in a noncircular bootstrap.
The all-five version removes nine certificate coordinates from the
225-variable parent. Two other partitions preserve useful degree tradeoffs.
Explicit acyclic unit pivots then eliminate further coordinates, with
integral reconstruction maps and exact finite certificates.

The compact construction combines the existing inverse-Lucas correction
and unsquared trace. The inverse correction resolves the earlier open
square-transport issue. The stronger signed bound permits the root center
`A U E V`; a cofinal positive Pell lift proves completeness, and a free
polynomial identity certifies the degree-224 cancellation.

The immediate source is [158-pooled-powers][s158].
[168-reciprocal-pooling][s168] already supplied two-base reciprocal pooling
and suggested oriented weights; this packet completes the five-base theorem
and its actual instances. Acyclic monic elimination and the matched
higher-degree comparisons are credited to [152-lucas-corrections][s152].
The compact ingredients are credited to [163-trace-radical][s163] and
[164-unsquared-factors-linear-selectors][s164].
[167-integral-projection][s167] supplies the retained historical calibration
audit. The source snapshot and precise boundaries are recorded in
[SOURCES.json](SOURCES.json) and [NOTICE.md](NOTICE.md).

## Replay and article build

Python 3.10 or later and its standard library suffice for the exact replay.
From this package's root:

```sh
python3 -B verify.py
python3 -O -B verify.py
python3 -B code/build_projections.py --check
```

The root checker covers all twelve direct profiles, including the
87-variable degree-8,388,612 profile, and the three compact circuits.
It verifies the literal pooling identities, unit pivots, acyclicity, circuit
blocks, complete source-row partition, degrees, coefficient bounds and
actual dependence on every input. Deliberately corrupted artifacts are
rejected. These commands do not search for a Diophantine zero.

The supplied evaluator reads the exact declared input order from its circuit.
For example, these commands print that order and perform a modular smoke
check at the all-zero tuple:

```sh
python3 -B code/evaluate.py --profile integer111_degree32 --variables
python3 -B code/evaluate.py --profile integer111_degree32 --zero --modulus 1000000007
```

Use `--tuple inputs.json` for a JSON array of integer arguments and omit
`--modulus` for exact integer evaluation. `--residuals` also prints the
summands before squaring. A modular zero is not an integer solution. The
high-degree profiles can produce very large values even at small inputs.

For a focused check of the compact supplement:

```sh
python3 -B compact/build_compact.py --check
python3 -B compact/verify_compact.py
```

With an ordinary TeX Live installation, rebuild the article from report/:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error ConZFC_Oriented_Powers_2026-10-25.tex
pdflatex -interaction=nonstopmode -halt-on-error ConZFC_Oriented_Powers_2026-10-25.tex
```

Exact mathematical definitions are the frozen coefficients, literal
circuits, source equations and certificates. PDF metadata and bytes can
vary with the TeX installation. Finite checks are not a replacement for
the unbounded number-theoretic proof.

## Logical and historical scope

The direct branch encodes the numerical C222 proof calculus. It does not
use K215 simulation, Jones's universal polynomial, or Sun's integer-domain
reduction. The compact positive branch retains its separate native/K215
ancestry. The ordinary consistency corollaries compose with explicitly named
inherited calibration theorems. The whole semantic calibration must not be
described as a newly implemented primitive-recursive proof translator.

The full historical arithmetic and Lean import closure is **not bundled
or freshly compiled by this packet**. Selected source proofs, the literal
parent, source identities and the new exact certificates are included.
Historical replay statements inside retained source documents belong to
those documents' original contexts; editorial wrappers identify them.
The new proofs and exact finite checks do not constitute a new end-to-end
Lean/Rocq theorem or an emitted object-language ZFC derivation. Separate
AI-assisted reviews are not external human peer review.

No worldwide novelty priority or global simplicity minimum is asserted.
See [INTEGRATION.md](INTEGRATION.md) for additive repository intake.

[s158]: https://github.com/VladimirReshetnikov/ProveIt/tree/0c48d332df6b0e50d4e5b6251c531898f5682c72/Computability/DiophantineConsistency/con-zfc-diophantine-forms/158-pooled-powers
[s168]: https://github.com/VladimirReshetnikov/ProveIt/tree/0c48d332df6b0e50d4e5b6251c531898f5682c72/Computability/DiophantineConsistency/con-zfc-diophantine-forms/168-reciprocal-pooling
[s152]: https://github.com/VladimirReshetnikov/ProveIt/tree/0c48d332df6b0e50d4e5b6251c531898f5682c72/Computability/DiophantineConsistency/con-zfc-diophantine-forms/152-lucas-corrections
[s163]: https://github.com/VladimirReshetnikov/ProveIt/tree/0c48d332df6b0e50d4e5b6251c531898f5682c72/Computability/DiophantineConsistency/con-zfc-diophantine-forms/163-trace-radical
[s164]: https://github.com/VladimirReshetnikov/ProveIt/tree/0c48d332df6b0e50d4e5b6251c531898f5682c72/Computability/DiophantineConsistency/con-zfc-diophantine-forms/164-unsquared-factors-linear-selectors
[s167]: https://github.com/VladimirReshetnikov/ProveIt/tree/0c48d332df6b0e50d4e5b6251c531898f5682c72/Computability/DiophantineConsistency/con-zfc-diophantine-forms/167-integral-projection
