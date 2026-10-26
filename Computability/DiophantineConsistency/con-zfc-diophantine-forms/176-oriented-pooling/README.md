# Joint arithmetic certificates for ZFC consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.
AI-assisted mathematical research with separate internal reviews.

## Result

This package supplies a complete ordinary integer polynomial in **90
unrestricted integer variables, of exact degree 32,768**, together with
lower-degree alternatives in **121 variables at degree 16** and **147
variables at degree 8**. The equations are given by explicit finite
arithmetic circuits with fixed literal integer constants.

For every delivered equation, the ordinary proof composed with the named
inherited calibration establishes:

```text
ZFC proves:  there is no integer zero  if and only if  Con(ZFC).
```

Here `Con(ZFC)` is syntactic consistency of the effective ZFC presentation
identified by that calibration. The proof does not assume or decide
consistency. Start with **[report/report.pdf](report/report.pdf)**; the
complete editable LaTeX source and generated appendices are alongside it.

| Integer variables | Exact degree | Residuals | Live binary operations |
|---:|---:|---:|---:|
| 194 | 6 | 131 | 2,682 |
| 147 | 8 | 84 | 2,559 |
| 135 | 12 | 72 | 2,498 |
| **121** | **16** | **58** | **2,453** |
| 115 | 24 | 52 | 2,438 |
| 111 | 32 | 48 | 2,429 |
| 105 | 64 | 42 | 2,495 |
| 97 | 256 | 34 | 2,398 |
| **90** | **32,768** | **27** | **2,306** |

These are measured improvements within the direct numerical proof-calculus
branch. For example, report 152's corresponding direct profiles include
153 variables at degree 8, 125 at degree 16, and 94 at degree 65,540.
The repository also contains constructions with fewer variables using
different coefficient architectures. **No global minimum, dominance of
every other construction, or literature-wide novelty is claimed.**

## The arithmetic contribution

The new joint certificate authenticates both the signs and indices of
fourteen Pell pairs and seventeen exact-power requests at five bases.
It makes one rational sum an integer, then expresses it as a sum of
bounded errors whose terms have a common sign and whose absolute total
is below one. The polynomial obtained by clearing its nonzero
denominators forces all those errors to vanish.

The proof handles zero bases before the source's sign bootstrap. It uses
bounded classified Pell indices before identifying them with the
requested indices, avoiding a circular application of the power lemma.
This replaces eleven private coordinates of the parent by one and gives
the **206-variable degree-26 joint seed** in
`equations/P206_joint.json`. The final 90-variable polynomial is its
certified monic projection. A 207-variable degree-24 intermediate and
partitions of the power requests provide the other seeds and tradeoffs.

Source 158 developed same-base pooling. Source 168 combined consecutive
bases and suggested base weights for aligning signs across larger pools.
Source 152 developed the acyclic monic-substitution method used here.
The contribution of this package is the complete simultaneous index-and-
power argument, its exact application to the current source, and the
emitted equations and certified reductions. The construction directly
encodes C222; it does not specialize Jones's universal polynomial or
encode a K215 run.

## Complete equation definitions

The files `higher_degree/equations/integer*_degree*.json` contain the
final polynomials. Their nodes are integer literals, independent variable
leaves, addition, subtraction, and multiplication. `output` identifies
the single polynomial; `residual_roots` identifies the polynomials whose
squares are summed. **Gate values are expression abbreviations, not
additional quantified variables.** There is no variable exponent,
unspecified coefficient, factorial primitive, or arithmetic oracle.

Every listed final circuit has maximum absolute literal constant 384.
This is not the height of the expanded polynomial. The files contain
checked conservative bounds on expanded coefficient height; exact
expanded support and coefficient maxima are not claimed. Operation counts
refer to the emitted circuits with sharing, not globally optimal circuits.

## Verify and evaluate offline

Python 3.10 or newer and its standard library suffice for the finite checks:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild --receipt /tmp/conzfc-verification.json
```

The root verifier runs the source, interface, arithmetic, circuit, and
elimination checks. The rebuild option also replays the specified
construction pipeline. Receipts from actual successful runs are retained
under `verification/` and `higher_degree/`.

The elimination checker imports neither its producer nor its search code.
It authenticates every pivot row and substitution, checks exact degree by
nonzero highest homogeneous coefficients, and checks genuine occurrence
of every variable by nonzero partial derivatives. Its nine final circuits
pass 45 deliberate corruption controls and byte-exact reconstruction.
These finite checks complement the unbounded proofs; they do not establish
consistency or replace the inherited semantic theorems.

To evaluate the degree-16 equation at a supplied list of exactly 121 integers:

```sh
python3 -B higher_degree/evaluate.py \
  higher_degree/equations/integer121_degree16.json tuple.json
```

Add `--residuals` to display its residual values. Evaluation is not a root
search or a consistency decision procedure. High-degree profiles can
produce very large integers even at small inputs.

## Rebuild the article

The delivered `.tex` files include all generated mathematical appendices.
Run twice with standard TeX Live packages:

```sh
cd report
pdflatex -no-shell-escape report.tex
pdflatex -no-shell-escape report.tex
```

PDF metadata can vary across TeX installations. The literal circuit data,
source hashes, parsed equation appendices, and finite certificates provide
the stable mathematical definitions.

## File map

| Location | Contents |
|---|---|
| `report/` | Complete article, compiled PDF, and LaTeX appendices containing source ports, retained rows, and elimination specifications. |
| `equations/` | Joint seed, oriented-power intermediate, partitions, exact circuits, source bindings, and metrics. |
| `higher_degree/` | Nine final lower-arity equations, frozen pivots, source circuits, builder, independent verifier, evaluator, proofs, and receipts. |
| `code/` | Seed builders, independently implemented source/interface and circuit checks, arithmetic fixtures, and report exporters/checkers. |
| `proofs/` | Full arithmetic arguments, internal independent reviews, and the obstruction to identifying the radix with the CRT modulus. |
| `source/` | Exact parent equation, unmodified incoming parent archive, and inherited anchor proof sources. |
| `verification/` | Actual replay and verification receipts. |
| `provenance/SOURCES.json` | Pinned repository paths and byte-exact retained source identities. |
| `MANIFEST.sha256` | SHA-256 checksums of every other delivered file. |
| `INTEGRATION.md` | Suggested additive ProveIt intake and comparison entry. |

## Provenance and proof boundary

The comparison snapshot is
`315154b670d7bdb1679554734e417410c9b8187b`.
The exact parent is `algebra/equation216.json` inside the incoming archive
`ConZFC_Pooled_Projection_2026-10-25.zip`. Its equation-file SHA-256 is:

```text
a91308bd0c82182ea15080763cb23cb4fa0aa45a812eabb7a6cbcd21c0b95a06
```

The proof composes the parent arithmetic decoding with the inherited
declarations `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
The new work is an ordinary mathematical proof formalizable in ZFC plus
exact finite verification. It is **not** a newly compiled end-to-end
Lean/Rocq development or an emitted object-language ZFC proof. Separate
reviews are AI-assisted internal checks, not external human peer review.
No existing repository files need to be replaced to incorporate this work.

The complete single-file LaTeX version is `report/report_standalone.tex`.
To check archive integrity independently of the mathematical verifier, run
`sha256sum --check MANIFEST.sha256` from the extracted package root.
