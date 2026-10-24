# Weighted cones and rational Pell descent

Research contribution prepared for Vladimir Reshetnikov and ProveIt, 23 October 2026.

**Two structural reductions yield four explicit Diophantine presentations of syntactic ZFC consistency.** The equations have solutions exactly when the repository's fixed ZFC proof calculus has a finite refutation, by composition with the identified inherited calibration theorems. Consequently, their lack of solutions is equivalent to `Con(ZFC)` in ordinary mathematics formalizable in ZFC.

Start with **`report/report.pdf`**; its complete source is **`report/report.tex`**.

## Results and exact comparison

| Artifact | Quantified domain | Variables | Exact degree | Structure | Inspected prior point |
|---|---|---:|---:|---|---|
| `integer/quartic38.json` | Unrestricted integers | 38 | 4 | Sum of 25 residual squares | 41 integers, degree 4 |
| `integer/sextic32.json` | Unrestricted integers | 32 | 6 | Sum of 19 residual squares | 35 integers, degree 6 |
| `integer/octic27.json` | Unrestricted integers | 27 | 8 | Sum of 14 residual squares | 30 integers, degree 8 |
| `positive/equation.json` | Strictly positive integers | 12 | 82 | Three-factor product minus one | 12 positives, degree 118 |

The positive evaluator uses **102 live binary operations: 57 multiplications, 26 additions, and 19 subtractions**, compared with 104 in the inspected parent. Squares and multiplication by fixed numerals are charged; fixed leaves and register reuse are free. Register names are polynomial abbreviations, not quantified unknowns.

The cone family uses six coefficient payloads totaling **881,696 raw bytes / 40,511 gzip bytes**. This is larger than its four-port parent, which occupies 532,479 raw bytes. The positive family retains its parent's complete four-port tuple of **295,388 raw bytes**. The two families use different coherent native tuples; their ports must not be mixed.

These are improvements in several complexity measures, not a proof of global minimality. They do not improve the separate nine-natural-variable or ten-integer-variable bounds. The complete endpoints retain the existing K215/native calibration, although the two new mechanisms are independent mathematical tools. No Jones universal equation is needed for these reductions.

## New ideas

1. **Normalize canonical anchors, then combine positivity guards.** The cone
   `2xy + 2xz + 2yz - x^2 - y^2 - z^2 > 0`
   forces three coordinates to share a strict sign. Every canonical native cell has a fixed large leading digit. This allows fixed weights to put the three relevant coordinates in a common interval `[L,2L]`, where the cone is positive. A single three-variable positive-value representation then replaces two such representations, saving three unrestricted integer variables. The initial reduction preserves existence through canonical witnesses; it does not preserve every old solution. The subsequent sextic and octic eliminations are genuine integer zero-set bijections.

2. **Use Pell descent to recover integrality after elimination.** If `Q>1` is an integer, `V` is an integer, and rational `y` satisfies `Q V^2 - (Q-1)y^2 = 1`, then `y` is an integer. An inverse Pell step preserves its reduced denominator while strictly decreasing the nonzero integer `|V|`. This makes a two-witness norm merger sound without extra coprimality constraints, lowering the twelve-positive equation's exact degree from 118 to 82.

## Reproduction

Use Python 3.10 or later, **standard library only**. No network or proof search is required.

```sh
python3 verify.py
```

The root driver authenticates the packaged file manifest and source pins, independently compares the paper's 25 displayed quartic residuals with the literal packet, and runs both component audits in isolated temporary copies. It writes `VERIFICATION.json` in the extracted root. A nonzero exit status indicates failure. The original equation and coefficient files remain unchanged.

Both component checks were also run successfully with Python assertions disabled. To reproduce that mode:

```sh
python3 -O verify.py
```

Supported component entrypoints, if working on a single family:

```sh
python3 integer/reproduce.py
python3 positive/verify.py
```

The integer command regenerates its packets, expansion certificates, coefficient payloads, and receipt. The positive command checks the circuit against an independent exact specification and rebuilds the native tuple in a temporary copy. To regenerate only the positive circuit, run `python3 positive/build.py`.

To compile the paper, run twice from `report/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The document uses ordinary TeX Live packages. The delivered PDF was visually checked after compilation. PDF timestamps and gzip header differences across Python platforms are not mathematical coefficient differences; the audits compare uncompressed coefficient bytes where appropriate.

## Proof and verification boundary

The new cone argument, canonical interval bounds, polynomial elimination maps, rational Pell descent, integer recovery, positive lift, and exact degree proofs are written out. Separate AI-assisted internal reviews examine the universal arguments and exceptional branches. Exact finite checks establish the algebraic identities, variable and operation counts, coefficient binding, and source authenticity.

The final semantic link to finite ZFC refutations uses the retained immediate native/Pell source interfaces and their transitive references at the pinned repository snapshot. This archive is **not** a new end-to-end Lean/Rocq certificate, a complete copy of every transitive semantic dependency, or a checked derivation in the encoded object-language ZFC calculus. It does not decide whether ZFC is consistent. Finite test results are not offered as proofs of universal semantic claims.

The comparison snapshot is:

`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`

The relevant previous packages are 61 (positive degree 118), 62 (integer degree-six/eight companions), and 64 (integer quartic). Their readmes and the repository's current status documents are retained under `review/upstream/`, with exact Git-blob and SHA256 identities in `review/SOURCE_PINS.json`. Component manifests retain their own exact source pins, including the older compact-tuple dependencies.

## Layout

- `report/`: complete paper, source and PDF.
- `integer/`: three literal equations, exact expansion certificates, full new proof/review, six numerical coefficient payloads, source pins and authentic upstream files.
- `positive/`: literal twelve-variable circuit, independent checker, full new proof/review, four numerical payloads, native reconstruction/audit, source proofs and provenance.
- `review/`: pinned comparison and formalization-status material.
- `verify.py`: root audit and paper-to-packet transcription check.
- `METRICS.json`: machine-readable claim and cost summary.
- `MANIFEST.sha256`: file integrity manifest. The manifest itself and the generated root `VERIFICATION.json` are intentionally excluded from its entries.
- `LICENSE`, `NOTICE.md`: contribution terms and inherited attribution.

For repository incorporation, add this directory as a new proposal. Its internal paths are relative, and the reproduced equations do not depend on an installation path. Historical files under `upstream/` preserve their original text and may refer to their original repository locations; the supported entrypoints are the new drivers listed above.
