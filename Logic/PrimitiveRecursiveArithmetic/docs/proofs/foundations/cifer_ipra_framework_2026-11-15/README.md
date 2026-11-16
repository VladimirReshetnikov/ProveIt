# CIFER: Certified Interfaces, Finite Evidence, and Residualized Proof Compilation for iPRA

Research package prepared on 15 November 2026 (America/Los Angeles).

## Main result

CIFER consolidates the recurring finite-interface ideas in the ProveIt iPRA research packets and adds a residual proof-compilation layer. A query-specialized finite proof graph compiles to an actual object-theory target of the form

```text
B_1, ..., B_r, Gamma |- [PRAAx] Goal
```

where `B_1, ..., B_r` are exactly the reachable unresolved producer boundaries after dependency normalization. Supplying embedded proofs of those formulas closes the theorem by `Prf.trans`. When a producer is genuinely unavailable, the package returns a precise conditional theorem instead of hiding the gap.

The report develops human-readable proofs of:

- residual graph compilation and boundary discharge;
- fixed-formula Boolean reflection;
- least bounded search and complete enumeration;
- capped cyclic demand closure;
- finite-trace reflection with quantifier-free induction;
- backward viability and least finite paths;
- stable-observer and diameter elimination;
- finite-horizon Cauchy coherence without infinite branch choice;
- height-bound/complete-list conversion; and
- a closed rational bisection framework for the inverse of `y^3 + y`.

It applies the framework to the recurring difficulties in Faltings/Siegel packets, Mordell-Weil descent, exact rotation axes and spectral branches, represented analysis, topology, and effective prime distribution.

## Start here

- `paper/cifer_ipra_framework.pdf` - 70-page research report.
- `paper/cifer_ipra_framework.tex` - main LaTeX source.
- `paper/sections/` - all report sections.
- `lean/FORMALIZATION_PLAN.md` - dependency-ordered Lean completion roadmap.
- `lean/CIFER/ObjectCompiler.lean` - residual object-proof composition core against the current `ConciseIPRA` API.
- `code/cifer.py` - exact finite reference algorithms.
- `examples/demo.json` - generated residual, demand, viability, and bisection example.
- `THEOREM_LEDGER.md` - claim/status ledger.
- `STATUS.md` - exact verification and non-verification status.

## Package layout

| Path | Purpose |
| --- | --- |
| `paper/` | LaTeX source and compiled report |
| `lean/` | Lean 4 integration outline and formalization plan |
| `code/` | Standard-library-only Python reference implementation and tests |
| `examples/` | Machine-readable example outputs and graph specifications |
| `metadata/` | Framework schema, difficulty matrix, and source audit |
| `validation/` | Test output, build log, PDF preflight, and QA record |
| `build.sh` | Rebuild tests, examples, PDF, validation, and checksums |
| `MANIFEST.sha256` | Integrity hashes for delivered files |

## Reproduce the executable checks

Requires Python 3.10 or later. No third-party Python package is used.

```bash
cd code
python3 -m unittest -v test_cifer.py
python3 demo.py
```

The current package records 13 passing tests. These verify the finite reference algorithms; they are not a proof checker for iPRA.

## Rebuild the PDF

A standard TeX Live installation with `latexmk`, Latin Modern, AMS packages, `longtable`, `listings`, `hyperref`, and `cleveref` is sufficient.

```bash
bash build.sh
```

The report was compiled, preflighted, rendered page by page at 120 DPI, and visually inspected. It is 70 letter-sized pages and contains no encryption, forms, JavaScript, or scanned-only pages.

## Lean status

The source targets the inspected ProveIt declarations:

- `PR`, `PTm`, `PRAAx`, and `PRA.qfInd`;
- `Prf` and `Prf.trans`;
- `pra_iff_native`;
- Lean toolchain `leanprover/lean4:v4.32.0`.

The artifact runtime did not provide Lean or Lake. Therefore:

- no supplied Lean file was elaborated here;
- no new theorem is claimed kernel-checked;
- the files contain no `sorry` or newly declared axiom;
- unproved completion targets are comments, data interfaces, or documented milestones, not admitted theorems.

The first decisive formal endpoint should be a closed cubic inverse theorem whose type is literally an empty-context `Prf PRAAx` derivation, followed by export through `pra_iff_native`.

## Source audit

The ProveIt repository was inspected at public `main`, current head recorded as:

```text
8649990597d73657bde480b6c389de7f85bc0cb0
```

See `metadata/source_audit.json` and the report's provenance section for inspected paths. No upstream repository file was modified.
