# Validation record

This record separates compilation, exact finite computation, source inspection,
and the remaining continuous formalization. It does not designate the whole
research report as a machine-checked iPRA development.

## Checked Lean kernel

The recorded build succeeds with **Lean 4.19.0**, compiler commit
`6caaee842e94`, using only the bundled `Std` library. There are no package
dependencies in `lean/lake-manifest.json`.

A declaration-level source inventory verifies **30 named theorems and three
closed examples**: 26 theorems and all three examples in `Finite.lean`, and
four theorems in `L1Finite.lean`. `PRSyntax.lean` and `Specifications.lean`
contain compiling definitions and specification types; these are not counted
as proved continuous theorems. The exact names appear in
`metadata/theorem_status.json`.

The source modules contain no `sorry`, `admit`, or new `axiom` declarations.
`lean/validation.log` includes axiom reports for eight representative
endpoints. These use `propext` and sometimes `Quot.sound`; none of those
reports uses `Classical.choice` or `sorryAx`. This is not a claim that all
Lean kernel axioms are absent.

The compiled mathematical statements concern finite natural weights, signed
finite sums, and rational inequalities with denominators cleared. They are
semantic Lean theorems. The full continuous `Prf PRAAx` endpoints described
in the report remain formalization work.

Reproduce from the archive root after installing the toolchain pinned by
`lean/lean-toolchain`:

```sh
./lean/validate.sh
```

The script runs `lake build` followed by `lake env lean Validation.lean`.
These commands can also be run directly inside `lean/` on systems without
a POSIX shell. Compiler binaries and build caches are not bundled.

## Exact rational reference checks

`exact_checks.json` records **2,963 passing checks** using integers and
Python `fractions.Fraction` only. The total equals the sum of the recorded
group counts:

| Group | Checks |
|---|---:|
| uniform moments | 12 |
| cantor moments | 6 |
| uniform refinement | 27 |
| cantor refinement | 27 |
| conditional expectation | 12 |
| tower | 36 |
| independence | 3 |
| clipping bound | 2500 |
| kolmogorov finite | 32 |
| smoothing polynomial | 303 |
| normal enclosure | 2 |
| budgets | 3 |

The receipt includes the exact enclosures

- Gaussian normalization: `1313939/524288 ≤ Z ≤ 2628903/1048576`.
- Normal CDF at one: `882141/1048576 ≤ Phi(1) ≤ 55143/65536`.

The enclosures use positive Taylor sums, reciprocal intervals, midpoint
quadrature and explicit Gaussian tails. Outward dyadic rounding preserves
containment; its grid size is not a promise that the final interval width is
at most one grid unit. The implementation uses the interval endpoints.

The checks also reproduce the stated example sample sizes: 2,000 for the
weak law, 8,000 for the strong-law window, and 40,960,000,000,000 for the
conservative CLT example. These computations check finite examples and
implementation budgets; they are not universal analytic proofs or an iPRA
proof oracle.

Reproduce with Python 3; no third-party Python package is required:

```sh
python3 code/verify.py
```

This regenerates `validation/exact_checks.json`.

## LaTeX build receipt

`latex_build.log` records the PDF compilation. The complete editable report
is `paper/report.tex` with its included sections and bibliography. Rebuild
from the archive root with a complete pdfLaTeX installation:

```sh
python3 build_pdf.py
```

The script makes three passes and refreshes the receipt. It reports overfull
boxes, unresolved references or citations, and missing-character warnings for
review. A successful TeX exit is separate from mathematical correctness and
from visual page inspection. Any runtime-specific path printed inside a
historical compiler log is provenance, not a required portable build path.

The delivered PDF has **34 physical pages**. Its final compilation has no
overfull boxes, missing-character warnings, or unresolved citations or
references. Every page was rendered and inspected in an overview; the title,
density-realization proof, continuous-interface table, coverage table, and
reference page were also inspected at reading size. A heading stranded before
a long table was moved to the next page. `pdf_preflight.json` binds this final
inspection record to the PDF's SHA-256 hash. Visual inspection does not certify
the mathematics or replace Lean checking.

## Upstream source inspection

`metadata/source_manifest.json` pins 23 selected provider files with exact
hashes; `metadata/PROVIDERS.md` describes their actual scopes. Existing
ProveIt finite probability sources contain object-language proof types, but
their upstream package and full dependency graph were not rebuilt in this
task. Earlier and current analytic research packets are human arguments and
formalization providers, not automatically completed continuous proofs.

## Remaining formalization

The report provides the definitions, finite inequalities, precision schedules,
and object-language targets for continuous events, L0/L1/L2 names, density
realization, integration, products, conditioning and limit theorems. These
continuous bridges still need explicit quoted PR programs and the final
`Prf PRAAx` derivations. Compiling a specification record or checking a finite
example does not discharge that work.

This packaging record was prepared from the existing receipts and source
inventory; tests were not rerun merely to create the documentation.
