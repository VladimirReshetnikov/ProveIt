# Replacing primitive labels with norm tests

This archive proposes and proves a local mathematical simplification of the
readable Lean proof of RH and GRH for Dirichlet L-functions in ProveIt.

**Read `order_tests.pdf` first.** Its complete, self-contained LaTeX source is
`order_tests.tex`.

## Main result

Replace the primitive-polynomial witness in the good-type projector by explicit
norm power tests and one subgroup exclusion. The replacement preserves every
audited arithmetic property of that witness. It has an exact elementary count;
for the existing source parameters, the count exceeds `q^r/(4r)`.

The bad-type counting condition becomes `f >= 4 r L` instead of
`f >= 2 r (2 r log q + 1) L`. For the source caller, `L = 9 log b`.
A finite union bound already proves the density needed by the Lean application,
so formalization does not need the stronger exact count or a CRT counting proof.

The report uses `T` for `P.q₂ D.towerExp`. The executable checks and auxiliary
migration audit call the same integer `N`. It is not the source's auxiliary
level `N`. The report's `B` means `q^(r/3)`.

## Status and scope

- General finite-field theorem: complete mathematical proof in the report.
- Exact examples and boundary counterexamples: checked with integer/rational
  arithmetic, including an independent enumeration of all monic cubics over F19.
- Source interfaces: read and mapped to the proposed hypotheses.
- Existing proposals: all five directories audited, including all 42 text files;
  all 47 blobs (including five PDFs) verified against the pinned revision.
- New Lean implementation: **not implemented or compiled**. No kernel replay or
  complete theorem rebuild is claimed for this proposal.
- No claim is made about global literature priority, a new independent proof of
  RH, a numerical speedup, or a reduction of a global tower exponent.

The projector definition must change coherently throughout the build. The new
count cannot be applied to the unchanged primitive-only projector. The rank-one
`X - 1` branch and the `IsCommonRootPower` output structure are retained.

## Contents

| File | Purpose |
| --- | --- |
| `order_tests.pdf` | Main report: theorem, proofs, implementation plan, novelty audit, examples and limitations. |
| `order_tests.tex` | Complete LaTeX source, with immutable repository citations. |
| `audit/lean_migration.md` | Detailed audit of primitive-label consumers and migration boundaries. |
| `audit/existing_proposals.md` | Mechanism-by-mechanism nonduplication audit. |
| `audit/existing_proposals_manifest.json` | Inventory and Git blobs of all 47 prior proposal files. |
| `audit/source_manifest.json` | Source-file hashes and exact declaration anchors. |
| `audit/source_anchors.tsv` | Human-readable source/declaration/link index. |
| `code/check_order_tests.py` | Direct cyclic checks, quotient-field cubic enumeration and counterexamples. |
| `code/check_by_orders.py` | Independent counts by summing totients over qualifying element orders. |
| `code/check_source_snapshot.py` | Read-only check against a pinned repository checkout. |
| `checks/*.json` | Saved exact-check outputs, with exhaustive versus sampled scope recorded. |
| `checks/guide_source_check.txt` | Result of running the guide's own source-index checker. |
| `checks/pdf_quality.json` | PDF compilation, reference and layout verification summary. |
| `METADATA.json` | Revision, report date, scope and verification status. |
| `MANIFEST.sha256` | Checksums of the deliverable files. |

The original proof source and the prior proposals are not redistributed here;
their immutable links and hashes identify the audited inputs.

## Reproduce the arithmetic checks

Python 3.10 or newer is sufficient; no third-party package is required.
Run from the extracted archive directory:

```sh
python3 code/check_order_tests.py --output checks/exact_checks.json
python3 code/check_by_orders.py --output checks/order_checks.json
```

The first script exhausts the root count in its five rank-three cases and
enumerates all 6,859 monic cubics over F19 using independently implemented field
arithmetic. Structural tests in the larger cases use deterministic samples;
the saved output identifies them. The rank-nine case is not an exhaustive
element enumeration.

The second script independently obtains the counts by summing `phi(d)` over
element orders `d`. Its `power` mode is the recommended predicate. Its `full`
and `threshold` modes compare neighboring predicates as auxiliary checks.
Neither is a separate proposal. The repository-shaped modulus check evaluates
the rational density only, not a construction of an actual residue field.

These finite tests do not prove the general theorem. The complete proof is in
the report.

## Reproduce the source audit

Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt)

Revision: `89d12dd40424f1217fd818d84877b3da52396a3b`

Obtain a checkout at that revision containing the `Lean`, `docs/guide`, and
`docs/proposals` directories under `Analysis/GeneralizedRiemannHypothesis`, then:

```sh
python3 code/check_source_snapshot.py /path/to/ProveIt
```

This checks the commit, the selected source files and anchors, and all prior
proposal blobs. To repeat the guide's broader source-index check, run from
`Analysis/GeneralizedRiemannHypothesis` in that checkout:

```sh
python3 docs/guide/check_sources.py Lean/grh
```

The latter reported 253 declaration anchors and 83 Git blobs matching.

## Build the PDF

A standard TeX Live installation with the packages named in the preamble is
sufficient. Run `pdflatex` until cross-references stabilize (three passes for a
clean build with this table of contents):

```sh
pdflatex -halt-on-error order_tests.tex
pdflatex -halt-on-error order_tests.tex
pdflatex -halt-on-error order_tests.tex
```

The supplied PDF was rendered and visually checked after compilation.

## Independent verification of the starting proof

The report cites [Andrew Sutherland's verification records](https://math.mit.edu/~drew/shortgrh/)
for the original shorter proof. Those external results are separate from the
checks performed for this proposed refactor.

Prepared 27 November 2026 (America/Los_Angeles).
