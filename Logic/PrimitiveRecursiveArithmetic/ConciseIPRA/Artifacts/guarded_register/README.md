# Guarded scalar registers for iPRA

Research package prepared for Vladimir Reshetnikov, 12 November 2026.

## Status of the requested result

The package gives a single-constructor numerical presentation with two
unconditional computation equations, a written whole-domain
bi-interpretability and equiconsistency proof, and a complete strict
proof checker. It achieves a small reduction against a matched scalar-I
checker in all three measured coordinates.

**It does not achieve the requested reduction below the existing compact
checker envelope. No absolute-minimality or corpus-wide improvement is
claimed.** This limitation is prominent in the report and CLAIMS.json.

| Complete program | Significant tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| Existing token comparator | 256 | 283 | 594 |
| Existing AST comparator | 263 | 276 | 580 |
| Existing byte comparator | 267 | 303 | 506 |
| Matched strict scalar-I control | 1,045 | 1,193 | 3,566 |
| Strict guarded-J checker | 1,041 | 1,181 | 3,467 |

The compact envelope (256, 276, 506) combines three different programs.
Those programs use a guarded public-language contract that differs from
the complete input validation in the two strict implementations. The
matched strict implementations use the same logical kernel, JSON
interface, scope conventions, and acceptance convention.

Measurements use CPython 3.12.14, `ast.unparse(tree) + "\n"`, UTF-8,
`ast.walk`, and significant tokens excluding ENCODING, ENDMARKER, NEWLINE,
NL, INDENT, DEDENT, and COMMENT. Python versions can affect normalization.

## Mathematical construction

Terms are variables, zero, and J(n;u.h), with u bound only in h. Every
body must be independent of its bound state or literally S(g), where
S(a) abbreviates J(a;v.0). The two computation equations are

    J(0;u.h) = S(h(0)),
    J(S(n);u.S(g)) = g(J(n;u.S(g))).

The six other primitive rules are Hyp, crossed term transport, closure
elimination, existential-closure elimination, introduction by numerical
cases, and literal-equation progress. See report.pdf, Section 2, for the
complete statement and every side condition.

The finite f/W/Z/G/C/P construction derives a selector and predecessor
using only the computation equations and equality transport. A single
literal-equation invariant then simulates initialized scalar iteration.
The report supplies explicit interpretations and internal recursion
uniqueness arguments for both composites. Both domains are whole, both
equalities are actual equality, and both isomorphisms use x=y.

The new result is a written mathematical proof using the pinned native
scalar/iPRA theorem upstream. It is not a new Lean or Rocq formalization.
The ordinary first-order realization explicitly includes numerical
coverage and (0=1) -> bottom; their native counterparts are derived.

## Contents

- `report.tex`, `report.pdf`: complete mathematical report, including
  all rules, arithmetic bootstrap, iterator compiler, interpretations,
  full logical macro interface, comparison, and the primary checker listing.
- `CLAIMS.json`: machine-readable claim boundary.
- `reproduce.py`: offline integrity, measurement, corpus, and proof-check
  reproduction; optional PDF build and manifest verification.
- `code/checker_j.py`: complete strict guarded-J checker.
- `code/checker_i.py`: matched strict scalar-I control.
- `code/README.txt`: exact certificate syntax and checking conventions.
- `code/reproduce.py`, `code/symbolic.py`: untrusted test and certificate
  producers; no producer belongs to the measured checker.
- `code/certificates/`: valid, invalid, and parameterized symbolic proofs.
- `code/evidence.json`, `code/symbolic_evidence.json`,
  `code/comparison.json`, `code/checker_comparison.diff`: reproducible results.
- `reference/`: three exact frozen comparison programs, upstream index,
  two relevant Lean source files, and the upstream license. The two Lean
  files are reference excerpts from a larger importing project, not a
  standalone Lean project. The upstream Lean build was not rerun here.
- `evidence/`: source provenance, full research-tree inventory, the 442
  retrieved small Python blobs, and all their measurements. The retrieval
  threshold was 1,500 source bytes; this is not an unrestricted global
  lower-bound proof.
- `review/final_guarded_review.md`: independent same-run assistant review
  of the final theory and code; this is not external human peer review.
- `MANIFEST.json`: SHA-256 hashes of all delivered files other than itself.

## Reproduction

From this directory, use Python 3.12.14 for exact metric reproduction:

```sh
python3 reproduce.py
python3 reproduce.py --manifest
```

The first command verifies all 442 retrieved Git blob hashes, remeasures
their recorded metrics and the five comparison rows, runs 108 subprocess
checks (ordinary and optimized Python), and regenerates twelve symbolic
equational certificates. It uses only Python's standard library and
requires no network access. All process and symbolic checks must succeed.

The final closed suite has 48 accepted and 60 rejected cases, with zero
mismatches. Each symbolic proof is checked with no hypotheses and its
declared arbitrary numerical parameters. The CLI itself accepts only
closed goals. A closed Q-closure proof for W(S(y))=y also exercises the CLI.

To check a single certificate:

```sh
python3 code/checker_j.py < code/certificates/j/positive/load_state_dependent.json
python3 -O code/checker_j.py < code/certificates/j/positive/load_state_dependent.json
```

Acceptance means exit code zero and exactly `ACCEPT` followed by a newline.
Exceptions and resource exhaustion are rejection. Runtime checks do not
use Python assertions, so `-O` does not disable them.

To rebuild the PDF with a normally configured TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively use `python3 reproduce.py --pdf`. The source uses standard
LaTeX packages and Latin Modern fonts. PDF metadata and TeX installation
differences can change PDF bytes without changing its mathematical content.
`--manifest` checks the delivered files before regenerating evidence or PDF;
an intentional edit or rebuild can therefore make a later manifest check
fail, as expected.

## Provenance and assurance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot: `5c6c2d8d68da11f89cf2937cf7aca3b85805fd41`.

Scope: `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`.

The code tests and symbolic certificates establish the reported finite
checks. They do not establish the general iterator translation, internal
composite identities, or checker correctness as machine-verified theorems.
Those arguments are given in the report and were independently reviewed
during this run. No upstream file or repository was modified.

The copied upstream material is distributed under the MIT No Attribution
License reproduced in `reference/LICENSE.txt`.
