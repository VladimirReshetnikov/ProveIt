# Validation record

## Actual run

`python3 verify.py --output verification_results.json` completed successfully
in this environment. Tested Python version: **3.13.5**. The recorded result is
`status: passed`.

The run includes:

| Check family | Cases or exact result |
|---|---:|
| Small graph–host instances | 56 |
| Binary sign-code cases | 11 |
| Shortest-relation cover cases | 6 |
| Odd-prime theta calculations | 3 |
| Incidence vertices / edges | 35 / 66 |
| Distinct point pairs / pair multiplicity | 33 / 2 |
| Point-graph triangles | 22, exactly the listed faces |
| Four-cycles / six-cycles | 33 / 88 |
| Cycle-space dimension | 32 |
| Enumerated point-spin assignments | 8192 |
| One-character polynomial degree | 22 in z=(t/p)^2 |
| Sum of polynomial coefficients | 4294967296 = 2^32 |

In each small graph–host instance the script compares the primal density
and conserved-flow sum, checks moment-defect identities, bounds negative
flow mass by the one-sided error, verifies the cycle-inventory lower bound,
and tests the spectral/set-cut estimates. Forest instances verify exact
random-density equality. The Boolean shortest-relation tests also check
the rank-plus-one upper bound. `faces.json` is compared with the source
list embedded in the verifier to prevent inconsistent data copies.

Every assertion uses integer or exact Fraction arithmetic. No numerical
tolerance is used. The random test values use the fixed seed 20261007;
randomness only chooses test inputs, not a probabilistic acceptance rule.

## PDF build and quality control

The self-contained `article.tex` was compiled with pdfLaTeX, rerun to resolve
cross-references, and produced a **25-page** US Letter PDF. The final build
has no overfull boxes, undefined references, or multiply defined labels.
Ordinary underfull bibliography-line warnings do not represent missing text.
The extracted final PDF contains no unresolved `??` references.

All 25 pages were rendered with Poppler. Contact-sheet review was supplemented
by larger rendered views of the moment-defect and incidence theorem pages.
Text-span bounds were also checked programmatically: no spans extend outside
the specified safe page bounds. No clipped equations, broken glyphs, or
obscured text were observed. PDF title and authorship/status metadata are set.

## What these checks establish

They establish the reported finite calculations and consistency of the
provided checker and compiled article. They do not prove the general theorems
by exhaustion, establish worldwide priority, independently referee the
written proofs, or verify a Lean development. The typed extension has a
written proof but no dedicated typed regression test in this package.

The mathematical proofs, computational tests, and source provenance are
separate evidence layers. The paper explicitly distinguishes them.

## Integrity and rebuilding

`checksums.sha256` describes the distributed file versions. Rebuilding the
PDF with another TeX version or timestamp may change its bytes without
changing its mathematical content. The verifier's numerical output is
deterministic for the supplied source and test seed. No bit-for-bit PDF
reproducibility across different toolchains is claimed.
