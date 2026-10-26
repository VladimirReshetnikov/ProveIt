# Two Routes to Smaller Diophantine Consistency Equations

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

This package gives two explicit ordinary Diophantine constructions. With
the identified inherited refutation calibrations, the ordinary proofs
establish in ZFC that each equation has no solution in its stated domain
if and only if Con(ZFC).

## Principal results

| Equation | Domain | Variables | Exact degree | Live binary operations |
|---|---|---:|---:|---:|
| D83, principal direct equation | All integers | 83 | 624 | 1,789 |
| P190, compact positive equation | Strictly positive integers | 10 | 190 | 118 |
| P202, cheaper companion | Strictly positive integers | 10 | 202 | 99 |

**D83 is the recommended contribution when avoiding the K215/native
coefficient route is the priority.** It is the sum of 31 explicitly
specified residual squares. Its circuit uses integer literals of absolute
value at most 64 in the preferred factored evaluator. Every expanded coefficient has absolute value strictly
less than 2^1568; this is a rigorous upper bound, not its exact expanded
height. Every one of the 83 independent inputs actually occurs.

The new direct mechanism uses the quotient of a large Pell solution as
the modular center witness. A local permutation of Pell indices supplies
the required residue class and arbitrarily large witnesses. A signed
frame permits a sextic source, and 144 acyclic unit definitions reduce it
to D83. Two exact factorizations of shared sums and squares then reduce
the evaluator from 2,939 to 1,789 operations without changing the polynomial.
This route uses a direct C222 proof calculus, with the inherited
C222-to-ZF and ZF-to-ZFC refutation equivalences. It uses neither K215
simulation nor Jones's universal polynomial.

**P190 is preferable when a small number of positive variables and a
short evaluation circuit are the priority.** Its new positive transport
weight is L = A U^3 b^2. Folding the weight into a polynomial center
preserves the early signed bounds in the free-quotient chart. The entire
degree-190 top form is given and checked. This route retains the whole
native/K215 four-integer tuple: its largest fixed integer has 592,884
bits, and the raw four-number payload occupies 295,388 bytes.

The PDF and standalone LaTeX specify both principal equations completely:
the positive equation by polynomial abbreviations and a finite coefficient
recipe, and D83 by all 83 free assignments, 144 ordered substitutions,
and 31 residuals. The electronic circuits are convenient exact evaluators
of those same polynomials.

## Measured comparisons

All source comparisons use ProveIt commit
cdfea7d90176775d74c1c30afbe49fa78ade9897, including its incoming archives.

| Comparable construction | Domain | Variables | Degree | Operations |
|---|---|---:|---:|---:|
| Package 175 direct equation | Integers | 92 | 692 | 2,428 |
| New D83 | Integers | 83 | 624 | 1,789 |
| Incoming Affine Horizons | Positive integers | 10 | 206 | 90 |
| Package 178 whole-product center | Positive integers | 10 | 208 | 116 |
| New P190 | Positive integers | 10 | 190 | 118 |
| New P202 | Positive integers | 10 | 202 | 99 |

The package also supplies eleven direct profiles, with complete equations
and exact-degree certificates:

| Integer variables | Exact degree | Residual squares |
|---:|---:|---:|
| 79 | 8,388,620 | 27 |
| 81 | 2,048 | 29 |
| 82 | 764 | 30 |
| 83 | 624 | 31 |
| 84 | 512 | 32 |
| 85 | 444 | 33 |
| 86 | 424 | 34 |
| 87 | 268 | 35 |
| 88 | 176 | 36 |
| 89 | 128 | 37 |
| 91 | 80 | 39 |

These are measured improvements in specified families. The repository
already has nine-positive-variable equations, a 37-integer quartic,
and other tradeoffs. No globally simplest equation, minimum possible
number of variables, or worldwide novelty priority is asserted.

## Contents

- report/report.pdf: compiled mathematical paper.
- report/report.tex: complete single-file LaTeX, including both literal
  definitions and the fixed coefficient recipe.
- report/main.tex and companion TeX sources: editable modular source.
- direct/factored83/circuit.json: preferred 1,789-operation direct evaluator.
- direct/P83/circuit.json: the same polynomial in the canonical 2,939-operation
  representation used for the projection audit.
- direct/P83/projection.json: exact unit definitions and free coordinates.
- direct/P83/TIGHT_HEIGHT.json: the stronger coefficient-bound certificate.
- direct/source227.json: complete sextic source.
- direct/P*/: all eleven direct profiles and their certificates.
- direct/parent166/: retained source equations, certificates, and proofs.
- direct/frame_alternatives/: positive-frame degree-eight source and
  source metrics, checked independently from the common parent.
- positive/whole190.json and positive/quotient202.json: compact equations.
- positive/coefficients/: every actual fixed coefficient payload.
- positive/retained_coefficient_recipe.py: complete finite reconstruction.
- positive/inherited172/ and positive/source178/: retained dependencies.
- positive/SOURCE_LEDGER.json and direct/PROVENANCE.json: exact source pins.
- calibration/: direct and positive logical-boundary audits, source pins,
  selected unchanged theorem files, and archived assumption logs.
- verify.py: offline release replay and integrity check.
- RESULTS.json: machine-readable principal metrics and logical scope.
- RELEASE_VERIFICATION.json: normal and optimized replay evidence.
- REPORT_VERIFICATION.json: compilation and visual inspection record.
- MANIFEST.sha256: hashes of all release files except the manifest itself.

The two component READMEs describe the graph formats and standalone
evaluation commands in detail. Historical proof files are retained
unchanged and should be read with their own original scope.

## Reproduce the finite checks

Python 3.10 or later and its standard library suffice. From the extracted
package directory:

    python3 -B verify.py
    python3 -B -O verify.py

The replay authenticates the packaged files; reconstructs all four fixed
integers; rebuilds all fourteen supplied circuits byte for byte; checks the
new source edits, unit projections, center identities, exact degrees,
genuine input dependence, coefficient bounds, and printed definitions;
and rejects deliberately corrupted certificates. Finite Pell cases are
included as diagnostics, separate from the unbounded proof.

To save a fresh receipt, choose a path outside the release directory:

    python3 -B verify.py --receipt /tmp/conzfc-replay.json

The verification does not require a network connection or a proof-assistant
installation. No consistency proof or polynomial zero is sought.

## Rebuild the paper

A TeX installation with pdflatex, the standard AMS packages, lmodern,
microtype, fancyhdr, hyperref and xurl is needed.

    sh build_report.sh

The builder recursively assembles report/report.tex, compiles with shell
escape disabled, and rejects undefined references and overfull boxes.
The delivered PDF was also visually inspected. Direct compilation of the
single-file report.tex works without any of the modular source files.
Rebuilding a PDF can change its metadata; the original release manifest
then correctly reports a changed file.

## Logical and verification boundary

The new unbounded arithmetic is an ordinary mathematical proof. It
composes with the specifically named inherited refutation calibrations.
Finite algebra checks validate the actual emitted equations; they do not
replace Pell/CRT reasoning or certify all logical dependencies by sampling.
This package does not claim a newly compiled end-to-end Lean/Rocq theorem
or an emitted formal object-language ZFC derivation.

No external-standardness or omega-model assumption is used: the arguments
are intended internally in ZFC, including finite proof codes and internal
integers. The claimed equivalence does not prove Con(ZFC), assert actual
insolubility, or provide a refutation.

Independent reviews here mean separately assigned mathematical and code
audits within an AI-assisted workflow, not external human peer review.

## Incorporation

This is a self-contained additive research package. It may be placed as a
new numbered folder in con-zfc-diophantine-forms, with the number chosen by
the maintainer, or retained as an incoming archive pending review.
The package does not replace or alter an existing construction.
See NOTICE.md for attribution and retained licenses.
