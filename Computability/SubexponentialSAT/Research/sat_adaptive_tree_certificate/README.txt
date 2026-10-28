ADAPTIVE CONTRACTION TREES WITH EXACT SUPPORT CERTIFICATES
Research for Vladimir Reshetnikov, October 26, 2026 (Pacific date)

Start with report.pdf. Its complete editable source is report.tex.

RESULT

For the reviewed generic normalized Boolean tensor-contraction interface,
with s wires, root maximum degree <= ceil(s^0.9), and initial precision and
truncation <= s, the new bound is

  time  <= poly(s + description length)
           * 2^((30.891018920366... + o(1)) s/sqrt(ceil(log2 s))),
  space <= poly(s + description length)
           * 2^((30.753912832055... + o(1)) s/sqrt(ceil(log2 s))).

Safe eventual coefficients are 30.892 for time and 30.754 for space.
The exact time constant is
  (pi/ln 2) [sqrt(128000/5103) + sqrt(134144/41067)],
and the exact space constant is 32 pi sqrt(295)/(81 ln 2).

This improves the strongest comparable submitted coefficient 35.354588...
and a stronger compatible existing-ingredients bound 35.063598... .
It is a coefficient improvement in an exponential UPPER BOUND, not a measured
runtime ratio. It uses subexponential space, not polynomial space.

The mechanism selects one of three fully specified contraction trees for
each exact pair-weight allocation. An elementary support-averaging theorem
gives a uniform certificate covering every feasible allocation, with all
child-factor calls paid for. A strict rational 9 -> 13 -> 7 schedule closes
the complete recursion. These steps add a new quantitative certificate to
the inspected corpus; basic averaging and tree methods are classical.

WHAT IS NOT CLAIMED

The general SAT order n loglog(n)/sqrt(log n) and fixed-density order
n/sqrt(log n) remain unchanged. The conditional n/log(n)-type proposals
remain unproved. Constants are per normalized wire, not per SAT variable.
Low-degree branches have stronger premises. No comparison to an unspecified
big-O constant, no global optimality of schedules, and no literature-wide
priority claim is made. The upstream deformation/recovery/reduction and
packet interfaces remain explicit mathematical dependencies.

The code checks exact finite certificates and contraction algebra. It is
not an end-to-end SAT solver or an implementation of the theoretical fast
matrix-multiplication backend. No Lean or Rocq development was rebuilt.

CORPUS

Two primary manuscripts, fifteen placed refinement packets, and five newer
archives in docs/incoming were reviewed at ProveIt commit
fa6e904d109b738154db7fe41e7f2777e6d24aee.
The source manifest contains immutable URLs, Git blob IDs and SHA-256 hashes.
The repository checkout was not modified. Incoming archives were inspected
without executing their supplied programs.

CONTENTS

report.tex / report.pdf          Full review, proof, schedule, barrier, scope.
code/portfolio.py               Primary support generator and exact selector.
data/portfolios.json            Fixed certified plans and exact expected norms.
code/verify_portfolios_independent.py
                               Independently reconstructed integer certificates.
code/verify_selector.py         Primary/independent selector comparison.
code/verify_schedule.py         Exact Fraction/rational interval schedule checks.
code/verify_algebra.py          Literal sum versus tree contractions over
                               (Z/64Z)[V]/(V^2), including zero divisors.
code/verify_table_width.py      Complete-graph boundary-width and exact-budget checks.
results/                       Normal and optimized replay records and PDF QA.
audit/                         Detailed source, proof and independent review notes.
provenance/                    Frozen source manifest and relevant commit log.
PROOF_STATUS.json              New/imported/unresolved claims and verification scope.
MANIFEST.sha256.json           Delivered-file checksums (excludes itself).

REPLAY

Use Python 3.10 or newer; check programs require only its standard library.
From the extracted directory:

  python3 verify_manifest.py
  python3 run_checks.py
  python3 build_report.py

On Windows, use python in place of python3 if that is the installed command.
The first command checks delivered bytes; run it before regenerating outputs.
run_checks.py runs every checker normally and with -O and requires identical
JSON results. It rewrites results/. build_report.py requires pdfLaTeX and
the standard LaTeX packages in report.tex, runs with shell escape disabled,
and rejects overfull boxes and unresolved references. _build/ is disposable.

The main exact support certificates inspect 21^3 = 9,261 and 33^3 = 35,937
operation tuples. All tests use explicit exceptions; optimized Python does
not remove the checks. PDF layout was separately rendered and inspected.

SELECTOR EXAMPLE

To certify the fixed menus:
  python3 code/portfolio.py

To select a tree for actual exact-list dimensions:
  python3 code/portfolio.py --dimensions dimensions.json

The input is an object with "groups" (7, 9 or 13) and "dimensions", a list
of [source_group, target_group, positive_integer_cardinality] for every
ordered pair of distinct groups. Empty-list allocations contribute zero and
must be skipped. Selection compares exact integer fifth powers; no floating
point enters the branch choice.

The final report also proves the exact explicit-table width
2 ceil(r/3) (r-ceil(r/3)) for complete directed pair graphs. This is a
representation-specific barrier, not a lower bound for SAT or all tensor
contraction algorithms.

CLOSING RELOCATION CHECK

Closing head dde01c4a63b822c25b8eb345299346c36f837b49 includes placement
commit 450252e9d86c155f188b485629b9755c5c665371. All 230 files of the
five incoming packets were independently checked against their new Git blob
IDs and are byte-identical to the reviewed archive members. docs/incoming
contains only README.md at that closing head. Two earlier replay scripts were
restored by the placement; no new mathematical bound was introduced.
The original source pin and immutable archive URLs remain valid provenance.
