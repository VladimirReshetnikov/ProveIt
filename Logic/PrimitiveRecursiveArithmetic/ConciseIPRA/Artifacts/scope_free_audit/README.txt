iPRA: A MEASURED REFINEMENT AND A SCOPE-FREE CORRECTNESS AUDIT
13 November 2026
=========================================================

READ THIS STATUS FIRST

The requested construction below the entire current compact frontier was
NOT established. This package must not be filed as a new globally simplest
axiomatization or as an arithmetic/logical axiom deletion.

There are two distinct results:

1. A single complete checker, code/checker_sorted_line.py, measures
   295 significant tokens / 332 AST nodes / 553 normalized UTF-8 bytes.
   This is below all three coordinates of the current SORTED-VALIDATION
   envelope 297 / 335 / 556, with an explicit change to one-line JSON input.
   The source-selected native calculus, sorted padding convention, and
   canonical-completeness qualification are inherited unchanged.

2. The separate scope_free/checker.py replaces the numerical scope floor
   by fresh negative integer names determined from the visible proof data.
   It measures 249 / 272 / 549, versus 239 / 261 / 549 for its matched
   control. The report gives a written soundness proof on all accepted
   integer/list auxiliary trees and a canonical-completeness proof.
   The naming idea was already an uncertified long_names.py experiment in
   the repository. Its completion here is not a new global size record.

COMPARISON

Pinned commit: 65c32fbe4730bfe5a064502b0b95ebc798c732fa
Repository: https://github.com/VladimirReshetnikov/ProveIt
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Current qualified coordinate envelopes (DIFFERENT programs attain the
coordinates within each row):

  Compact canonical theorem:              239 / 255 / 460
  Compact general sequent:                239 / 255 / 458
  Compact seeded sequent:                 238 / 255 / 455
  Sorted public-goal validation:          297 / 335 / 556
  Exact actual-binding public validation: 303 / 338 / 582

The sorted-line result does not beat the compact envelopes. Those finite
corpus records are achieved upper bounds on an unknown optimum, not proven
complexity lower bounds. The 3,776-source audit and all four incoming
archive hashes are supplied in evidence/.

MATHEMATICAL SCOPE

The ordinary realization is the inherited scalar theory T_eq, with the
whole numerical domain and actual equality. Its full first-order iPRA
bi-interpretation has both formula round trips and numerical comparison
graphs x=y. The report specifies its axioms and intuitionistic logical
rules, the native calculus, the interpretation maps, and the exact inherited
Lean theorem dependencies. The Python semantics are not newly formalized
in Lean or Rocq in this package.

The sorted checker validates its public goal but admits administrative
padding aliases. Completeness is for canonical theorem encodings, not every
such alias. The scope-free compact module assumes exact integer/list data
and a canonical closed guarded public root; it does not validate that entire
contract. Do not mix the size of one module with the interface of the other.

FILES

  report.pdf                  Complete 18-page mathematical report.
  report.tex                  Its principal LaTeX source.
  scope_free/proof.tex         Detailed included proof; needed to rebuild.
  evidence/scope_free_summary.tex  Included evidence paragraph.
  code/checker_sorted_line.py  Selected complete checker, 295/332/553.
  examples/                   One-line native proof certificates.
  tests/verify_sorted.py       Process checks of the selected refinement.
  scope_free/                 Separate checker, producer, fixtures, receipt.
  measure.py                  Complete-module measurements and hashes.
  reproduce.py                Manifest, measurements, and optional tests.
  build_report.py             Offline LaTeX build with local-format fallback.
  reference/                 Frozen control, selected upstream proof sources,
                              prior-art evidence, and repository license.
  PROVENANCE.json             Exact source URLs, commit, and hashes.
  CLAIMS.json                 Machine-readable result and unmet target.
  MANIFEST.sha256             Integrity of the packaged files.

DIRECT USE

Use CPython 3.12.14 for the published normalized metrics. No third-party
Python package is needed by either checker.

  python3 code/checker_sorted_line.py < examples/zero_computation.json
  python3 code/checker_sorted_line.py < examples/induction.json
  python3 code/checker_sorted_line.py < examples/implication_elimination.json

The input must be one physical JSON line; escaped newlines inside a JSON
string are not physical line breaks. The last array element is the public
goal. Earlier elements are popped as three-field packets. Unused earlier
array elements and later physical lines are ignored as documented. A normal
exit with exactly ACCEPT and one line feed is success; exceptions reject.

  python3 code/checker_sorted_line.py < examples/false_zero_equals_one.json

This last command must reject. The file is a deliberately invalid proof,
not a derivation of a contradiction.

  python3 -X int_max_str_digits=0 scope_free/checker.py \
      < scope_free/fixtures/specialization.jsonl

The scope-free input is a stream: first the goal, then one packet per line.
The displayed runtime setting removes a decimal-conversion guard; it is
explicitly outside the measured module. The source-size claim uses the
same ideal finite-resource convention as the upstream recursive programs.
The practical producer can still be very expensive: a large inherited
fixture exceeded a 2,000,000-digit diagnostic cap and was not run. The small
induction and specialization examples do run and use their checked closure.

REPRODUCE

  python3 reproduce.py
  python3 reproduce.py --tests
  python3 build_report.py

The first verifies the delivered manifest and remeasures complete sources.
The second additionally reruns 476 sorted-interface process checks and 47
scope-free expectations. The latter deliberately tests an unsound fixed-name
control and expects its false proof to be accepted, thereby checking that
the genuine freshness rule is doing work. All recorded expectations passed.

Check the delivered manifest BEFORE regenerating files. Rebuilding PDFs or
rerunning receipts on another runtime can change bytes; it does not preserve
the original delivered manifest. The build script downloads nothing, uses
installed TeX and Latin Modern/AMS packages, and makes a private TeX format
if the installed source tree lacks a cached format. Rendered QA images are
not needed to rebuild the report and are not bundled.

For an independent source census after obtaining the pinned repository:

  python3 reference/corpus_census.py /path/to/ConciseIPRA \
      --output census_reproduced.json

The census is a static size audit. A print-ACCEPT screen does not certify
soundness; qualified records were separately classified by their contracts.

Further research questions appear in the report. No remote repository files
were modified by this investigation.
