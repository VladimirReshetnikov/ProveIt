iPRA: SMALLER CHECKERS AND THE INDEPENDENCE OF PROGRESS
=====================================================
Prepared for Vladimir Reshetnikov, 12 November 2026.

RESULT
------
This archive supplies two smaller implementations of the existing complete
bi-interpretable iPRA presentation, and a new written mathematical proof
answering the repository's open progress-independence question.

The new token program is 251 tokens / 283 AST nodes / 605 normalized bytes.
The new byte program is 269 tokens / 301 AST nodes / 502 normalized bytes.
They improve the former 253-token and 506-byte records separately. The
275-node AST record is unchanged. No single program attains all three
coordinates, and no universally simplest axiomatization is established.

MAIN MATHEMATICAL THEOREM
-------------------------
QI by progress is not admissible over the other seven native kernel rules.
There is a coherent actual-equality model of all finite scalar iterator
computations, successor coverage, and separation in which

    I(c, 0; u.u) = 1 != 0.

For E(y) := I(y, 0; u.u) = 0, its base and successor-step sequent are
derivable without progress, but Q_y E(y) is false in that model.

The model is constructed using a staged tower of ordinary ultrapowers.
Universal cross-extensionality makes all iterator descriptions coherent
under parameter substitution. The stronger initial structure also preserves
cancellative addition and I(n, 0; u.Su) = n. The proof can be followed entirely
in the report; it does not rest on a finite numerical experiment.

A second written result constructs arbitrary finite scalar clocks without
induction and excludes every fixed finite successor cycle. Together with
the repository's seven earlier independence results, the main theorem
establishes irredundance of all eight original kernel rule families.
This is not a lower bound on other calculi, rule fusions, or checker sizes.

START HERE
----------
ipra_progress_independence.pdf   Compiled full report.
ipra_progress_independence.tex   Self-contained editable LaTeX source.
CLAIMS.json                     Exact positive claims and limits.

The report contains every primitive rule, ordinary logical macros, both
interpretations and their identity composites, the complete countermodel
construction, proofs of the refinements, checker listings, and further
research questions. The underlying arithmetic bi-interpretation is inherited
from the cited repository work and preserved by the new checking arguments.

ARTIFACTS
---------
checker/code/checker_tokens.py   New 251-token complete compact program.
checker/code/checker_compact.py  New 502-byte complete compact program.
checker/code/checker_parity.py   503-byte trace-inclusion companion.
checker/code/checker_strict.py   869-byte program with full public validation.
checker/reference/              Frozen matched comparison programs and license.
checker/fixtures*/              Positive and adversarial certificates.
checker/ARGUMENT.txt            Universal trace and compiler arguments.
checker/evidence/               Measurements, tests, source audit, tree identity.
mathematics/                    Reusable TeX fragments and bounded evaluators.
reference/foundations/          Unchanged attributed arithmetic bridge sources.
reference/Native*.lean          Inspected upstream kernel and independence files.
SOURCE_PROVENANCE.json          Exact source snapshot and hashes.
MANIFEST.sha256                 SHA-256 integrity ledger.

REPRODUCE
---------
Use CPython 3.12.14 for exactly matching source-normalization measurements.
All checking and validation scripts use only the standard library.

    python3 verify_manifest.py
    python3 reproduce.py
    python3 build_pdf.py

The last command additionally needs pdfLaTeX and the packages in the source
preamble. The LaTeX source contains the checker listings and all mathematical
sections; no external figure or TeX input is needed to rebuild the report.

Example of the strict public-input checker:

    python3 checker/code/checker_strict.py < checker/fixtures/computation_zero_local.json

Acceptance is successful exit with exact stdout ACCEPT and a newline.
Exceptions reject, including under python -O. Compact programs assume the
documented canonical integer/list public interface; the strict companion
validates that interface itself. The token and byte profiles have different
scope conventions, so their corresponding fixture directories must not be
mixed. A finite Python recursion or memory limit can reject large proofs;
the mathematical checking algorithms use unbounded finite resources.

EVIDENCE AND LIMITS
-------------------
The packaged checker suite ran 512 processes with no unexpected outcomes.
The scalar clock evaluator passed 1,243 bounded standard evaluations.
The initial-model evaluator passed 16,665 bounded algebraic checks.
These are finite implementation checks, not proof-assistant verification
or a simulation of the nonprincipal ultrapower model.

The model proof uses ordinary classical metamathematics with choice. This is
legitimate for a countermodel to intuitionistic derivability; it adds no
classical axiom to the object calculus. The construction does not settle
whether the separate successor-uniqueness principle is equivalent to iPRA.

No new Lean or Rocq verification, global complexity lower bound, all-coordinate
single-program improvement, or new smaller arithmetic axiom basis is claimed.
No GitHub repository files were changed.

PINNED SOURCE
-------------
https://github.com/VladimirReshetnikov/ProveIt
Commit 6ffc49f55d355b548f7a8e1530570aee5de086b3
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Inherited material retains the upstream license under reference/ and checker/.
The mathematical bridge and prior code refinements are explicitly attributed.
