EQUATION-ONLY ALIASES AND FIXED SPECIALIZATION IN iPRA
Research package prepared for Vladimir Reshetnikov
12 November 2026

READ FIRST

This package proves a new restriction of the ConciseIPRA raw calculus:
fresh-alias discharge and backward substitution may both be limited to
literal equations while reusable clauses are specialized only at the
newest numerical parameter. The restricted presentation has the same
native consequences as the reference calculus and inherits its full
bi-interpretation with first-order intuitionistic primitive recursive
arithmetic. Both formula round trips and the numerical comparison maps
are addressed; equiconsistency alone is not the claim.

It does NOT meet the requested global checker-size target. The new
mathematical restriction makes its matched checker larger. Separately,
three refinements of the inherited calculus improve the fully validated
native checker envelope from (342 tokens, 391 AST nodes, 637 bytes) to
(338, 386, 633). Different programs attain those coordinate minima.
The compact promised-input envelope (248, 270, 479) remains unbeaten.
The repository's recorded minima are achieved upper bounds, not proved
lower bounds for all possible presentations.

MAIN FILES

  report.pdf                  Complete typeset research report
  report.tex                  Main LaTeX source
  implementation_results.tex  Implementation and verification section
  strict_results.tex          Strict checker comparison and proof summary
  build_pdf.py                Portable PDF build helper
  atomic/                    New restricted calculus and proof compiler
  strict/                    Separate strict native checker refinements
  reference/                 Exact inherited source and compact controls
  evidence/                  Audits, hashes, measurements and review receipts
  CLAIMS.json                Machine-readable scope and limits of claims
  PROVENANCE.json            Source identities and archive organization
  MANIFEST.sha256            SHA-256 of every other delivered file

The atomic and strict directories each contain their own README, matched
controls, tests, detailed arguments, reproduction scripts and provenance.
They are separate projects: the small strict programs do not implement
the equation-only Alias/Back theorem.

REPRODUCE

Use CPython 3.12.14 to reproduce the exact normalized measurements.
Only its standard library is required for the checker and compiler work.

  python3 measure.py
  python3 reproduce.py
  python3 reproduce.py --quick
  python3 build_pdf.py

measure.py reports whole-module measurements without modifying evidence.
reproduce.py checks the package manifest and runs both complete suites
in temporary copies, preserving the distributed sources and evidence.
The --quick option runs representative acceptance/rejection examples
and checks all measured sizes, without regenerating the full suites.
The full suites comprise 196 atomic-checker process runs, 34 closed
source compilations, three open-sequent compiler examples, and 336 strict
checker process runs with exact source-transformation checks.

For individual certificates:

  python3 atomic/code/atomic_alias.py < atomic/tests/compound_specialization_rank2.json
  python3 strict/checkers/bytes633.py < strict/fixtures/00_compound_case_introduction_local.json

The PDF helper uses an installed pdflatex or builds a private format from
installed pdfTeX/LaTeX sources. It does not download dependencies, execute
shell-escape commands from TeX, or change the system TeX installation.
A normal LaTeX installation can instead compile report.tex directly.
The source chapters in reference/ are inherited dependencies for reading;
they are not standalone LaTeX documents or included in the main build.

EVIDENCE AND LIMITS

The initial source snapshot is
ae3c615de1b0dabe386f2bdbdb0f955cd8326e49.
All seven incoming ZIP archives at that snapshot were authenticated and
reviewed. A final recheck at 2dc8c095b10b74cb9d4383cd5c1153cac3d08236
authenticated the additional ipra_479_predecessor57 archive. It leaves
the relevant compact and fully validated incumbent envelopes unchanged.
Its separate native goal-only checker has 607 normalized bytes; its
proof-data alphabet remains a promise, so that is a different category.

The new mathematical equivalence has a written proof and an executable
source-to-target compiler. It has not been formally verified in Lean or
Rocq. The inherited arithmetic bridge is supplied and attributed; its
Lean development was not rebuilt here. Independent review means a
separate review within this research run, not external peer review.
Finite test executions supplement the general arguments and do not
establish absolute minimality or replace the mathematical proof.

Inherited ProveIt material is distributed under its attached MIT-0
license. New explanatory material and code in this package use the same
license. The standard Python and TeX platforms are not included.
