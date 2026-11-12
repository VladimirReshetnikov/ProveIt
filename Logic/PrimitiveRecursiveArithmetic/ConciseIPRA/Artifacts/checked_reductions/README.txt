A SMALLER CHECKED PRESENTATION OF iPRA
====================================
Research prepared for Vladimir Reshetnikov, 12 November 2026

Start with ipra_checked_reductions.pdf (16-page report) or its standalone
LaTeX source, ipra_checked_reductions.tex. The source includes the selected
code listings and needs no external section files to compile.

RESULT AND ITS LIMIT

The compact guarded checker uses 477 normalized UTF-8 bytes, improving the
478-byte minimum found in the pinned proposals. Four separate validated
implementations also improve their respective families' coordinate minima.
These are implementation reductions of the established native scalar
presentation of iPRA, with written preservation arguments. They do not
delete an arithmetic or logical axiom, and do not prove global minimality.

Complete standalone modules, measured on CPython 3.12.14:

  Program          Significant tokens    AST nodes    Normalized bytes
  compact477.py                   273          305                 477
  strict623.py                    340          385                 623
  strict330.py                    330          379                 641
  native600.py                    336          378                 600
  native323.py                    323          369                 622

Observed coordinatewise envelopes (different programs attain coordinates):

  Compact guarded:       (244,267,478) -> (244,267,477)
  Strict native:         (334,386,628) -> (330,379,623)
  Native goal validated: (324,370,607) -> (323,369,600)

The retained compact token/AST minima use JSON-line streaming; the compact
byte minima use a whole JSON array. The envelope combines different framing
contracts. No single new program beats all three old compact coordinates.
These observed minima are upper bounds on an unknown optimum, not proved
mathematical lower bounds.

THEORY AND INTERPRETATIONS

The report specifies the target full first-order intuitionistic primitive
recursive arithmetic, the inherited native Eq/Q/D scalar-iterator rules,
the guarded compact rules, all ordinary connective macros, and the ordinary
arithmetic realization. Its two numerical domains are whole domains;
equality is actual numerical equality; both comparison maps are x=y.
Internal term and formula round trips provide bi-interpretability and hence
equiconsistency. These mathematical results are inherited from the pinned
development and preserved by the proved implementation transformations.
The upstream article and native Lean sources are supplied for inspection.
They were not newly rebuilt or independently formalized in this work.

INPUT CONTRACTS

All five selected modules read one finite JSON array. Earlier entries are
four-field proof packets [m,s,u,t], consumed from right to left; an unused
prefix is allowed. Successful acceptance means normal exit with exactly
ACCEPT followed by one newline. Exceptions reject.

* strict623.py and strict330.py validate the whole exact-integer/list
  alphabet (including unused entries) and the closed native Eq/D public goal.
* native600.py and native323.py validate the closed native Eq/D public goal.
  The theorem claim retains the exact-integer/list proof-data contract;
  these programs do not claim whole-input alphabet validation.
* compact477.py assumes finite exact-integer/list proof data and a canonical
  closed GUARDED Eq/D public goal. Its final array entry is [A,k], normally
  [A,0], instead of the native programs' final entry A. The compact module
  does not independently validate that entire public grammar or alphabet.
  Its successful-run simulation and canonical completeness prove public
  theorem preservation. Exact arbitrary-certificate acceptance equivalence
  is false: an included empty-auxiliary boundary is newly rejected.

The public guarded grammar and scope-header proof are stated explicitly in
Section 4. Do not apply the header construction to the unrestricted native
grammar: that extension has a known zero-free counterexample. Do not charge
the compact module as if it provided the stricter validated interface.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 203cbef70b358772a43d40ba340209b9ae1d6e32
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The audit parsed 2,543 artifact Python paths and 1,709 Python members of
13 incoming ZIPs: 4,252 paths, 1,658 unique contents, zero parse errors.
Candidate novelty is relative to that inspected corpus, not a claim of
literature-wide priority. The new checkers compose or simplify ideas whose
individual sources are identified in the report and evidence files.
No repository commit, pull request, or external message was created.

VERIFICATION AND REPRODUCTION

Verify the delivered manifest BEFORE regenerating any files:

  python3 verify_manifest.py

Recompute all five complete-module metrics:

  python3 measure.py

Replay the frozen offline checks (standard-library Python only):

  python3 reproduce.py

The retained native receipts cover 1,530 isolated process executions on
85 fixtures, including ordinary and optimized (-O) Python; there are no
acceptance mismatches or failed expectations. The compact receipt covers
454 invocations. Twenty additional independent compact process checks are
in review/. A portable compact smoke run was made after materialization.
Finite testing is not the universal proof: the written simulation proofs
and the inherited mathematical bridge supply the soundness/completeness
arguments. There is no new Lean or Rocq proof of these Python programs.

Measure exactly on CPython 3.12.14. Normalization is
ast.unparse(ast.parse(source)) plus one final LF. Significant tokens exclude
layout and comments; every AST node and every normalized UTF-8 byte count.
The measured modules include JSON reading and the acceptance output, import
only standard JSON support, and do not load proof databases or hidden code.

The complete source census is optional and requires a checkout of the pin:

  python3 evidence/census.py --repo /path/to/pinned/ProveIt

Rebuild the standalone source from the editable modular source:

  python3 assemble.py

Rebuild the PDF with an installed TeX distribution:

  python3 build_pdf.py

Alternatively, python3 reproduce.py --pdf performs both verification and
the PDF rebuild. The builder uses private temporary TeX resources when the
installation lacks lookup caches; it does not change global TeX files.
It was adapted from the upstream MIT-0 builder only by changing the default
report filename. A PDF rebuild requires the packages declared in the source.

Regenerated receipts or PDF metadata can legitimately change manifest
hashes; use --skip-manifest only after deliberately modifying a verified
copy. Source assembly is deterministic. Physical resource exhaustion is
outside the finite abstract execution equivalences.

ARCHIVE MAP

  ipra_checked_reductions.tex/.pdf   Main standalone report
  sections/, paper_template.tex     Editable modular report source
  checkers/                        Five selected complete programs
  validation/                      Native controls, fixtures, receipts
  compact_validation/              Compact controls, fixtures, verifier
  proofs/                          Written preservation proofs
  review/                          Independent analysis-agent reviews
  evidence/                        Census, metrics, origins, final QA
  reference/upstream_article/       Pinned 503-page article and source
  reference/upstream_lean/          Pinned native formalization sources
  CLAIMS.json                      Machine-readable claims and limits
  MANIFEST.sha256                  All delivered hashes except itself

Inherited reference material is clearly separated from the new 16-page
report. Lean dependencies are not vendored, so no offline Lean rebuild is
promised. Analysis-agent review is not external human peer review.

All inherited material retains the repository's MIT No Attribution license.
The new code and documentation are offered under the same terms; see
LICENSE.txt.
