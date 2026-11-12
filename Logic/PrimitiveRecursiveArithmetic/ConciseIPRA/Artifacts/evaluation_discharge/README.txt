iPRA WITH EVALUATION AT WITNESS DISCHARGE
========================================
Prepared for Vladimir Reshetnikov, November 11, 2026.

START HERE
----------
ipra_evaluation_discharge.pdf is the full research report.
ipra_evaluation_discharge.tex is its standalone LaTeX source.

RESULT
------
The main presentation uses RAW scalar iterator terms and exactly three
inference families: Use, Intro, and Evaluate-and-discharge. It retains one
explicit initial axiom clause [ ; y.y=y]. There is no normalization, implicit
computation conversion, proof oracle, or normalization fuel.

The discharge rule proves D B, opens its clause at fresh b, proves arbitrary
formulas E and F in that scope, then performs one deterministic evaluation
and exports the result only if b is absent. The evaluation has the two
existing raw Eval patterns and identity as the fallback. A compound E forces
identity and recovers ordinary witness elimination. Dummy witness opening
recovers both Eval cases. The report proves exact unchanged-end-sequent
translations in both directions.

Composing with the attributed, included arithmetic and logical foundations
gives bi-interpretability with full first-order intuitionistic PRA: whole
domains, actual equality, identity numerical composite graphs x=y, both
formula round trips, and equiconsistency.

The zero/ companion also has three families. It contracts only literal-zero
iterators and uses the existing SeedEval pattern at discharge. It has the
smaller source by bytes and tokens; the raw system has the simpler syntax
specification and slightly fewer AST nodes.

MEASUREMENTS
------------
Complete modules; CPython 3.12.14; actual docstrings removed; ast.unparse + LF.
                                  Bytes Tokens AST Gzip 9
Raw fused                          1892   643   695  773
Matched raw separate               1995   665   717  786
Zero-normal fused                  1858   633   697  777
Matched zero-normal separate       1879   645   707  771
Incoming inferred output control   1983   663   751  812
Incoming inferred witness          1990   683   771  819
Incoming explicit clause discharge 2010   636   708  791

The raw fusion alone saves 103 bytes, 22 tokens, 22 AST nodes. The zero fusion
alone saves 21 bytes, 12 tokens, 10 AST nodes, while gzip grows 6 bytes.
The zero program improves all three primary coordinates of the three listed
incoming strict programs. The raw program has a higher token count than the
636-token explicit clause-discharge program. No global optimum is claimed;
the repository's different compact codec is 508 bytes, and its validated
public-goal companion is 780. No new Lean/Rocq proof is claimed.

REPRODUCE
---------
Use Python 3.10+ for structural pattern matching; recorded metrics use 3.12.14.
All Python tooling uses the standard library and makes no network calls.

  python3 verify_manifest.py
  python3 reproduce.py
  python3 measure.py
  python3 raw/checker.py < raw/examples/raw_zero_computation.json
  python3 build_pdf.py

The main report is standalone and needs standard TeX Live packages. PDF
building disables shell escape. Reproduction regenerates evidence/examples;
PDF rebuilding may change metadata. The manifest describes original delivered
bytes, so verify it before reproducing or rebuilding.

VERIFICATION
------------
Raw: 33 pinned upstream fixtures; 38 accepted fused examples; 38 exact-goal
control roundtrips; 38 independent upstream reverse replays; 34 rejected
adversaries; 144 ordinary/optimized CLI checks.
Zero: 85 pinned upstream fixtures translated/replayed into both systems;
both transformation directions and 85 roundtrips; 6 additional positives;
27 adversaries;66 ordinary/optimized CLI checks.
Independent reviewer: 12 raw and 6 zero fixtures, 36 CLI checks in total.
The integrated reproduction passed every expected outcome.
These finite checks supplement the general written proofs.

CONTENTS
--------
raw/                    Raw checker, matched control, translations and evidence.
zero/                   Zero-normal checker, matched control and evidence.
reference/foundations/  Attributed complete inherited mathematical foundations.
reference/lean/         Frozen relevant Lean source excerpts, not a standalone
                        Lean project. Obtain full dependencies from the pinned repo.
reference/*.py          Frozen incoming peer checkers used in the metric table.
evidence/               Metrics, reproduction results and independent review.
validation/             Independently written fixtures and expected outcomes.
sections/               Editable parts of the new paper (main TeX is flattened).
CLAIMS.json             Precise claims and limits.
SOURCE_PROVENANCE.json  Pinned revision, source paths, archive and file hashes.
MANIFEST.json           SHA-256 ledger of delivered files.
LICENSE.txt             MIT No Attribution license, also used for new materials.

The inspected snapshot is 11814771b7490dfbea0ed5fcf0f5b23586334764, including
all six incoming archives. The report includes further research questions.
