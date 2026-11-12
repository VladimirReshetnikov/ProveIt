A smaller guarded presentation of iPRA
=====================================
Prepared for Vladimir Reshetnikov, November 11, 2026.

READ FIRST

report.pdf is the main mathematical report; report.tex is its source.
The report states every primitive axiom and inference rule, proves the new
dependency and composition results, explains the two interpretations and
both composites, and includes further research questions.

RESULT

The guarded-core deterministic introduction and source-dispatch elimination
can coexist. The key observation is that the inherited proof recovering
literal-zero-source equality transport uses only equation induction and
equational reasoning. Its equation case splits follow from induction by
ignoring the induction hypothesis. Logical case introduction is not needed
for that bootstrap.

The resulting public presentation has the same canonical guarded
consequence relation as the inherited guarded core. Its ordinary realization
is bi-interpretable and equiconsistent with full first-order iPRA, with whole
numerical domains, actual equality, and identity numerical composites.

The gain is strict but modest. This package does not establish an absolute
minimum or a substantially different arithmetic basis. The individual
source-dispatch and guarded-core constructions, scalar arithmetic bridge,
logical macros, and raw representation are inherited and attributed.

PINNED COMPARISON

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 1517d9d79ce33f631e0f82960c849427cbba23bf
Subdirectory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The comparison includes the latest source-dispatch result present at that
commit. Exact frozen comparison files and their Git blob checks are supplied
in implementation/PROVENANCE.json; additional mathematical foundations are
listed in reference/PROVENANCE.json.

MEASURED COMPLETE CHECKERS

All sizes below count whole standalone Python modules after CPython 3.12.14
ast.unparse normalization and a final newline.

                                  tokens   AST nodes   bytes   gzip-9
code/checker_tokens.py                257         285     568      338
code/checker_ast.py                   261         279     603      345
code/checker_bytes.py                 264         301     522      328
code/checker_strict.py                490         561    1202      571

The old attained coordinate minima were 259 tokens, 283 AST nodes, and 526
bytes. The new minima 257, 279, and 522 belong to THREE DIFFERENT programs.
No one supplied program attains the whole triple. Gzip uses level 9 and
mtime=0 and is an informational metric.

PUBLIC STATEMENTS VERSUS AUXILIARY PROOF FORMULAS

Public formulas are equations and D-binders. An atomic matrix directly
under D has the exact guarded form

    I(y,0;u.h) = I(y,0;u.k).

Internal proofs may also contain unguarded atomic D matrices and Q resources.
They have an explicitly specified mixed reading. The full equivalence and
both formula composites are asserted for the canonical public grammar.
They are not asserted for every unguarded auxiliary formula.

The compact modules have the same canonical-goal contract as the inherited
guarded-core compact modules: they do not reject all noncanonical end goals.
Use checker_strict.py if that rejection is required. It is self-contained
and its entire validator is included in the 1202-byte measurement. The
corresponding pinned guarded-core strict checker is 1208 bytes.

QUICK START

From the extracted archive root:

    python3 code/checker_strict.py < implementation/composed_tests/computation_zero_local.json
    python3 implementation/reproduce_composition.py

The first command prints ACCEPT on success. The second regenerates the
certificates, runs all process checks, audits the named proof nodes, and
recomputes metrics. It uses only Python's standard library. The recorded run
contains 150 executions, 92 expected acceptances, 58 expected rejections,
and zero failures, including both ordinary Python and python3 -O.

The token profile uses global fresh names; the AST/byte/strict profiles use
local fresh names. Choose certificates ending in _global.json for the token
profile and _local.json for the others. Do not assume that raw certificate
streams are interchangeable between these protocols.

REBUILD THE PDF

On a standard TeX installation, from the archive root:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

The LaTeX source loads its complete code listing from code/checker_bytes.py,
so keep the archive's relative directory layout when rebuilding.

CONTENTS

report.tex, report.pdf       Main report and compiled PDF.
CLAIMS.json                 Machine-readable scope and limitations.
code/                       Four standalone checkers and normalized gzip files.
implementation/             Reproduction bundle, detailed receipts, producers,
                            42 generated certificate files, exact baselines.
reference/foundations/      Frozen mathematical sources for the inherited
                            logical, arithmetic, guarded, and codec bridges.
reference/PROVENANCE.json    Original repository paths and verified Git blob IDs.
evidence/                   Measurements, validation receipts, build summary.
MANIFEST.sha256             Checksums of all other packaged files.

TRUST AND VERIFICATION STATUS

The checkers import no producer, proof database, or project module. Producers
are larger untrusted tools that only construct certificates.

The mathematical composition is a written proof. It has not been formally
verified in Lean or Rocq in this delivery. Upstream Lean results are cited
for their stated roles; no new formal-verification claim is made. Finite
process tests exercise the implementation but do not replace the universal
proofs or the inherited raw-codec soundness argument.

The repository and all remote branches were left unchanged. The requested
deliverable is this research package.

ATTRIBUTION

Frozen upstream sources are from ProveIt under its MIT No Attribution
license, reproduced in reference/LICENSE_ProveIt.txt. The report identifies
which mathematical constructions are inherited and which dependency and
composition arguments are developed here.
