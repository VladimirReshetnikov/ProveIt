REMOVING FORMULA TEMPLATES FROM BACKWARD SUBSTITUTION
Research report for Vladimir Reshetnikov, 13 November 2026

RESULT

The deterministic diagonal Alias/Back calculus remains equivalent to full
first-order iPRA when Back is restricted to literal equations. It also admits
the one-term crossed rule

    b = t,  h[t/b] = r   ==>   r = h,

where b is the newest parameter, h is the only substituted term, and r and t
may contain b. Both new calculi preserve all scoped open consequence judgments
of the liberal source calculus. The inherited whole-domain bi-interpretation,
actual equality, identity numerical composites, and both formula round trips
therefore transfer unchanged.

This answers the pinned article's explicit question wit:q:ab-back. The proof
first establishes persistent clause realization, then atomic transport, then
full transport by formula-depth induction, and only afterward compiles source
derivations. It never silently weakens a completed deterministic derivation.

SIZE TARGET NOT MET

This is a mathematical restriction of a primitive equality rule, not a new
complete-checker size record. Whole standalone modules, normalized with
CPython 3.12.14 after removing genuine docstrings:

                         tokens   AST   bytes   gzip-9
Pinned newest control       862  1011    3245     1044
Equation-only Back          869  1021    3263     1053
One-term crossed Back       867  1022    3267     1058

The compact shifted byte record in the pinned corpus is 461 bytes under a
different contract. The current request's lower-envelope target remains
unresolved; no absolute-minimum or frontier-beating claim is made.

BASELINE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Revision: 798856e4ef2d02b7f9c0f1660828c5ce58f277f2
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Open question: docs/Article/chapters/ch07_wit.tex, wit:q:ab-back
Inherited bridge: base:thm:bridge and wit:cor:ab-bridge

The article's exact LaTeX sources are included under reference/article/.
They are reference dependencies. No upstream changes or new Lean/Rocq
formalization are claimed. The one Lean file included is an exact reference
to the existing bridge and requires its original repository imports.

CONTENTS

ipra_equational_transport.tex/.pdf : complete research report
code/equation_back.py             : standalone equation-only checker
code/crossed_back.py              : standalone crossed checker
code/source_liberal.py            : standalone liberal source checker
code/compile_equational.py        : untrusted source-to-equation compiler
code/compile_crossed.py           : untrusted source-to-crossed compiler
tests/source/                    : source certificate fixtures
tests/equation/, tests/crossed/   : compiled closed certificates
tests/open/                      : open-sequent transformation fixtures
tests/kernel_fixtures/            : crossed-rule acceptance/rejection fixtures
verify_compiler.py               : reproduce proof translations and CLI tests
verify_kernel.py                 : primitive-rule tests and negative controls
measure.py                       : reproduce whole-module size measurements
build.py                         : rebuild PDF, using installed TeX only
proofs/                          : proof fragment and independent audits
reference/                       : pinned controls and inherited sources
evidence/                        : exact measurements and validation receipts
PROVENANCE.json                  : snapshot identity and reference hashes
SHA256SUMS                       : hashes of archive files other than itself

REPRODUCE

From this extracted directory, with Python 3.12.14 for exact size reproduction:

    python3 verify_compiler.py
    python3 verify_kernel.py
    python3 measure.py

Only the Python standard library is used. The report can be rebuilt with:

    python3 build.py

This requires an installed TeX distribution. The build helper first tries
normal pdfLaTeX, and if installed format/cache files are missing, builds a
private format from installed TeX sources. It downloads nothing and changes
no global TeX configuration.

Check or compile an individual certificate:

    python3 code/equation_back.py < tests/equation/transport_beneath_D.json
    python3 code/crossed_back.py < tests/crossed/transport_beneath_D.json
    python3 code/compile_equational.py < tests/source/transport_beneath_D.json
    python3 code/compile_crossed.py < tests/source/transport_beneath_D.json

The compilers print JSON certificates, not acceptance decisions. The standalone
checkers are authoritative. For open inputs use the documented Python derive
API with a well-formed context and scope; see tests/open/ and verify_compiler.py.

VALIDATION STATUS

19 closed translations; 13 open translations; 150 checker subprocess runs
in the compiler suite. The primitive suite adds four open crossed examples,
five exact two-crossed simulations, and 24 checker subprocess runs. All 174
process runs passed, including normal and optimized Python. Separate
mathematical and implementation reviews are included. The work is not formally
verified in Lean or Rocq; finite tests do not replace the general written proof.

INPUT CONTRACT AND LIMITS

Each checker validates the entire closed native goal and every consumed term,
formula, rule premise and scope constraint. An antecedent-free Use ignores its
premise placeholder. Such unused payload is not a false-proof loophole and is
discarded by the crossed converter. No extra grammar validator is omitted
from the measured checker.

Completeness concerns ideal finite executions without fixed memory/stack
limits. A physical Python run can reject a sufficiently deep valid certificate.
The transparent tree compiler can substantially duplicate proofs; no polynomial
size bound is claimed. In one fixture 47 source nodes become 329 equation-only
nodes and 148404 crossed nodes.

All source adaptations use the included MIT-0 license. Pinned reference
provenance is retained separately from the new proof and implementation.

Closing repository check
------------------------
At revision c0c9ef353e9ac3c877c9c5cb37354e1721baada4, the cited open
question and selected compact 239-token, 256-AST, 461-byte sources have the
same Git blob hashes as the pinned baseline. A newly integrated validated
profile reports 597 bytes. The main report's measurements are explicitly
pinned, not claims that its 599-byte validated representative is still the
latest. The closing receipt records these facts and the reported new metrics.

Rejected compact-checker experiment
----------------------------------
experiments/rejected_match_guard contains an explicitly UNSOUND 255-node
variant and the guarded false-goal certificate it accepts. It is included
only to document why that apparent improvement was rejected. It is not
one of the proposed checkers and must not be used to certify theorems.
