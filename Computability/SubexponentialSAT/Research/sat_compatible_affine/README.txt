COMPATIBLE AFFINE CONTRACTION PLANS FOR 3-SAT
Research memorandum prepared for Vladimir Reshetnikov
26 October 2026, Pacific time

RESULT

For the same normalized general-degree cached tensor-contraction interface
as the strongest reviewed incoming proposal, the certified time and space
coefficient is reduced from 29.81160894538347 to

    C = (pi / ln(2)) * sqrt(23343389777236 / 564375000000)
      = 29.148921368872137575...

The coefficient multiplies s / sqrt(log2(s)) in a base-two exponential,
where s is the normalized Boolean-wire budget, not the SAT variable count.
A safe eventual coefficient is 29.149. Initial maximum degree is at most
ceil(s^(9/10)), with the precision, entry access, and imported exact
contraction identities specified in the report.

This improves an explicit asymptotic upper-bound coefficient by about
2.223%. It does not improve the logarithmic order of unrestricted 3-SAT:
the supported general exponent order remains n loglog(n) / sqrt(log(n)),
with the existing density-sensitive refinement. This cached algorithm
uses subexponential space. It does not dominate the existing lower-space
or polynomial-space branches in all resource comparisons.

WHAT IS NEW

1. Twelve ten-group plans from the affine plane F_3^2 plus a tenth vertex.
2. A compatible-support certificate: one operation choice per plan stays
   consistent throughout all pair comparisons. Independent pair maxima
   can charge mutually incompatible choices and are less sharp.
3. A three-piece rectangular cost envelope using an interior interpolated
   anchor from published matrix multiplication bounds, with strict slack.
4. An exhaustive improvement of the thirteen-group middle-stage certificate.
5. A completely paid recurrence with root 29.148921368872138, middle stage
   29.00088217429141, and infinite tail 29.06574852464126.
6. An exact restricted optimum for the preceding nine-plan envelope, and
   scoped obstructions to several proposed changes of logarithmic order.

The new root plans alone give 29.6406449072 with the previous matrix
backend. The final result combines all the improvements above.

CONTENTS

report.pdf                  Complete proof and review, including appendices.
report.tex                  Main LaTeX source.
sections/                   All local LaTeX section sources.
verify_all.py               Reproducible verification entry point.
code/                       Standard-library Python checkers and inputs.
results/                    Frozen certificate outputs and replay records.
provenance/                 Pinned commits, source/archival hashes and review.
audit/                      Supporting proof and formalization review notes.
PROOF_STATUS.json           Machine-readable scope and claim boundaries.
build_report.py             Offline PDF build using pdflatex.
check_manifest.py           Verify shipped file identities.
MANIFEST.json               SHA-256 and byte length of each shipped file.

REPRODUCE

Python 3.10 or newer is sufficient; the recorded runs use Python 3.12.
No third-party Python packages or network access are needed for the checks.

    python3 verify_all.py

This runs all checks in a temporary work directory, compares the exact
generated results with the supplied references, and removes temporary
outputs. The separate independent root replay is the slowest step.

    python3 verify_all.py --quick

This skips only that independent root replay. It is useful for a short
inspection but does not replace the complete check.

    python3 -O verify_all.py

Optimized mode propagates to every child process. Acceptance conditions
use explicit exceptions; disabling assertions cannot remove them.

    python3 verify_all.py --output replay.json

This additionally saves a replay summary at the chosen path. Individual
checkers and their input conventions are described in code/README.txt.

To rebuild the PDF, install a standard TeX Live distribution including
the packages listed at the top of report.tex, then run:

    python3 build_report.py

The build makes three LaTeX passes, checks for unresolved references and
overflow warnings, and replaces report.pdf. Rebuilt PDF bytes can differ
because of PDF metadata and local TeX versions; this is not a mathematical
verification failure. The shipped report was also rendered and visually
inspected. Run the identity check before rebuilding:

    python3 check_manifest.py

WHAT THE CHECKS PROVE

Two independently written generators and searches reconstruct the root's
1,152 indexed supports and its exact maximum squared norm. The producer
uses incremental conditional sums; the independent checker recomputes
prefix bounds directly. They certify all 96^12 choices through valid
elimination and branch bounds, visiting 303,513 nodes.

Two independent thirteen-group generators enumerate all 2,299,968 triples.
The schedule checks use arbitrary-precision integers, rational arithmetic,
and certified intervals for pi, ln(2), and square roots. Eight scalar
fixtures over Z/8Z give 96 comparisons against direct enumeration, plus
empty-allocation and exact selector checks.

WHAT THE CHECKS DO NOT PROVE

They do not rebuild the imported deformation, interpolation, coefficient
ring, entropy, and packing theorems. Those are explicit dependencies.
They do not implement asymptotically fast matrix multiplication or a full
3-SAT solver. No solver runtime improvement has been measured. No new
Lean formalization of these certificates is included. The linked Anthropic
formalization was inspected at its exact commit and its successful CI
record; Lean, Comparator, and nanoda were not independently rebuilt here.

The old-menu optimum and uniform-entropy bound are lower bounds for
specified analytical cost envelopes, not lower bounds for SAT algorithms.
The local obstructions have explicit hypotheses and documented escapes.
No global optimality, literature-wide novelty, or smaller SAT exponent
order is asserted.

FROZEN SOURCE BASELINE

ProveIt: 8e76d515063c4b9fbd8743a846b457e3a01bc039
Latest incoming addition: 26bd83d4b37d3c5a3ccb45bab2e6385fae3977f1
Anthropic: 1a6eee293b9e00cb432eef6018a21f523623a9af
Matrix dependency: arXiv:2307.07970v2, Table 1 (SODA 2024).

Source URLs, exact archive hashes, selected file hashes, relevant commit
history, and comparison premises are supplied under provenance/ and in
the report bibliography. No remote repository was modified.
