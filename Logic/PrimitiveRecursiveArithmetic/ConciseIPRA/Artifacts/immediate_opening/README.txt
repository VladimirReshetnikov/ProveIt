AN EXACT 479-BYTE REFINEMENT OF THE CONCISE iPRA CHECKER
Prepared for Vladimir Reshetnikov, 12 November 2026

READ FIRST

This is a verified improvement of the existing compact checker's byte
coordinate, from 487 to 479 normalized bytes. It preserves the same input
contract and every proof rule. It is not a new mathematical axiom basis,
does not beat the separate 248-token and 270-AST records, and does not prove
absolute minimality. The broader requested research target remains open
in this work. The observed family envelope becomes (248, 270, 479), in
different programs.

The comparison is pinned to ProveIt commit:
36d37fc1071fe289371f6bcd7dcfa0eac593a5a6
under Logic/PrimitiveRecursiveArithmetic/ConciseIPRA, including all nine
archives in docs/incoming at that commit.

CONTENTS

report.pdf / report.tex
    Report with explicit native rules, the public-interface restriction,
    both whole-domain interpretations, exact implementation proof,
    measurements, and attributed foundational appendices.
notes/preservation_and_scope.tex
    The new preservation proof and the scope-phase obstacle.
reference/*.tex
    Five inherited mathematical sources, reproduced verbatim. Their
    SHA-256 values and archive members are in reference/provenance.json.
code/checker479.py
    Complete compact byte-record program: 272 tokens, 304 AST nodes,
    479 normalized bytes under CPython 3.12.14.
code/checker_readable.py
    Standalone explanatory expansion of exactly the same protocol.
code/checker_strict.py
    Standalone strict integer/list and guarded-public-goal validator
    followed by the exact candidate kernel. This larger program is not
    the byte record.
controls/
    Exact frozen source programs used in the comparison.
verification/
    66 frozen fixtures, hash/provenance/expected-verdict manifest, and
    portable regression script. See verification/README.txt.
evidence/
    Source census, archive provenance, measurements, and verification
    receipts. The original 260 executions plus 178 companion executions
    cover the full 438-execution reproduction set without a duplicate run.
measure.py / build.py
    Offline measurement and LaTeX build commands.
provenance.json / STATUS.json / MANIFEST.sha256
    Scope of the claims, provenance, and final archive-member hashes.

REPRODUCTION

Use CPython 3.12.14 for the exact metric convention:

    python3 measure.py
    python3 verification/verify.py
    python3 code/checker479.py < verification/fixtures/byte/context/computation_zero_local.json
    python3 build.py

The checker prints ACCEPT followed by one newline only on successful
completion. Certificates are consumed from right to left. The compact
program assumes a canonical closed guarded Eq/D public goal and finite
integer/list certificate data. Use checker_strict.py to enforce those
public input requirements. An unused instruction prefix is permitted,
as in the old program. The compact candidate retains multiline JSON;
the inherited token and AST controls use one physical input line.

The reproduction script's default run performs 438 isolated executions.
The --companions-only option repeats only the new 178-execution receipt.
Finite tests supplement the universal local-transformation proof. They
are not an end-to-end formal verification of the Python checker or a new
proof-assistant development of the arithmetic bridge.

The whole source census is preserved as evidence. Recomputing it requires
the pinned repository checkout:

    python3 evidence/census.py --repo /absolute/path/to/ProveIt

The mathematical bridge and its native Lean formalization are inherited
and attributed. The Lean development was not rebuilt for this report.
The ordinary realization explicitly retains the falsity bridge
(0 = S(0)) -> bottom. Neither theory is claimed to prove its own consistency.
