Frozen checker frontier, inspected 2026-11-12
===========================================

Repository: VladimirReshetnikov/ProveIt
Snapshot: e85c5e24dba535a296c46cd18fa66a146ce36b8e
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The five modules in code/ are UNCHANGED UPSTREAM CHECKERS. They provide
the comparison baseline; they are not a new result of the accompanying
research. They import no file from this package.

Program             Tokens    AST nodes    Normalized UTF-8 bytes
compact479.py         272        304                 479
tokens244.py          244        272                 608
ast267.py             249        267                 606
native607.py          337        383                 607
strict637.py          344        392                 637

The compact coordinatewise minima (244,267,479) are attained by THREE
DIFFERENT PROGRAMS. They are exhibited upper bounds on unknown optimal
checker sizes, not proved mathematical lower bounds.

Contracts differ. The three compact modules assume a canonical closed
guarded Eq/D public formula and an integer/list proof alphabet; they check
scope but are not full public-grammar validators. tokens244.py and ast267.py
read one JSON value per requested physical line. Their fresh-parameter
conventions differ, so they require their respective stream fixtures.
compact479.py reads one whole JSON array, consumed from the end.

native607.py validates the full native Eq/D public grammar, while retaining
the consumed integer/list proof contract. strict637.py additionally checks
the whole input alphabet and is the appropriate interface for arbitrary
input. It uses whole-array JSON framing.

Run with CPython 3.12.14:

  python3.12 verify_baselines.py
  python3.12 code/strict637.py < fixtures/strict_proofs/computation_zero_local.json
  python3.12 code/tokens244.py < fixtures/stream_global/computation_zero.jsonl

Successful checking prints exactly ACCEPT and exits with code zero.
Every other outcome is rejection. The verification utility remeasures the
complete normalized modules and runs retained positive and negative cases
normally and under Python -O. It also checks source SHA-256 identities.
The recorded run executed 266 processes with no unexpected verdicts.
Finite regression evidence is not a proof of unrestricted soundness.

frontier_census.json records contracts, metrics and source archive members.
archive_census.json records the sizes and SHA-256 hashes of all ten incoming
ZIP archives present at the pinned snapshot (12,228,231 bytes in total).
verification.json records the new local regression execution. The older
INHERITED_PROOF_NOTES.txt explains the inherited implementation simulations;
it was copied unchanged and is not a new proof.

Small helper scripts and compressed-source exec wrappers are not direct
proof-checker contenders under this comparison. In particular the incoming
reference corpus contains 459-byte compression wrappers. A literal-byte
comparison allowing such wrappers is a DIFFERENT accounting contract and
must not report 479 as its global minimum.

No new below-frontier standalone checker was verified in this work. The
accompanying predecessor result concerns arithmetic term size and does not
reduce any of the five checker modules above.
