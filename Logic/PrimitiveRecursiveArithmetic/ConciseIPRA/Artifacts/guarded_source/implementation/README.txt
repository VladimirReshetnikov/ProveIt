EQUATIONAL BOOTSTRAP AND A DETERMINISTIC GUARDED iPRA CHECKER

Pinned comparison: ProveIt commit
1517d9d79ce33f631e0f82960c849427cbba23bf.

Mathematical contribution
-------------------------
The literal-zero-source transport reduction can be proved in a purely
equational fragment with contextual equation induction. Logical case
introduction is unnecessary for that proof. This removes the apparent
dependency cycle when combining source_dispatch with guarded_core.

The resulting proof calculus has a deterministic introduction mode and
a source-determined elimination major. It is sound in iPRA for all decoded
administrative certificates and complete for the same canonical guarded
formulas as guarded_core. The full proof and its exact limitations are in
COMPATIBILITY_NOTES.md. The numerical signature and domain are unchanged.

Selected complete standalone checkers
------------------------------------
                                Tokens    AST    Bytes   gzip9
exactroot_checker_tokens.py        257     285     568     338
exactroot_checker_ast.py           261     279     603     345
exactroot_checker_bytes.py         264     301     522     328
exactroot_strict_checker.py        490     561    1202     571

The three small profiles are different programs. The attained minima
over them are 257 tokens, 279 AST nodes, 522 normalized bytes, versus
259, 283, 526 for the pinned source_dispatch profiles. No one program
attains all three new minima; no absolute minimality is claimed.
The gzip sizes use normalized source, level 9 and mtime=0, for information.

The compact contract assumes a canonical closed guarded goal. It permits
administrative formulas inside certificates and is not a goal validator.
The strict checker includes and charges a closed canonical-goal validator.
It uses the same local certificate protocol as the byte/AST profiles.

Run a supplied certificate:

    python3 exactroot_checker_bytes.py < composed_tests/zero_transport_guarded_D_local.json

Reproduce the proof transformations, source metrics and process checks:

    python3 reproduce_composition.py

The token profile uses global fresh-name certificates; the byte/AST/strict
profiles use local lexical certificates. Both encodings are generated.
The checkers themselves import only Python's JSON library. Neither a proof
producer, database nor test fixture is loaded by a checker.

Validation
----------
validation.json records 150 executions in regular Python and -O:
92 expected acceptances and 58 expected rejections, with no failures.
Tests include both computation schemas, transport, progress with a used
induction hypothesis, compound case introduction, elimination, zero-source
transport beneath a guarded D, a guarded Q resource and a compound D,
incorrect endpoints, missing data, false goals, escaping names and leaked
contexts. The named-proof audit checks zero-source elimination and the
deterministic introduction modes. These are finite executable checks, not
a proof-assistant verification of universal metatheorems.

Provenance and inherited work
-----------------------------
PROVENANCE.json records pinned source paths, Git blob IDs and checked
local hashes. The source_dispatch/ and guarded_core/ test producers and
baseline checker files are copied from the user's repository; their
mathematical constructions are inherited. The new proof transformation
is composition_producer.py, which explicitly refuses unsupported raw
unguarded atomic binder transports. The small exact-root test is an
implementation cleanup after the compatibility theorem.

Python and zlib versions, normalization and gzip settings are recorded
in metrics.json. Physical memory and recursion limits may reject large
finite valid certificates; acceptance is exactly normal termination
with the line ACCEPT. The mathematical theorem refers to finite proofs
in the ideal unbounded calculus.
