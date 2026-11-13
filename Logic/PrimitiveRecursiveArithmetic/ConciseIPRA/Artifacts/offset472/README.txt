A 472-BYTE CHECKED PRESENTATION OF iPRA
=====================================

Read ipra_offset472.pdf, or its standalone source ipra_offset472.tex.

RESULT AND LIMIT

The complete direct-source checker offset472.py measures:
    271 significant Python tokens / 307 AST nodes / 472 normalized bytes.
The exact current matched byte control measures:
    272 tokens / 308 AST nodes / 473 normalized bytes.

This improves only the byte coordinate of the current separately attained
243-token / 264-node / 473-byte envelope. The new envelope is 243/264/472,
attained by different programs. The mathematical axioms and rules are the
established guarded-source presentation. The new result is a verified
representation refinement, not a new axiom deletion or global minimum.
Compressed execution wrappers form a separate source-accounting class.

THE CHANGE

Reserve two extra positive depth positions in the sorted syntax encoding:
formula-root depth 0 becomes 2, numerical-root depth 3 becomes 5, witness
opening 2 becomes 4, and bound-slot coordinates 3+2j become 5+2j. Literal
zero and negative eigenparameter names remain unchanged. Parity, arity
increments, scope floors, arithmetic and logical inference are preserved.
Scalar 0 now passes initial scope validation, so the neutral context can be
[0] instead of [[]]. That removes one token, one AST node, and one byte.
Changing the initial context alone without the depth shift would fail.

The report states every primitive rule, proves the shifted decoding and
checking claims, and explains both full iPRA interpretation round trips.
The numerical domains remain whole and the comparison graphs remain x=y.
The arithmetic/logical bridge is inherited from the pinned repository;
its exact current base chapter and Lean theorem statements are included.
The shifted Python checker is not newly formalized in Lean or Rocq.

INPUT CONTRACT

Input is one finite JSON array used as a stack. Its final element is [A,0],
where A is a canonical CLOSED GUARDED PUBLIC Eq/D formula in the shifted
codec. All certificate data are finite exact-integer/list trees. Consumed
preceding instructions have four fields [m,s,u,t]. Unused prefixes are
permitted. Normal termination printing exactly ACCEPT and a newline
accepts; exceptions reject. The compact checker does not independently
validate the promised public grammar or alphabet. Physical resource limits
are separate from mathematical completeness for finite ideal executions.

MAIN FILES

ipra_offset472.pdf / .tex   Complete report, construction, proofs, comparison,
                           interpretation bridge and further questions.
offset472.py               Entire measured checker, no private dependencies.
checker_readable.py        Readable equivalent on the promised input contract,
                           with exact evaluation order made explicit.
control473.py              Exact current matched control, not reimplemented.
translate_certificate.py   Utility for canonical old-codec certificates;
                           no universal raw-language equivalence is claimed.
verify_offset.py           Exact edits, source metrics and isolated regressions.
offset_verification.json   Verification receipt: 102 cases, 612 executions,
                           zero failed expectations, ordinary and -O Python.
OFFSET_PROOF.txt           Detailed independent written decoding/checking audit.
SOURCE_PROVENANCE.json     Exact pinned source, archive and source hashes.
CLAIMS.json                Machine-readable claims and limitations.
fixtures_original/        Inherited examples and adversarial regression cases.
fixtures_offset/          Shifted counterparts, including direct_zero_seed.json.
reference/                Attributed inherited mathematics and metric controls.
evidence/                 Current incoming-archive identities and source census.
MANIFEST.sha256            SHA-256 inventory of the complete package.
LICENSE.txt               MIT No Attribution license for the supplied material.

REPRODUCE

From this directory, using Python 3.12.14 for identical measurements:

    python3 verify_offset.py
    python3 offset472.py < fixtures_offset/direct_zero_seed.json
    python3 translate_certificate.py < fixtures_original/direct_zero_seed.json

The verification uses only the Python standard library and tests ordinary
and optimized execution. Some malformed-data regressions are intentionally
outside the formal compact input contract. Tests do not prove universal
soundness; that argument is in the report and OFFSET_PROOF.txt.

The TeX source embeds the measured code and is self-contained:

    latexmk -pdf -halt-on-error ipra_offset472.tex

The compiled PDF is already included. Files under reference/ are inspection
sources and are not extra LaTeX build targets or checker dependencies.

SOURCE SNAPSHOT

VladimirReshetnikov/ProveIt
6c6a164d211f0af34e913d55c9f46f8ef7cb560f
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Eight current incoming ZIPs were matched to their Git blob identities.
The byte control is the member
ipra_vacuous_specialization/compact/checker473.py
of docs/incoming/ipra_vacuous_specialization_2026-11-12.zip.
Its SHA-256 is
282c2165b84b96957b12390ebb2f12ba6f24080396f9802ece080d914555c026.
The candidate SHA-256 is
c0e3766bfa73b0edd7c88c828ca5d7917f2f3dd99f7142bfe8dcf3996772b682.

No changes to the remote repository are part of this deliverable.
