# Rational-rotation family: research packet

Primary result: `PROOF.md`. It independently derives the arbitrary-rational-rotation five-live-signal family, exact complete-word chamber and infinite-validity set, rational/integer sign obstruction, fixed-machine polynomial-time rational membership, optional rational scaling/Zeno classification, and a literal fixed-arity degree-12 certificate.

This is distinct from the single machine in Reports57/58. For the same (3,4,5) rotation, the present smaller shear steps produce a different chamber and 174 half-scaled events, rather than the earlier 138-event machine. No previous reports were edited.

## Files

- `static_family.py`: newly written exact symbolic endpoint and static grammar constructor
- `evidence/STATIC_RECEIPT.json`: 45 fixture summaries with hashes and exact parameters
- `evidence/a*_scale*.json`: complete guards, rules, phase ranges, speeds, return/duration rows and tangencies for each fixture
- `arithmetic_review/ARITHMETIC_REVIEW.md`: independently written family arithmetic review
- `arithmetic_review/*checks.json`: fresh exact and sparse-polynomial receipts
- `arithmetic_review/check_*.py`: newly owned arithmetic checks, copied after their author executed them in the separate review directory
- `PRIOR_WORK.md`: primary-literature and pinned connected-repository comparison
- `inert_sources/pell-source.lean`: pinned constructive theorem source, read only, not executed
- `SOURCE_PINS.json`: provenance and source SHA-256 values
- `PACKET_MANIFEST.json`: final file hashes, excluding the self-referential manifest itself

## Status and limitations

The mathematical proof is conventional. The finite static fixture checks do not replace its parameterized argument. The number-theoretic family has an independent arithmetic review, but the new physical family still awaits the root-assigned adversarial audit. The polynomial-time and arbitrary-positive-rational-scaling statements are included in the audit scope.

There is an implemented physical static constructor, but no general emitted arithmetic circuit/DAG frontend and no source-specific arithmetic gate count. The arithmetic witness/equation counts refer to the explicit finite formula. No generic MRDP, witness uniqueness, semialgebraic classification, arbitrary-matrix compilation, novelty, minimality, or undecidability claim is made.

No old executable, upstream program, physical simulator, or saved collision schedule was run. Sources were inspected as inert text. The implementation creates endpoints by composing rational linear forms and expands a finite event grammar only.
