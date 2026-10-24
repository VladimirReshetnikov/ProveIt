# Attribution and scope

This research package was prepared for Vladimir Reshetnikov with ChatGPT
assistance for possible incorporation into ProveIt. The report records the
ordinary mathematical argument, exact output equations, and the limits of the
finite verification. It does not assert historical priority or global
optimality.

The direct numerical C222 calculus, its ZF/ZFC refutation calibration, the
eight-column proof-row projection, the Horn-flow construction, the prime-power
CRT lift, the existing arithmetic interfaces, and the three-square conversion
have explicit predecessors in ProveIt. The inspected repository commit and
incoming archive checksum are in `provenance/SOURCE_METADATA.json`.
`source/horn_shared_source.json` is retained from the inherited literal source.
`source/build_direct.py`, `signed_backend.py`, `positive_arithmetic.py`, and
`polynomial.py` retain or adapt that construction. The source and domain changes
are described in the report and `proofs/SOURCE_AND_DOMAIN_AUDIT.md`.

The contributions developed for this package include simultaneous shared Pell
certificates, the common output-bound argument, signed positive-index recovery,
exact neighboring-exponent reuse, their synthesis with signed row evaluation
and an absolute majorant, and the two fully materialized quartics. Separate
checkers and review notes document the finite interfaces and ordinary proofs.

The ProveIt material retains its upstream MIT No Attribution license, reproduced
in `LICENSE.upstream`. The copied Mathlib source retains the copyright header
of Mario Carneiro and its Apache 2.0 license in `provenance/LICENSE.mathlib`.
The copied Mathlib file has the exact pinned Git blob recorded in the provenance
metadata. The Lean excerpts retain their source declarations and imports;
this directory is not presented as a complete compilable Lean project.

`proofs/INDEPENDENT_BATCH_REVIEW.md` is explicitly labeled as a historical
review of the stronger positive-progression certificate. Its signed successor
is proved and independently reviewed in `proofs/SIGNED_INDEX_THEOREM.md` and
`proofs/SIGNED_INDEX_INDEPENDENT_REVIEW.md`. Current numerical claims are the
ones in the two `metrics.json` files and the release verification receipts.

The ordinary argument is intended to be formalizable in ZFC. No new end-to-end
Lean proof or encoded object-language ZFC derivation was emitted in this work.
Finite reconstruction and coefficient checks support the exact transcription;
the universal mathematical proof is not replaced by numerical testing.
