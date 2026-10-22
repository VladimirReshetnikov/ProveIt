# Provenance and scope

This prototype is based on ProveIt commit
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

The copied reference semantics, arithmetic coding, candidate program literals,
and macro proofs retain their original source comments. Their source paths and
SHA-256 values are in `evidence/source-audit.json`. The three reference modules
`RM`, `Codes230`, and `KCode230` are identical to the files saved in the
repository's completed Rocq endpoint evidence archive after CRLF-to-LF newline
normalization. No definition, theorem, or import was changed for Coq 8.18.

The new local transport proof follows the design of the maintained Lean
`BusyBeaver/ZFC/RMTransfer.lean`. Its application to the canonical 89-node
Rocq macro footprint is new in this packet. The arithmetic and macro proofs
themselves are reused from the existing `ProgLibPerm.v`; they are not claimed
as new mathematical derivations.

The source comments credit Elliot Glazer's K230 development, Jeff's pinned
m254 arithmetic and program proofs, and Andrew James Wade's TMBuilder
architecture. ProveIt contributor work is covered by the repository's MIT
No Attribution terms. The inherited license and provenance notices are
retained in `licenses/`. Broader third-party notices describe upstream
components; this small build does not import BusyCoq or the Coq Library of
Undecidability.

No candidate transition table, enumerator, theory, or existing production proof
is modified. This is a component-level prototype, not a newly checked final
ZFC endpoint or a smaller Turing machine.
