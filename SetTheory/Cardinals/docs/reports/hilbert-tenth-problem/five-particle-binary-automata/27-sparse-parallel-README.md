# Sparse evaluator for the new parallel particle CA

A bounded research companion to the two-involution construction. This packet
implements the **new** CA on every finite particle support, without building
its potentially enormous endpoint-template arrays. It is separate from the
old ordered evaluator and intentionally differs on malformed inputs.

## Main result

- Exact finite-support equality to the new eager interpreter, forward/inverse
- All raw type/anchor keys and both orientations, including malformed supports
- Exactness plus guards, within-family all-type exclusion, prospective
  key-set preservation, then one simultaneous rewrite per block
- At most n+2 raw-discovery calls per n-particle step; at most 2n+4 with
  verification. These bounds count candidates rejected after prospection too
- Metadata-sized compilation; runtime polynomial in particle count,
  coordinate/source bit lengths, and metadata/class descriptors, without an
  F-long cascade or F-element allocation
- Explicit caveat: class descriptors still cost O((p+a)(J+2)^2); this is not
  polynomial in log J when J is supplied in binary

## Files

- `sparse_parallel.py`: new immutable compiler and finite-support evaluator
- `PROOF.md`: complete discovery/equality/resource argument and limits
- `audit-candidate-completeness.md`: independent formulas/code/resource audit
- `test_sparse_parallel.py`: eager differential, malformed, locality, and API tests
- `audit_candidate_completeness.py`: independent all-index and guard checks
- `benchmark_universal.py`: frozen-source startup and malformed-state runs
- `universal-source.json`: pinned 122,622-control source, 32,034,272 bytes
- `frozen-ordered-startup-trace.json`: pinned comparison on valid startup states
- `parallel_particles.py`: unchanged small-source eager new-rule oracle
- `PARALLEL_*.md`: unchanged new-rule theorem and its independent audits
- `COMPILER_PROOF.md`, `SOURCE_SCHEMA.md`: unchanged inherited source background
- `frozen_lazy_source.py`, `frozen_reversible_binary.py`: unchanged pinned
  local-authored source metadata dependencies; old execution is not called
- `RESULTS.md`, JSON receipts, logs: measured bounded evidence
- `PROVENANCE.json`, `manifest.json`, `SHA256SUMS`, `verify_bundle.py`: provenance
  and replay integrity

## Replay

Python standard library only. No network or sibling directory is needed. All
paths resolve relative to the scripts. To preserve the packet bytes, choose
an external output directory and disable bytecode writes:

    python -B verify_bundle.py
    python -B test_sparse_parallel.py --output-dir /tmp/sparse-parallel-replay
    python -B -O test_sparse_parallel.py --output-dir /tmp/sparse-parallel-replay
    python -B audit_candidate_completeness.py --output-dir /tmp/sparse-parallel-replay
    python -B -O audit_candidate_completeness.py --output-dir /tmp/sparse-parallel-replay
    python -B benchmark_universal.py --output-dir /tmp/sparse-parallel-replay
    python -B -O benchmark_universal.py --output-dir /tmp/sparse-parallel-replay

Main differential runs take roughly one minute each here. Universal startup
requires approximately 370 MiB peak process memory and several seconds for
source metadata, then well under a second for the bounded steps; timings vary.

## API and semantic boundary

Create `a = SparseParallelCompiler(source_dict)` and use `a.step(particles)` or
`a.step(particles, inverse=True)`. `verify=True` checks mass, key preservation,
selection symmetry, and each block's involution. `trace=True` returns the
support and immutable `StepTrace`/`BlockTrace` records. `a.encode(...)` encodes
five-particle source states; `a.E` and `a.P` expose block candidates, selection,
application, and the certified local-output oracle. `a.gate_at(i)` materializes
one endpoint template. E/P key IDs share a global E-then-P naming space.

The `.metadata` field is the pinned legacy metadata object. Its inherited old
execution methods are not the new CA API; use the enclosing compiler's
`step`. Counts named `E`, `P`, and `factors` in ledgers count endpoint types,
not sequential operations of the new rule. A fresh mutable ledger dictionary
does not expose mutable compiler state.

Position inputs must be exact sets/frozensets of exact integers; flags must
be exact Booleans. Empty supports and arbitrary signed integer coordinates are
valid. All validation survives `python -O`. Only source-derived immutable
guards are supported.

The frozen source has F=269,291,358,255 endpoint types but radius 91,711,698.
The benchmark executes 128 literal startup steps and 128 malformed cases; it
does not complete the long startup, a whole Turing step, or a halting proof.
No eager universal oracle or full local truth table is emitted. Whole-family
parallelism and the n+2 call bound do not mean two constant-cost arithmetic
instructions. This is a proof plus bounded executable corroboration.

The unchanged inherited documents retain references to their original packet's
filenames and tests. Here `PARALLEL_RULE_PROOF.md` is that packet's `PROOF.md`,
`PARALLEL_LEMMA_AUDIT.md` is `audit-lemma.md`, and
`PARALLEL_PRESERVATION_AUDIT.md` is `audit-preservation.md`. Their prior test
counts describe their own frozen packet; this packet's executed evidence is
listed in `RESULTS.md`.
