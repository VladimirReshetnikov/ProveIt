# Automatically inferred K215 source correspondence

This package synthesizes a 1,426-entry source certificate from the two literal
decoder trees, materializes it as an untrusted cache, and proves the all-register
source equivalence using the established normalized checker:

```lean
theorem source_halts_iff (R : Registers) :
  Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩
```

The concrete statement is in namespace
`SetTheory.BusyBeaver.ZFC.KSource215Auto`. The full binary-machine/ZFC endpoint
is outside this standalone build.

## New contribution and inherited work

`RMAutoCertificate.lean` traverses decrement/halt leaves in left-to-right order,
pairs their consumed paths, computes successor ranks from the first source,
and constructs a candidate relation. It is a heuristic: failure to find the
right relation does not imply that two programs differ. The proved normalized
checker validates the generated relation against **both** sources.

`KSource215AutoEmit.lean` runs this generator in Lean and emits literal balanced
certificate blocks. Correctness of this executable is **not assumed** by the
semantic theorem. The final proof only uses the kernel-checked initial and
entry obligations. A wrong generator can cause rejection; it cannot bypass
the checker. No equality between the cache and generator is needed as a premise.

The trailing-zero normalization idea, existing `RMNormalizedBisim.lean`, exact
shared trees, program data, and their well-formedness/tree bindings are inherited
from `docs/incoming/K215_Proof_Simplification_2026-10-21.zip`. The canonical
weighted-graph observation also appears in the structural incoming proposal.
The new work here is automatic inference plus executable staging and its exact
source instantiation, not discovery of the 1,426-entry quotient.

The eight core source/DAG modules are byte-identical to ProveIt commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959`. In particular, the current phase-four
`RMBisim.lean` is used. `SOURCE_BINDINGS.json` also binds the literal `p215Nodes`,
`p215`, `pathDagPerm`, and the three inherited metric lists to the same commit.
The imported shared-tree module proves the exact decoder-tree identities in
the kernel; hashes are provenance, not semantic premises.

## Fresh reproduction

With Lean **4.32.0** and Python 3, from this directory:

```sh
python3 build.py --lean /absolute/path/to/lean --out /tmp/k215-auto-fresh
```

The output directory must initially be absent. The driver:

1. Copies sources into the fresh output directory.
2. Compiles every project dependency from source.
3. Runs the Lean emitter to synthesize the certificate.
4. Compiles sixteen `decide +kernel` acceptance blocks and the final theorem.
5. Records exact source/object/log hashes, toolchain version, time, and memory.

The standard Lean installation supplies the standard library; no project
`.olean` is distributed or imported from another build. The default memory
limit is 4,000 MiB. A resource-interrupted build can be continued with `--resume`;
it checks source, object, and log identities of each successful earlier module
before reusing it within that same build. No unbound preexisting object is
accepted. The delivered receipt distinguishes the resource retries.

`verification/receipt.json` and its logs record the actual completed validation.
`verification/entries.json` contains a readable generated relation and
`verification/emission.json` the exact row/block counts. These are supplementary
artifacts; the proof checks the generated Lean data directly.

## Why staging matters

The first experiment defined each block by reducing the entire inferred list.
Executable checking accepted it, and three kernel blocks passed, but block four
exhausted a 3,000 MiB cap. The failed experiment and log are retained under
`experimental/`. Its final source theorem is not claimed to have compiled.

The staged implementation avoids repeating inference during kernel reduction.
Blocks 11 through 15 additionally use the incoming proposal's quarter-block
kernel batching. This is a resource-management technique, not a new proof idea.
The generated literal certificate remains visible and independently checkable.
It is 108,231 bytes; removing the need to maintain it manually is the relevant
simplification. This is not a claim that total source bytes or whole-project
build time decrease. See the receipt for measured costs and the report for the
distinction between normalized checking, inference, and certificate caching.

The active proof files contain no `sorry`, `axiom`, or `native_decide` proof.
The printed final assumption list is retained verbatim in the final theorem log.
Standard Lean foundational axioms appearing there must not be described as a
closed Rocq global context; the two assistants report different foundations.

## Integration

The current K215 facade can import `KSource215Auto` and define its existing
`p215_halts_iff R` by `KSource215Auto.source_halts_iff R`. Update its generator
and dependency manifest accordingly. This standalone packet does not claim
that the remaining production machine/ZFC closure has been rebuilt.

Inherited attribution and license material is retained in `licenses/` and the
top-level packet notice. The new contribution is intended for incorporation
into ProveIt under the project's MIT No Attribution terms.
