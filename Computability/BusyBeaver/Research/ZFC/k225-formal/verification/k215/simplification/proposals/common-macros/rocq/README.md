# One Rocq macro library from an 89-node footprint

Base: ProveIt `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

## Result

The entire 780-line maintained `ProgLibPerm.v` proof library compiles when its
program is replaced by a sparse canonical program with only 89 nontrivial
cells. The 58 theorems whose statements mention a literal node use 53 roots;
their descendant closure is exactly these 89 cells. The same cells appear
unchanged in the literal `DagPerm` (215 candidate) and `DagDom` (217 candidate).

`LocalProgram.v` proves a generic whole-node run-transport theorem, including
normal, break, continue, and halting exits. It preserves the exact starting
and resulting register functions. It also permits semantic contracts at
selected nodes, as in the existing Lean `RMTransfer` abstraction.

`Macro215Binding.v` and `Macro217Binding.v` kernel-check the literal node
bindings independently. The 215 contract dependency closure does not import
the 217 candidate. `MacroBindings.v` is an optional comparison module proving
that every finite run from a footprint node, with any registers and any exit,
is identical in the two structured program semantics.

`Macro215Contracts.v` derives all 58 concrete contracts for the exact literal
215 DAG by transport. This includes the branch-sensitive equality loop,
existential normal exit, unpairing, pair construction, arithmetic transfer
loops, formula constructors, and candidate fetch. The block contains no
repeated arithmetic induction.

## What the measurements mean

| Quantity | Observed value |
|---|---:|
| Maintained `ProgLibPerm.v` | 780 lines / 37,951 bytes |
| Maintained `ProgLibDom.v` | 781 lines / 38,002 bytes |
| Concrete macro declarations transported | 58 |
| Distinct literal roots in those declarations | 53 |
| Closed shared footprint needed by those roots | 89 nodes |
| Largest agreeing closed subset of the 484-node Dom program | 466 nodes |
| Concrete nontrivial cells in `MacroProgram.v` | 89 |

These are reuse and footprint measurements. This prototype does **not** claim
that the current 215 endpoint is shorter after simply adding these files.
The eight new `KLocal` source files total 1,300 lines / 61,524 bytes, including
the 780-line reused proof library, concrete wrappers, bindings, and assumption
reports. Its purpose is to replace multiple candidate-specific copies by one
owned library, after the API migration below. A full source-size comparison
must count that shared library once and include all adapters and generators.

The generic transport induction and finite table checks are small; the
mathematical macro proofs remain the existing proofs. The canonical program
has root 115 solely to satisfy the `prog` record. It is a library artifact,
not a candidate machine or a claim about the candidate's root 0.

## Reproduce

Tested with Coq 8.18.0 and OCaml 4.14.1. The maintained repository endpoint is
recorded as checked with Rocq 9.1.0; this component build does not substitute
for that pinned toolchain gate.

```bash
python3 build.py --build-dir build-checked
python3 audit_sources.py /path/to/ProveIt
```

The first command requires a fresh output directory, copies only source files,
builds all 13 project modules serially, requires 58 `Closed under the global
context` reports for the transported contracts, and recursively checks the
new public modules with `coqchk`. It records tool versions, exact source
hashes, commands, elapsed times, exit codes, and raw logs. It does not fetch
anything or invoke repository generators. The second command checks the
unchanged reference files, exact identifier-only macro-library transformation,
all 58 textual declarations, footprint closure, literal cell equality, and
identity with the recorded production reference definitions.

The saved final build receipt and logs are under `evidence/final/` in the
delivery. Generated `.vo`, `.glob`, and other build products are deliberately
omitted from the delivery; the build recreates them.

## Proof idea

For a predicate `ok` on node labels, an edge lies inside when it is a leaf or
its node label satisfies `ok`. A node is certified when its two program cells
agree and both children remain inside, or when a whole-node semantic
preservation theorem is supplied. Induct on a finite source run. Leaf cases
reuse the same primitive rule. Structural node cases rewrite the cell
equality and use the child induction hypotheses. The `continue 1` case also
reuses the induction hypothesis for restarting the same node, whose `ok`
hypothesis is retained. Contract nodes use their supplied theorem directly.

For the 89-node instance every node uses structural equality. A Boolean
checker checks the finite table and child membership, and a separately
proved soundness theorem turns its result into the `Closed` premise. Both
directions are checked to obtain exact local run equivalence. Python's
footprint generation is not trusted for soundness: the Coq kernel verifies
the resulting table-binding proof terms.

## Integration steps and remaining work

1. Move `St`, its operations, and the program-independent semantic utilities
   into an owned shared module; retain explicit compatibility names where
   downstream clients use them.
2. Keep the canonical arithmetic proofs once. Generalize sequence composition
   and expansion utilities over the candidate program, so clients do not
   accidentally use the canonical program's `sem` or `seqx`.
3. Put the 58 wrappers in one program-parameterized module or functor.
   Make `ProgLibPerm` and the matching Dom/219 libraries thin facades using
   the checked bindings and that shared contract module. Repeating the
   wrapper declarations for every candidate would reduce the size benefit. Update their producer
   templates at the same time; do not maintain a second hand-edited copy.
   The concrete producers are `rocq/rocq-extension/regenerate215.py` and
   `regenerate217.py`, which currently copy/rename `coq/218/ProgLib219.v`;
   `regenerate218.py` in turn derives that library from `ProgLib222.v`.
4. Rebuild `L2RootPerm`, its seed/main clients, and the complete exact 215
   endpoint using Rocq 9.1.0. Check public types, assumptions, and unchanged
   literal table hashes. Then count the total maintained source reduction.

The 58 transported declaration texts match their maintained counterparts,
but `MacroLibrary.St` is a different nominal record from the original
`ProgLibPerm.St`. Consequently the adapter is **not yet an audited drop-in
replacement**. The new all-register run-equivalence theorem does not depend
on that record choice. Root 0 lies outside the footprint; no equivalence
between the whole 215 and 217 enumerators is asserted.

Other recent proposals already address the implication core, candidate
scheduler, normalized source certificate, and semantic runtime sites. This
packet complements that work. The macro-word compression newly applied in
Lean should not be claimed as a missing Rocq feature: Rocq already has
`seqx`, `expand`, `run_seq`, and an eight-line `L2RootPerm.ax1` proof.
