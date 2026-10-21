# K215 proof simplification and positive-stuttering transport

Snapshot: `VladimirReshetnikov/ProveIt` commit
`b6c7087477e51c017003bd729e712c8969733223` (21 October 2026).

This packet contains two independent developments. Neither changes K215's
transition table or its calculus.

## 1. A checked general theorem for local machine transformations

`PositiveStuttering.lean` is a standalone Lean 4.32.0 development, importing
only `Init`. Its endpoint, `PositiveStuttering.Simulation.halts_iff`, is
kernel-checked and **does not depend on any axioms**. The compiler log is
`positive_stuttering_kernel.log`.

For deterministic partial steps `old : A -> Option A` and
`new : B -> Option B`, a possibly noninjective map `F : A -> B`, and a
source invariant `I`, the client supplies three facts:

1. A successful old step preserves `I`.
2. An old terminal configuration satisfying `I` maps to a new terminal
   configuration.
3. Every successful old step from `I` is simulated by a positive finite
   sequence of new steps, ending at the mapped successor.

Then, for every `c` with `I c`,

```text
Halts old c <-> Halts new (F c).
```

No target invariant, reverse simulation, injectivity assumption, uniform
block-length bound, or unbounded trace certificate is required. This is useful
for CM215's noninjective state map `176 -> 52`. The all-tape marker proof and
concrete table checks are supplied separately in the comparison packet.

The reason positivity matters is precise. Given a target halting run of length
`N`, a simulated source step consumes `m > 0` successful target steps.
Determinism ensures this prefix cannot cross the terminal point; it leaves a
halting suffix of length `N - m < N`. Strong induction yields source halting.
The forward implication concatenates the blocks. Allowing `m = 0` would let a
nonhalting source self-loop map to a terminal target configuration and invalidate
the conclusion.

`PositiveStuttering.v` is the same theorem for Rocq/Coq, using only the standard
library. It compiled with Coq 8.18.0 and printed a closed global context;
`coqchk` independently rechecked the compiled theorem. This is not a rerun
using the repository's Rocq 9.1.0 toolchain. `check_transport_coq.py` reproduces
the compile, assumption report, and independent checker with explicit exit codes.

To rerun the Lean proof:

```sh
lean PositiveStuttering.lean
```

When writing an `.olean`, run Lean with this directory as its working directory,
for example `lean -o PositiveStuttering.olean PositiveStuttering.lean`.

## 2. Share the literal source trees, retaining the same checker

The current `KSource215Data.lean` has two explicitly expanded `Tree` literals,
`t215` and `tD`. Each contains 4,751 primitive leaves. Together their definitions
occupy 245,920 bytes. They contain only 427 distinct constructor subtrees in
union: 202 are needed by `t215`, 283 by `tD`, and 58 are shared between them.

`share_trees.py` replaces repeated constructor subtrees by named definitions.
It does not introduce a new semantics, proof checker, offset certificate, source
program, theorem statement, or machine. The output retains all 2,240 existing
forward-certificate entries, all 16 check shards, and the existing `rfl`
identities between path-program trees and their literal representations.

Measured source sizes:

| Item | Bytes |
|---|---:|
| Current upstream data module | 456,548 |
| Shared-tree pilot module | 239,744 |
| Reduction | 216,804 (47.49%) |

The script reconstructs both complete constructor trees and checks exact
structural equality; it also restores the replaced definitions and compares all
other bytes with the input. It emits `SharedTreesAudit.lean`, which independently
checks both tree equalities by `rfl` in a freely generated constructor datatype.
Lean 4.32.0 checked both audit theorems with **no axioms**.

Reproduce:

```sh
python3 share_trees.py --input reference/KSource215Data.lean --out pilot \
  --lean /path/to/lean
```

The precise limits of this result are important:

- The reduction is for one current source-data module, not the whole proof.
- The standalone equality audit is not a rebuild of the changed module against
  all of ProveIt's dependencies, its 16 forward shards, or the final endpoint.
- No checking-time or peak-memory improvement has been measured. Definition
  sharing reduces source size but can affect kernel unfolding in either
  direction; the existing serial driver should measure this before adoption.
- A full adoption must regenerate the data module, recompile its affected
  dependency closure, rerun the typed endpoint clients, and retain the exact
  table/source hashes and fresh axiom reports. Old `.olean` files must not be
  reused under changed-source identities.

`pilot/sharing_receipt.json` records all hashes, sizes, and the standalone kernel
check. The preserved reference file is byte-for-byte the pinned upstream source;
its SHA-256 is
`43093f181bfdd86408a7c88bbf8c0d99ada494b5e3780ae9d93cff05502dbe67`.
The generated pilot SHA-256 is
`b260068b969f2ba2128a46841c86b0f5e9728a722b3640d1e7bb97185f569fa3`.

## 2b. Compact Rocq path lists without changing their values

The pinned `coq/215/Cert215Offsets.v` is 1,499,170 bytes. Its 2,240 certificate
entries repeat two explicit `list bool` addresses each. The long target addresses
contain many repeated `true` values. A positive binary numeral stores the same
address with a high sentinel bit:

```coq
Fixpoint certPath (p : positive) : list bool :=
  match p with
  | xH => []
  | xO q => false :: certPath q
  | xI q => true :: certPath q
  end.
```

The least-significant bit is the head of the list. Thus the empty path is `1`,
`[false]` is `2`, `[true]` is `3`, and `[true; false]` is `5`. The helper is
transparent; the public `Cert215` still has exactly the original type
`list (list bool * list bool * Z * N * N)`.

`compact_rocq_paths.py` produces a 229,933-byte drop-in data file, a reduction of
1,269,237 bytes (**84.66%**). Every decoded path, integer offset, successor index,
and entry order is unchanged. It emits `Cert215CompactAudit.v`, containing the
original literal certificate and the compact certificate, with the single
whole-certificate theorem `Cert215 = Cert215Literal` proved by `reflexivity`.
See `rocq_pilot/compact_paths_receipt.json` for its actual compiler and checker
status. The existing offset-aware checker and the machine proof are not changed.

The encoded input `reference/cert215_encoded.json` reconstructs the original
pinned file exactly, including its comments and formatting. The generator emits
that original definition inside the audit, so the equality check does not rely
on trusting a Python assertion about compressed-data semantics.

```sh
python3 compact_rocq_paths.py --coqc /path/to/coqc --coqchk /path/to/coqchk
```

This is source-data compaction, not a reduction in the 2,240 logical obligations.
No performance improvement or complete K215 endpoint rebuild is claimed. Adoption
requires rerunning the affected source/checker/endpoint chain using the pinned
Rocq 9.1.0 environment.

## What is already in the repository

These are existing improvements, not new claims of this packet: shared guarded
implication schemas, deduction-theorem abstraction, source-certificate symmetry,
AX-word macro contracts, common enumerator completeness, simplified selector
lemmas, and direct site-block composition. The recorded primary Lean closure
already fell from 204 to 185 project modules. The latest snapshot additionally
uses a symbolic `xrun` tactic in `EnumPerm`. The source-sharing pilot was checked
against that snapshot; its source-data file is unchanged from the preceding
`65e00c64` snapshot.

Relevant pinned files:

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMOffsetBisim.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumPerm.lean`
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/README.md`
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase3/README.md`

## Next mathematical abstraction to develop

A reusable equivalence theorem for the *resolved primitive control-flow graph*
would benefit alternatives based on source reassociation. Number the primitive
occurrences in execution-order syntax, give each occurrence its register action,
and resolve its successor targets for both outcomes of a decrement. Control-only
BREAK/CONTINUE occurrences carry their resolved target and an identity register
action. Prove once that this finite graph executes the path program. Two source
trees whose resolved graphs are equal then have the same register behavior,
regardless of their binary association or path-address lengths.

This should be a theorem about the complete graph, including jump targets,
halting, and all control-only transitions. Equal leaf words or bounded traces
alone are insufficient. The proposed theorem is not implemented in this packet.
It could replace new source-to-`DagPerm` certificates for the rebalanced and
reencoded alternatives by a much smaller bridge to the already-proved source.

For a new calculus, the endpoint ultimately needs preservation and reflection of
finite refutations. It does not need equality of all generated codes. Weakening
an interface to the refutation theorem can permit simpler formalisms, including
junk codes, but it does not by itself supply a shorter proof: soundness of every
halt and completeness of the scheduler still need explicit proofs.

## Interpretation of the easier-candidate recommendation

CM215 is an easier *additional* correctness theorem once K215 is available.
Its endpoint can use K215 as a black box plus the small transport argument.
This does not eliminate K215's inherited ZFC calibration or assert that CM215
has a smaller complete proof when all transitive dependencies are counted.
