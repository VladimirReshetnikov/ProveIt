# K215 proof audit and next simplifications

Pinned repository: `b6c7087477e51c017003bd729e712c8969733223`.
This audit reads the committed sources and records. It does not claim a fresh
Lean/Rocq endpoint build.

## What is already proved

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` exports

```
blank_halts_iff_zfc_refutation :
  BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
nonhalting_iff_zfc_consistency :
  (¬ BlankHalts machine215) ↔ ¬ BProv ZFCax_s [] Form.fBot
```

`Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v`
exports the corresponding exact dense-table theorem

```
tm215_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥
```

The exact literal dense machine has 215 working states, not merely a sparse
labelled machine or a source program. Nonhalting is the negation of existence of
a finite halting run. The endpoint is an equivalence, not an unconditional proof
of nonhalting. Its two sides are external proof-assistant propositions. An
internal PA derivation is explicitly still open for K215; the independent
240-state development has an internal PA theorem. This distinction should not
be lost in a simplification report.

The original verification record reports a fresh 204-module Lean build and a
237-source Rocq build plus recursive `coqchk`. The latest simplification record
reports a **185-module Lean closure**, with 9 modules recompiled and 176
hash-bound objects reused. It is explicitly an incremental checkpoint. The
endpoint audit reports use only `propext`, `Classical.choice`, and `Quot.sound` in
Lean; the Rocq endpoint reports are closed. The current Rocq compact dominated
rule was checked with seven recompiled dependent modules and focused recursive
`coqchk`; this is distinct from the original full recursive endpoint replay.

## Do not repeat already completed work

The current simplification directory is
`k225-formal/verification/k215/simplification/`. Its README and phase-three
checkpoint already implement:

| Component | Original source bytes | Current source bytes |
| --- | ---: | ---: |
| Lean dominated implication | 689,857 | 35,185 |
| Lean AX routine | 202,222 | 7,563 |
| Lean source data | 653,569 | 456,548 |
| Lean site facade | 107,243 | 14,916 |
| Lean register determinism | 17,209 | 12,988 |
| Rocq dominated implication | 921,691 | 22,673 |

These are the repository authors' existing results, not contributions of this
packet. The completed changes include offset-bisimulation symmetry in Lean,
61 bootstrap lemmas with 81 reusable conditional schemas, a general enumerator
L1 theorem that handles all valid between-candidate states, AX word-contract
composition, shared selector lemmas, and direct composition of the 105 checked
site blocks. In particular, the generic endpoint theorem is already in
`KEndpoint.lean`; `KEndpoint215.lean` is 57 lines. Factoring its final theorem is
not where substantial further savings lie.

## New exact representation prototypes

### Shared Lean tree literals

`KSource215Data.lean` contains two fully expanded tree literals, although the
source DAG and the bisimulation certificate are already represented separately.
The first literal contains 4,751 leaf occurrences, height 47, and 202 distinct
subtrees. The second contains 4,751 leaves, height 178, and 283 distinct subtrees.
Their union contains only **427 distinct subtrees**.

`compact_source_trees.py` interns that union into 427 acyclic private definitions.
Public `t215` and `tD` become references to the two roots. The `rfl` connections
to the real program trees, every certificate entry, every theorem statement, and
the entire remainder of the production file remain unchanged.

Measured full-file size: **456,548 -> 245,190 bytes**, a saving of 211,358 bytes
(46.30%). A second parser unfolds the emitted definitions and compares the full
abstract syntax trees for exact equality, not only hash equality. Every alias
points backward, so the definitions are acyclic. See
`prototype/compact_trees_result.json`.

`prototype/SharedTreeIdentity.lean` is a separate Init-only check of the two
representation identities, with the original expanded literals retained and
both equalities proved by `rfl`. Its scope is exactly representation equality.
It passed Lean 4.32.0 kernel compilation: both `t215_exact` and `tD_exact`
report no axioms. This does not by itself constitute a new endpoint build. The production replacement must still be built with its existing
consumers and the maintained generator must be updated before adoption.

### Packed Rocq certificate paths

`Cert215Offsets.v` currently has 2,240 entries, each containing two explicit
Boolean lists. The file is **1,499,170 bytes**. All 2,240 offsets are zero; the
maximum path length is 176. These are data-representation facts, not a new
bisimulation argument.

For a path `(b_0,...,b_{d-1})`, encode

```
c(P) = 2^d + sum_{i=0}^{d-1} b_i 2^i.
```

The topmost one is a sentinel; it is required to retain all false bits. The
Rocq decoder recursively reads the constructors `xO`, `xI`, and terminates at
`xH`. The structurally recursive encoder and decoder satisfy
`unpack_path (pack_path P) = P` by list induction. No machine theorem or checker
soundness statement changes.

`compact_rocq_paths.py` emits the encoded tuple data and adds the known zero
offset while decoding. Its independent parser decodes all **4,480 paths** and
checks all 2,240 complete entries against the original in order. The proposed
source is **179,009 bytes**, saving 1,320,161 bytes (88.06%). See
`prototype/compact_rocq_result.json`. The existing `Source215.v` still checks the
forward and backward certificates by `vm_compute`, so the input representation
can be changed without changing the semantic proof. The companion Rocq packet separately compiles the codec, the exact full
certificate identity, and the generic mirror theorem using Coq 8.18. That
check is narrower than replaying the pinned Rocq 9.1 binary endpoint.

Together these changes remove 1,531,519 source bytes. They are exact **source
and certificate-data compression**, not evidence of a smaller proof term or a
faster kernel check. Timings, object sizes and final endpoint assumptions must
be measured after full affected-closure rebuilds. Neither changes the TM.

## Generic Rocq certificate symmetry

Lean's `RMOffsetBisim.OBisim.symm` already swaps source paths and negates register
offsets. Rocq's current `Source215.v` still computes both
`certificate_forward` and `certificate_backward` over the mirrored 2,240-entry
certificate. Its `OffsetBisim230.v` exports `ocheck_iff` with two premises.

The companion Rocq packet implements symmetry. A convenient checker statement is

```
ocheck t1 t2 C = true ->
ocheck t2 t1 (omirror C) = true.
```

Prove this generically from: map/nth lookup commutation; involution of path
swapping and integer negation; symmetry of the tested-register equality;
`delta (-z) i = -delta z i`; and the rearrangement

```
delta z i + cnt l1 i = cnt l2 i + delta z' i
iff
delta (-z) i + cnt l2 i = cnt l1 i + delta (-z') i.
```

The finite support enumeration in `counts_ok` changes order when the two lists
are swapped. Prove each side equivalent to the universal count equation first,
using `cnt_notin` outside `5 :: l1 ++ l2`; do not assume the Boolean tests are
textually identical. Then `certificate_backward` becomes an application of
this theorem to `certificate_forward`. This is a general theorem worth proving
once for all K-family source variants. It removes one whole certificate
computation. It does not halve the total project build, which also includes
site/runtime and logical calibration.

## Ordinary Lean bisimulation for the zero-offset certificate

All 2,240 entries of the present K215 source certificate have zero register
offset. The signed-register relation in `RMOffsetBisim` is therefore unnecessary
for this particular proof. The separate `plain_source` packet preserves the
public source theorem and replaces its checker interface with the ordinary
`RMBisim.Bisim.halts_iff` theorem. The new 113-line, 4,639-byte `RMPlainCodec`
module parameterizes the small checker over a path decoder; it introduces no
integer offsets or new semantic relation. The original 293-line, 13,151-byte
`RMOffsetBisim` module is absent from this source closure.

The existing ordinary decoder has a 128-step cap. It cannot simply be reused:
622 of the 4,480 path occurrences have more than 128 bits, with maximum 176.
The new `totalDecode n := RMBisim.decodeAux n n []` uses structural recursion
with input-dependent fuel. Each nonterminal quotient halves the input.
Checker soundness is proved for every decoder, so no codec identity or fuel
claim is an unproved premise of the semantic theorem. The concrete certificate
is checked by the kernel with this decoder.

The exact audit interface is

```lean
SetTheory.BusyBeaver.ZFC.KSource215PlainAudit.source_halts_iff_iter
    (R : RegisterPath.Registers) :
  RegisterPath.Halts KSource215.p215 ⟨[], R⟩ ↔
    RMDag.IterHalts DagPerm.dagPerm R
```

The packet records its own selected source hashes, compile receipts, final
axiom report and complete dependencies. It checks the source program and DAG
bindings, not only two unrelated literal trees. It does not replay the binary
`KEndpoint215` consumer.

Tree sharing plus removal of literal zero-offset fields takes the monolithic
data prototype from 456,548 to 220,643 bytes. The executable packet splits data
and finite checks to fit the available memory: its five data/facade modules
sum to 224,084 bytes. This is a source-data reduction, not a proof-object or
whole-build performance claim. The extra partition modules are deliberately
not counted as a reduction in module count.

The finite proof composition also illustrates an actionable general rule.
After a chunk has been checked, compose its theorem through a generic lemma
whose parameters remain abstract. Do not ask elaboration to normalize the
whole concrete chunk again merely to combine two Boolean equalities.
`allC_of_halves` makes the certificate wrappers independent of certificate
computation; the actual `decide +kernel` checks stay in the leaf modules.

## Larger follow-up: canonical test graphs

The current source certificate lists 2,240 pairs of decrement/halt sites and no
nonzero offsets. Abstract each path program to a finite graph of tests and
halts, labeling each outgoing edge by its increment-count vector between tests.
A checked common bisimulation quotient can replace pairs of long path codes.
The present relation is not a graph bijection: its 2,240 pairs contain only
2,154 distinct left paths and 2,232 distinct right paths. Eighty-six left paths
and eight right paths each occur twice, so simply assigning canonical traversal
indices and comparing graph arrays is not justified. A partition-refinement
checker must verify the common quotient, or retain a finite relation.
The soundness theorem is a stuttering bisimulation: tests read equal register
values; straight-line segments add equal count vectors; both branches land at
corresponding graph nodes. Root-entry segments and halting nodes must be
included. Zero-length silent cycles need explicit treatment; bounded
normalization returning failure is safe, while silently assuming termination is
not.

This is a proposal rather than an implemented reduction. Existing source trees
include control-depth-sensitive `break` and `continue`, so equality of the
flattened primitive word alone is insufficient. Use the resolved control-flow
graph and verify both successors of every decrement. Avoid replacing the
existing proved checker with an optimizer trusted only because its output
looks plausible.

## Adoption plan

1. Preserve the pinned exact tables and all public endpoint statements.
2. Adopt the exact tree sharing and path packing through the maintained source
   generators, retaining the checked identities as regression evidence.
3. Integrate the ordinary Lean source checker and generic Rocq mirror lemma.
   Rebuild the affected production consumers with the pinned toolchains.
4. Rebuild both typed endpoint clients and recursive Rocq check; compare final
   axiom/assumption reports with the maintained endpoints.
5. Measure wall time, peak memory and object sizes before making performance
   claims. Keep the original path available until the same endpoints pass.
6. Only then consider the more invasive canonical-graph representation.

No new oracle or `native_decide` is needed for these changes. The source-lane
checks use proof terms accepted by the ordinary Lean kernel. The canonical
graph proposal remains a proposal; the concrete source and codec packets
separately state exactly what was executed.

## Pinned source references

All paths below are relative to the pinned ProveIt commit stated above.

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`:
  exact binary endpoint statements.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean`:
  original trees, source bindings and source certificate.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean` and
  `RMOffsetBisim.lean`: ordinary and signed-offset checker interfaces.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v`:
  exact Rocq dense-machine endpoint.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Cert215Offsets.v`:
  original Boolean-path certificate.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/README.md`
  and `phase3/lean/README.md`: already completed simplifications and latest
  185-module incremental Lean verification boundary.
