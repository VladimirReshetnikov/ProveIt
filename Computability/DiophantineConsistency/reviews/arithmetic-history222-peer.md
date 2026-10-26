# Independent actual C222 represented-history review

Reviewer `/root/complemented47_review`, 26 October 2026. PASS within the
stated scope; no correction requested. This was a read-only mathematical,
source, and provenance review. No compiler was invoked, no frozen source or
object was changed, and no Git action was performed.

I read all 208 main lines and 55 check lines, the complete current generic
`ArithmeticSequenceHistory`, complete actual `ArithmeticRow222`, complete
Foundation PRF source, the arithmetic predecessor/projection contracts, the
Foundation arithmetic completeness bridge, and the old `ArithmeticHistory254`
for comparison. I also read the author receipt and all three preparation,
compile, and receipt scripts. I previously reviewed the actual row, seed,
growG, Nat checker, and generic sequence-history packets independently; I did
not author them. My separate equation and HA proofs do not supply premises
for this module. I have not included the later `ArithmeticHistory222Nat`
packet in this review.

Source prefix: `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| Source | SHA-256 |
|---|---|
| `ArithmeticHistory222.lean` | `42c196715f04b4bd8d257a3450e0947a13a62c9332e06c62b556a835d60156b8` |
| `ArithmeticHistory222Checks.lean` | `aa553cf0e5d9ab5b760b3dfafc9f648de97be168e2ce802239ab9814957145f3` |
| `ArithmeticSequenceHistory.lean` | `764b832d28249b17d640a7a3a2b3721deb90a0ee82360e48331be6dabd0d9a3d` |
| `ArithmeticRow222.lean` | `7341c95d5b3d9a9d17eb2f6bfb32c7b1bf781fe86274c0eeba817c953be6c8f1` |

## Actual rule selection and internal recurrence

`positiveStepDef` has free slots `(r,s,raw)` and syntactically binds the
base-12 remainder `k`, quotient `p`, Cantor tail `t`, its minor/major fields
`b,c`, and the two sequence lookup results `u,v`. GEN/tag2 takes its first
lookup at the whole tail; all other tags take the minor component. The second
lookup is always the major component. The final graph is explicitly the
new `ArithmeticRow222.rowDef`, so tags9/11 use actual growG/helper-free
bundle222. The bound variables and their uses agree with `positiveStep`;
there is no captured free parameter or old-row substitution.

`stepDef` returns zero at code zero and otherwise binds a predecessor by
`code=raw+1`. The reused `ArithmeticRow254.predecessor_witness` is a generic
arithmetic fact over IOpen, not a C254 semantic premise. Its weak bound
`raw≤code` and equation determine the correct predecessor, including rejection
at zero. A valid conclusion is encoded by its successor; code-zero rejection
is not confused with a valid conclusion whose numeric code is zero.

The actual step function has its own proved represented-function instance.
It instantiates the generic append-history with the fixed `stepDef`; no
arbitrary graph is assumed total. The generic totality theorems retain their
semantic step and exact representation premise, which are discharged here
by `step_defined`. The history starts with `[0]`, and history at `code` has
length `code+1`. Its next row uses predecessor history at `raw`, while the
semantic step receives `raw+1`, so the two increments match exactly.

The quotient and both Cantor projections are at most `raw`. Thus every
GEN/MP child position lies in the preceding complete history, even when
`raw=0` or the payload is zero. `value_succ` rewrites those actual lookups
using this evaluator's own `history_lookup_le`, with no valid-proof, correct
oracle, or desired child-value premise. The separate full lookup theorem
also handles all out-of-range internal indices by returning zero.

## Fixed syntax, totality and scope

All history/value/acceptance graph formulas depend only on fixed syntax.
Although several appear after the ambient-model variable declaration, their
definitions do not use that type or a chosen semantic function. Their Σ1 and
Δ1 graph instances are proved for every stated IΣ1 model. Sequence validity,
length, lookup and primitive recursion are internal-index results obtained
from Foundation's definable induction and represented recursion; they are
not merely standard-Nat recursion theorems.

The Boolean graph has free slots `(b,code,conclusion)`. Its positive and
negative branches compare the same unique `value code` with `conclusion+1`.
The closed `totalitySentence` binds all three arguments and universally
quantifies the competing result for uniqueness. `totalitySentence_true` uses
the full represented graph and Boolean range in every IΣ1 model. The final
`isigma1_proves_totality` invokes Foundation's actual arithmetic completeness
bridge, yielding `IΣ1 ⊢` this fixed sentence. This is stronger than a statement
about only standard outputs, but is a classical IΣ1 derivability result, not
an HA derivation or an internal seed-validity/consistency theorem.

No old `ArithmeticHistory254` is imported. Its row-independent recurrence
shape is factored through the new generic module, and the old numeric row
is reused only through the already-reviewed tag-preserving Row222 interface.
The remaining standard-Nat decoder agreement, internal validity of the new
seed, C222 proof translation, actual interpreter/runtime calibration, and
HA equation/consistency equivalence are not established by this packet.
The separately announced Nat-binding leaf is outside this review.

## Provenance checked without compilation

I independently rehashed all 118 selected custom sources (95 Foundation),
403 cached object/companion files, 38 external boundary objects, five parent
receipts, compiler, package manifest, input inventory, all three drivers,
final leaf sources/snapshots/objects/logs/timings and the sole run JSON.
All 582 checked hashes matched. Each selected source's direct import list
matches its inventory, and every direct dependency lies in the selected set
or explicit package/toolchain boundary. No cached object is relabeled as a
fresh build by this review; external package internals are not newly audited
transitively.

The author's first fresh pair exited zero under the recorded 6GB/single-job
caps. I read the empty main log and all 14 standard-only axiom reports
(`propext`, `Classical.choice`, `Quot.sound`). The source snapshots match the
frozen files, and the private objects are:

- Main: `1bcb989a5ca4e9c40390bc12f2bfbe37a691423ce666eee9b59afb2c602b2057`.
- Checks: `5dd7eb3601dc9b741f448c2ac9c21f3e3d5a6069a963c2448e630f38d8c491f3`.

Reviewed receipt pins:

- Author: `81495be49c6e13abd3af0d26807296abb51d67a0815a6e2e0e3900a3b2bb21e4`.
- Replay: `2f17663e8b2448c2ed2e7bc8201985dbb862d87cf8580ed384e4df184ab37049`.
- Input inventory: `c24d3865cf1b501e998581c460b10cbccef6eba7f9e8c99d243bc320ebfd3cd8`.

These checks authenticate the author's bounded executions. They are not an
independent fresh compiler replay or a broad Foundation-closure validation.
