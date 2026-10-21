# Independent review of the dominated continuation K217

No substantive mathematical or code-scope blocker was found in the full
manuscript and selected-check closure read. The new contribution is a targeted
source reassociation and one physical marker merge on the already reviewed
Source149 dominated-rho8 construction. The submitted ordinary result is an exact
217-state machine with initialization included; fresh selected execution is
owned by root and is not claimed by this source review.

The archive arrived at `8a1796545e` and was safely extracted from its Git object
into this review directory without invoking submitted code. Its 39 files include
the exact original Source149 archive. That nested archive is byte-identical to
the one arriving at `7071e5041ee316d087661b658362feed159901ef` (SHA-256
`080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9`). The deeper
predecessor pin remains `f8ec6158f3bdc885139ee395ae34fe44c3251b9f`.

## Ordinary construction proof

The source subtree at `11101001001110010` changes from
`(D,(((A,B),C),E))` to `((D,A),((B,C),E))`. The five closed, halt-free factors
have 14, 27, 53, 374 and 3,682 primitive occurrences. Closure prevents break or
continue from escaping a factor; it does not assert termination. Therefore a
nonterminating factor is not incorrectly discarded by the reassociation.

The three rotations use physical parent/child pairs 210/188, 213/210 and 201/213.
The scripts require pure bit-preserving right-moving rows, unique logical roles
and the rotated child's unique physical incoming edge at each intermediate
stage. They compare the complete expected decoder relation after each update,
including the changed role of the child. The primitive word and guarded ordinal
CFG are checked completely, including both decrement outcomes. This supplies
the all-natural source-step correspondence, rather than a finite register test.

The final selector is `213/0=0R92`, `213/1=1R90`, with `92/0=0R104` and
`90/0=0R105`. Old69 and old400 share `1R31`; their different zero branches go
to105 and104 respectively. The only incoming old edges are `53/1=1R69` and
`224/0=0R400`. Thus the previous cell supplies an exact origin marker on every
reachable visit from state0, for an arbitrary initial tape.

Deleting400, mapping its target to69, and setting `69/0=0L213` gives one-step
read-one simulation and three-step read-zero simulation. The two read-zero
blocks visit only the current and previous cells, preserve both, and end at the
old head+1 with the correct continuation. All other rows are mapped copies.
Positive bounded blocks, deterministic continuation and no internal halt give
both halting directions. The argument correctly concerns arbitrary tapes from
state0; it does not claim arbitrary configurations already inside69/400 have
the marker invariant. Sharing selector213 with its source-decoder role causes
no conflict: the row semantics are identical in both uses.

The result deletes one state, adds none, and changes nine retained rows versus
the dominated parent. Relative to the rotated218 intermediate, just69/0 and
224/0 change, besides removing400. There are217 working states/434 rows and a
separate halt. Native labels are not a state count. The source remains4,751
primitive occurrences,203 subtrees,depth45 and zero-run6;94 addresses change.

## Calibration and boundaries

All logical and command semantics are inherited literally from Source149.
The numerical inequality U≤A, zero alias I(0,0)=0, depth-three axiom used to close
cd59, and the3,728-node unrestricted-row derivation are described correctly.
The manuscript distinguishes numerical schema instantiation from an assumed
native formula-substitution rule. Its all-natural AX wire order is[c+3,z,y,x],
with U=d+z,A=U+x,B=h+y,C=c, and the original common fields for MP/DROP/NIP remain.
The ten stack outputs and selection/reset counts agree with the parent.
The strong proof compiler permits arbitrary underlying data for completeness
and early halt, while soundness retains the required theorem/Good-stack invariant.
The cofinal number P(3,P(1,P(1,P(Y,R)))) is unchanged.

The reassociated source therefore inherits the same finite-refutation criterion.
The final binary runtime and whole blank initialization remain separate required
bridges. The packet's reported startup is312,617 steps to native84/canonical83,
head−5,gap80,logical vector[3,0,0,0,3,0,0,0,0],130 one-valued spares and277 one cells.
Its delivered runtime reports6,176 cases,1,616,558 symbolic steps,min13 and all434
rows. Those are delivered records at this review checkpoint, not a new execution
by this reviewer.

The ordinary proof is formalizable in ZFC using the pinned inherited calibration.
No new exact217 Lean/Rocq or internal PA endpoint, unconditional nonhalting,
minimal-state theorem, priority claim or216-state construction follows.
The protected-tail extension is additional possible seed freedom, not a premise
needed for the delivered clean seed. It preserves the same command arities and
conservative stack effects; arbitrary initial proof data are not generally safe.

Opening's separate helper-span candidate025 has the exact delivered source and
an isomorphic table under188→213,213→210,210→188. Its own saved comparison checks
all434 rows. This is an independent rediscovery/confirmation of the same saving,
not an additive fold or a second state reduction.

## Selected code closure and replay precision

The new reconstruction, independent source/fold audit, independent blank audit,
and wrapper were read completely. The independent source audit imports only the
standard library and rebuilds the tree, control graph, complete prefix binding
and four marker cases. The blank audit separately checks sparse, dense and
canonical execution against a directly encoded complete frame. Its state
bijection is reconstructed through transition graph traversal.

The vendored source_language.py/build221.py and all-tape check_joint_fold.py are
byte-identical to the previously reviewed maintained files. The embedded
parent's runtime driver, both induction modules and legacy mapping are exact
accepted Source149 inputs. `code-closure.json` records the identities. The new
root plan selects reconstruction, source/fold audit, blank audit, joint-fold
checker and parent validate_native on the new table/source; it does not run the
manifest wrapper or replay the parent's successful proof checks.

One reporting distinction matters. `audit_blank.py --directory machine` finds
no machine/validation/startup.json in this archive. It independently computes
the312,617-step trajectory and whole frame, but its fresh
`trace_rows_independently_replayed` is0. The delivered receipt's312,617 comparison
against stored trace events belongs to a prior run. The full trace was omitted
from the release; its digest and complete endpoint were retained. This is not a
startup proof gap, but an intake note must not describe the fresh default-path
job as comparing absent stored events. A newly generated trace can be compared
separately if desired; no additional execution is required by this review.

The exact source/rotation/marker premises are sound on this reading. Fresh actual
records, after root's terminal observation, can be attached as an additive review.
