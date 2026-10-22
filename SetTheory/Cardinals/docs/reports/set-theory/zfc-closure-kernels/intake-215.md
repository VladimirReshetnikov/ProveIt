# Batch 215: exact residual contracts and shared scheduler proofs

This continuation reconciles **Sources 193–194**, the two manuscripts arriving
in `1b16269c48e54b0e5aff35caa645f392f9c019af`. Both compare against
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`. Placement
`6bd7e8ff0153c2a82d0dcd9ec8810be6473ed88b` preserves their original contents.
The host now has **194 sources**, with written coverage of **1–164 and 167–194**;
Sources 165–166 and the independent batch-209–211 reconciliations retain their
pending status. The collection still contains **290 reports**.

The [placement note](intake215-placement.md), [member and rename map](data/intake215-placement.json)
and [recovery helper](code/intake215-recover.py) account for all **508 members**:
231 immutable Git aliases, 49 earlier-delivery aliases, 50 arrival-only members
and 178 new ancillary files. The main manuscripts, PDFs, READMEs and Source193's
`validation-summary.tex` and `artifact-guide.tex` remain recoverable from the
committed arrival. Verbatim delivered commands use their original layouts;
restore those layouts through the map before interpreting their paths. The
present note uses the permitted reconciliation-note route. It changes neither
the delivered base article nor its labels, and builds no merged article PDF.

| Source | Manuscript | Contribution and status at this review |
|---|---|---|
| 193 | *K215: shorter proofs through shared invariants and exact runtime contracts* | A shorter dense proof; optional finite-cleanup transports; exact residual-port attachment with submitted component checks; an uncompiled subtree abbreviation. |
| 194 | *One proof per mechanism: shared implication proofs and a checked candidate scheduler* | One progress/completeness theorem for four enumerators; exact concrete adapters; a counterexample to exchanging payload and candidate quantifiers. |


| Source | Committed archive | Immutable Git blob |
|---|---|---|
| 193 | `K215_Proof_Simplification (2).zip` | `d07ea108bc48c4deb3824b1af612bfc43b72f1c0` |
| 194 | `K215_Proof_Simplification_2026-10-22.zip` | `f779cc031d92c0df5c63592a30f251f3b6e3c253` |

The complete ordinary reviews are retained for [Source193](data/intake215-review/ordinary-01.md)
and [Source194](data/intake215-review/ordinary-02.md), with their
[pins and scope](data/intake215-review/ordinary-01.json) and
[comparison record](data/intake215-review/ordinary-02.json). The manuscripts and
relevant sources were read as mathematical arguments; recorded logs were read as
evidence supplied by their authors. No supplied program, generator, proof compiler
or archived executable was run for these reviews. Neither review found a reason
to retract the currently checked construction.

## Shared results and the current checkpoint

Both reports repeat the implication basis already adopted in
[phase13](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase13/README.md).
Their generic core and Lukasiewicz bridge are byte-identical to the maintained
files, and Source194's numeric adapter is identical too. The six-goal derivation
is credited to upstream `3a7a61ee`/`49e99c5b`: two final aliases are inlined, leaving
56 private lemmas. Its restricted-row assumptions require reflexivity,
domination into either implication operand, modus ponens and the restricted rho
row. They require no implication injectivity, relation transitivity, syntax
well-formedness or collapse of a truth code. The universal relation supplies the
unrestricted K/S/Peirce/composition interface.

The advertised 42,454-to-18,243-byte, 811-to-401-line pair reduction is therefore
historical phase13 work, not another saving. Nor does Source193's historical
three-file/433-line estimate or 1.17% selected-closure estimate describe an
additional current reduction. Its derivation is not asserted minimal. The
maintained producer has separately checked provenance; an older supplied
renderer or patch is not a replacement merely because its output agrees.

The accepted [phase14 checkpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase14/README.md)
also shares derived rules and weak transitive-container profile contracts. Its
selected endpoint contains 178 project modules. The reports' historical
179-module scopes must not replace that inventory. The combined phase15 proposal
is being checked separately at this note's cutoff. In particular, the selected
Source193 dense successor below is held for its retry; this note does not claim
that retry or a new full endpoint has passed.

## Source193: dense synchronization and finite cleanup

The short dense proof keeps one invariant: either both computations already
have halting witnesses, or they have the exact synchronized successful run at
time `t`. Dense-to-sparse transfer evaluates it at the dense stopping time.
For the reverse direction, evaluate it at `k + 1`, where `k` is the sparse
stopping witness. The synchronized arm contradicts the successful `k`-prefix
and its missing next step through `run_succ`. This removes the remaining state
case split in Source192's proposed one-induction proof.

The [delivered bridge discussion](193-invariant-README-a387587671.md) retains the
same definitions, earlier lemmas, imports and complete `blank_iff` header. No
inverse state map, injectivity or tape-finiteness condition is introduced.
The 7,323-byte/170-line source is 804 bytes/23 lines smaller than phase14 and a
further **204 bytes/eight lines** smaller than the initial phase15 candidate.
These are alternative endings of one proof; the savings cannot be added as if
both replacements remained. The phase15 integration selects the exact Source193 bytes for the
pending phase15 check, independently of this manuscript intake.

A separate optional abstraction permits **finite terminal cleanup**. Each
successful source step gives a strictly positive target run to a related state;
a stopped source need only imply eventual target halting, allowing an epilogue.
Cancellation of a successful prefix from a terminal target witness proves the
reverse direction from advancement alone. Preservation uses the terminal finish
condition. The supplied zero-cost-loop/stopped-target example shows why positive
progress cannot be omitted. The register adapter requires a stuck source to be a
literal halt leaf; decode failure is not silently treated as halting. The dense
adapter counts accepted partial steps rather than absorbing total steps.

This is useful reusable mathematics, but its measured two-client implementation
grows by **6,716 bytes/172 lines** after 8,543 bytes/219 lines of utilities replace
1,827 bytes/47 lines. It is retained as a marked alternative to the short dense
proof, not presented as a source reduction. Its `KSim` implementation and the
residual semantic `KSim` below are different alternatives; separate component
receipts do not certify their combination. Earlier positive-stuttering and
terminal-contract proposals retain their priority.

## Source193: exact residual attachment and the remaining integration

The substantial runtime advance is the [residual component](193-invariant-README-1dd6aae6a6.md).
The [routing proof](code/193-invariant-KResidualRouting215.lean) computes the
role reached by every bit before the final primitive bit. It rejects a missing
role or premature primitive edge. Induction over `RolePath` identifies that
role and its formal state. Two route witnesses for the same complete word and
last bit have equal preceding prefixes by reversing and cancelling the list
equation. This uses the whole consumed prefix, not just a physical state or a
short suffix. Internal block indices are irrelevant to this route-identification
lemma; the certified prefix theorem still provides the block executions.

The selected port keeps the entire reversed prefix on the left and the final
bit, symbolic gap, header and register frame on the right. `checkEdgeFrom`
receives the original whole word for increment, break, continue, stripping and
overflow. Both decrement cases, register permutation and bounds, the path bound
48, increment's spare-register extension and terminal230 remain explicit. A
suffix begins with progress=false; every nonhalting suffix establishes positive
`Reach1`, including when the preceding prefix is empty. Its symbolic semantics
quantifies over all natural register values and gaps, not selected tests.

The [site facade](code/193-invariant-KResidualSites215.lean) applies
`allSites_sound` at each exact `LeafAt`, then rewrites the computed port to the
routed port. The earlier `KDecoderSuffix215.leaf_spec` composes uniform prefix
execution with the positive suffix. Source totality and `t215_eq` cover source
walks with implicit zero padding. `KTape.boxLemmas` supplies the register-engine
boxes, and finite checks discharge the source count and both terminal rows.
The resulting `source_halts_iff` needs only its initial `KSim.Rel p215 c T`:
the formerly universal suffix, box and source-totality premises have been closed
inside this **submitted component**.

Ordinary review matched all 105 residual block statements to the maintained
whole-site indices and complete forward/reverse paths, and checked the 51
submitted source/log pins and zero-exit metadata. Those 51 sources comprise 24
new modules and 27 prerequisites. Three prerequisite alternatives come from the
older `proof-contracts` KSim/KSimPrefix/KDecoderSuffix215 proposal; they are not
current maintained replacements. Six batches are split into halves for resource
limits. The ledger preserves failed attempts and resumed work, including early
observations followed by persisted rechecks. No objects are delivered and no
compiler was rerun here. Its printed profiles are standard, with the named
source-halting result using `propext`, `Classical.choice` and `Quot.sound`.

This closes an earlier mathematical premise, but it does **not** show the old
fuel-limited Boolean site evaluator returns true. Full adoption must expose
semantic coverage at `KEndpoint` or compose the new theorem with the unchanged
dense, boot, source-calculus and ZFC bridges. It requires the current transitive
source rebuild, all concrete residual checks, endpoint clients, and a maintained
emitter/partition regeneration route. The received 705,880-versus-926,351
symbolic-iteration estimate (23.8%) is not a measured Lean or whole-endpoint
speedup. All occurrences remain checked; shared arbitrary-prefix primitive and
return contracts are a possible subsequent step, not supplied by this result.

The independent [subtree abbreviation](193-invariant-README-ac2a53e332.md) is
smaller in scope. `checkedSubtree test t P` abbreviates
`allSites test P.reverse (descend t P) = true`, printing the prefix once. It is
transparent and preserves the finite obligations by definitional reduction.
The 105 replacements, reversals and delivered after-hashes were reconstructed
as text; all ten baseline source pins and the maintained generator pin match.
The existing proof bodies and root join stay fixed. Nine batches lose 18,803
bytes and the helper adds 238: **18,565 net Lean-source bytes**, excluding the
generator change. This proposal is explicitly **uncompiled**. It claims no
object-size or evaluation saving. It stacks with the proof-only phase15 edits;
using it for residual predicates requires adaptation from its current whole-site
predicate. Fresh descendant checks remain necessary even if an intermediate
object happens to be byte-identical.

## Source194: one candidate-progress proof with the right quantifiers

The new [CofinalScheduler core](code/194-scheduler-CofinalScheduler.lean) separates
concrete dynamics from progress laws. `Dynamics` retains each client's step/run
functions and their zero/successor equations. `Laws` says a successful boundary
step increments the candidate index by one; a successful active step strictly
decreases its pending rank and preserves the index. The rank loaded at a boundary
may be arbitrary. No encoding injectivity, global time bound or extra fairness
assumption is imposed.

Lexicographic induction on `(target - index s, pending s)`, with
`index s ≤ target` retained, reaches the target boundary or halts earlier. At a
boundary already at the target, zero steps suffice. Failure of a transition
halts; a boundary transition below the target decreases the first component;
an active transition decreases the second. Prepending the successful step
composes the witness. `complete_at` fixes **one target first**, then requires
halting from every *reachable* boundary payload there. It need not assume the
same property for unreachable payloads. Run composition and invariant transport
can be reused without the progress laws.

For `EnumPerm`, the existing cofinal encoding bound chooses a candidate beginning
with `AX(0;1,Y)`, where `Y` is the initial candidate index. The existing
`program_none` contract handles every working payload after that prefix. Thus
one chosen target works for whichever boundary payload is actually reached;
there is no claim that every register was reset to one fixed value.
`complete_any` allows an initial active candidate. The corresponding
`halts_iff_any` **retains `Inv (toW s)` for soundness**: arbitrary working data
can already contain a halting trigger unrelated to derivability. Existing
boundary-restricted APIs remain wrappers. `Enum254`, `Enum222` and `EnumDom`
reuse their existing boundary/decrease facts as well. Executable definitions
are intended unchanged, and sixteen repeated inductions become three shared
ones. Arbitrary-state completeness itself has earlier antecedents such as
`EnumSafeStart254`; the reusable multi-client implementation is the contribution.

The report supplies a counterexample to the tempting weaker quantifiers
`∀payload ∀N ∃K≥N`. In state `(k,b)`, advance to `(k+1,!b)` exactly when `b`
matches the parity of `k`, and halt otherwise. Every state is a boundary. For
each fixed payload and lower bound, either that index or its successor halts.
Yet the aligned trajectory keeps changing payload to match the next index and
never halts. Payload-wise cofinal success therefore does not imply a single
successful target for the reachable payload. This does not refute the maintained
compiler's stronger reset-word contract.

Source accounting matters: the four enumerators plus the 4,304-byte/113-line
core change 109,663 to 109,339 bytes and 2,666 to 2,659 lines, saving only
**324 bytes/seven lines**. `EnumPerm` plus the core alone **grows by 3,411 bytes
and 95 lines**. The benefit is shared proof maintenance, not a large K215 source
cut or measured speedup. The scoped textual audit of 237 old statements and
117 executable declarations is submitted evidence, not a general semantic
checker. Literal Enum222/EnumDom generator transformations appear compatible;
actual reproduction and current provider checks remain adoption obligations.

The supplied Lean ledger describes a fresh 22-module component build, 14 basis
typed clients, ten scheduler typed clients and the counterexample, with six
warnings in inherited TarskiComplete. It excludes the physical machine endpoint.
Ten scheduler declarations are not ten printed profiles: the audit has six
concrete and three generic reports; four declarations check run composition.
The generic reach/completeness profiles contain `propext` and `Quot.sound`, the
invariant profile is empty, and the counterexample's three profiles are empty.
These are attributed records, not fresh intake execution. The new module and its
imports require a new closure census before integration; historical endpoint
counts cannot receive the four-client saving automatically.

## Alternatives, open work and execution boundaries

Source193's generic state-relabeling functor assumes transition commutation
including terminal rows, preserves tape and needs no inverse or injectivity.
Its one-client use grows by 1,467 bytes/48 lines; family reuse concerns eight
generated copies of one template. Its CD222/DomRho8 alternatives retain their
producer/manifest obligations. Source194's Rocq scheduler uses nested strong
induction and supplies the uniform-cofinal corollary. Its twelve-module plus
client record uses Coq8.18/OCaml4.14.1 and four namespace adaptations, not the
maintained Rocq9.1 endpoint. Imported utility axioms and closed named reports
remain distinct. All this Rocq material is inert reference data under the
current Lean-only work scope; neither paper supplies a new maintained Rocq run.

Source194's route-before-tape proposal has the correct order: choose route and
clock from the source path, then prove execution for every admissible tape.
It overlaps the maintained phase-nine route/prefix bridge and adds no new decoder
theorem. Role/path identity and the terminal primitive bit cannot be erased by
keeping only a physical state or suffix; the clock stops before primitive action.
Source193 advances the residual component beyond that proposal, while production
still retains its 4,751 occurrences and 6,176 branch obligations until integration.

The dense successor, current-site abbreviation, semantic residual replacement
and scheduler refactor are separate choices with different costs and gates.
None changes the literal 215-state machine, proves a smaller state count,
unconditional nonhalting, an internal PA/ZFC endpoint or a new consistency result.
No minimum derivation or controlled runtime speedup follows. The open work is to
choose and check the relevant adapters and regeneration paths, preserving the
exact endpoints rather than combining overlapping source counts.
