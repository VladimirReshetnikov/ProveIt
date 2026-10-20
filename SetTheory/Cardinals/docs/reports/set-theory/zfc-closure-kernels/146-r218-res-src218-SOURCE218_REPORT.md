# Source and encoding research after the published219 construction

## Status and pinned starting point

The active target is218 or fewer working states. This source work has not
produced a verified blank-start machine meeting that target. The joint work
has produced a218-state initialized core with all6,167 arbitrary-natural
primitive interfaces proved, but its blank initialization has an explicit
counterexample. This source work has reproduced the published219 machine,
constructed and independently checked a distinct alternative219 machine, and
screened several families of source encodings. Estimated hardware costs below
are properties of explicitly described allocation models, not unrestricted
Turing-machine lower bounds.

The pinned ProveIt commit is `26d5de6d21fa354d50e0b84fe851c289925b8d72`.
The published219 archive SHA-256 is
`04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b`.
The full published replay completed with `FULL_K219_REPLAY_PASS` in
`k219_replay/replay.json`, including fresh primitive proofs and the independent
published runtime audit. The published native table SHA-256 is
`b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`.

## Accepted alternative219

The accepted artifact is `alternative219/candidate.tm`, SHA-256
`142cb09f13f336cf23330f959d5e78e4249c47a3d8f728efed7c61cc38825a11`.
Its source is `alternative219/sites.json`, SHA-256
`e2e41a573aba9f6a763bca387900fd383a737822776b48e6a853db1714bb9adf`.
It contains219 working states and438 rows. The source has206 DAG nodes,
4,744 leaves, depth38, and maximum zero run6.

The construction combines the previously accepted source reassociation with
the published new equality macro. Exactly35 rows differ from published219;
the old35-row patch is disjoint from all eight retained-row changes and all
three state deletions in the published220→219 reduction. Disjoint syntax
patches alone would not prove compatibility: the alternative's repaired CB1
entry uses state103, whose behavior changed in219. A fresh full runtime
derivation was therefore required and passed.

The checked evidence is:

- Complete primitive word equality and equality of both complete ordinal
  guarded CFGs with the published219 source.
- Fresh proof of all6,167 arbitrary-natural primitive families, containing
  1,512,606 symbolic rules, with minimum constant duration13. Every one of
  the438 literal transition rows occurs in the proof traces.
- Independent sparse-native and dense-canonical replay of the complete blank
  startup, agreeing after312,617 steps at native dispatcher84/head−5. The
  frame has logical registers `[3,0,0,0,3,0,0,0,0]`, gap80,130 spare1 values,
  277 one-cells, and zero everywhere else.
- Independent recheck of the seeded product invariant against the alternative
  source's complete guarded CFG.
- Complete R7 projection of all6,162 seeded primitive families:115,096 full
  windows and113,357 post-initialization windows. This projection widens
  correlations and is a sound over-approximation under the checked source
  invariant and universal primitive proofs; it does not assert local-machine
  fixed-point closure.

These artifacts are in `alternative219/`; `releaseproof/` under that directory
is the self-contained offline package. It includes a literal35-row builder,
the pinned published219 archive, fixed final artifacts, and adaptations of
the published runtime and startup auditors. The symbolic engine and helper
are unchanged and hash-pinned. The inherited calculus calibration remains a
separate mathematical premise of the composed construction; no new compiled
proof-assistant endpoint is asserted.

The self-contained quick replay completed with
`QUICK_ALTERNATIVE219_REPLAY_PASS` in
`alternative219/release_quick_replay/replay.json`; the release's fresh full
primitive derivation also passed. The accepted alternative is the table with
the hash above. In particular, the separate depth36 layout
`allocated_v0008/candidate.tm` is **not** an accepted blank-start machine:
its6,167 primitive interfaces passed, but every designated blank start
screened entered a blank-ray loop before a clean source frame.

## Why219 changes source allocation

The published equality macro is

```text
P = (CD6, CC2)
U = (P, CB1)
L = ((CD5, U), CD6)
R = ((CD5, CC1), U)
E = (L, R).
```

All four old equality occurrences are replaced. Its proved contract clears
registers5 and6, preserves all other registers, returns normally precisely
when the original inputs agree, and otherwise exits by Break1. This contract
is open-context equivalence, stronger than a finite collection of examples.

The native encoding represents `P` at both13 and108. A syntax-node-to-state
function therefore loses information: the inherited decoder relation is a
relation from one logical node to two physical states. State108 also shares
the distinct `(CD6,CB1)` role. The published census is169 decoder states,
184 physical source roles,183 distinct internal syntax nodes, and50 states
outside that source relation.

`hardware_objective219.py` and `allocate219.py` preserve this relation. The
objective retains existing physical roles and matches fresh syntax nodes
against the frozen rows of missing helper states. It checks actual old
nontrivial decoder paths and contextual suffixes. The maximum matching may
ignore interactions among several simultaneous assignments, and it excludes
new as-yet-undiscovered aliases. It is therefore only a search bound within
its preservation model. The allocator solves the actual remaining row and
assignment constraints, then checks literal decoder binding. Complete
primitive/runtime and startup checks remain mandatory after allocation.

The fresh219 classification records146 runtime rows across82 native states.
Relative to the old220 classification, it adds302/read0 and302/read1 and
removes162/read1. Including the original alias paths and the first36 blank
steps yields201 protected rows for the current source allocation model.
These classifications guide allocation; they do not prove that the rows
cannot be replaced by a different architecture.

The new302 return also permits right-child decrements in more contexts.
Fixed-PC unbounded probes established direct `(write1, R, selector)` entries
for D1→41, D3→17, D4→144, D5→45, and D6→21 at the four literal source
addresses in `right_decrement_entries.json`. Those observations are not
uniform theorems over arbitrary earlier prefix bits. Every actual candidate
occurrence still receives its own runtime proof. The analogous limited
screen did not find general entries for D0, D2, D7, or D8.

## Equality-tree census

`equality_variant_census.py` screened the16 equality hits supplied in the
published archive, each both unchanged and with registers5 and6 exchanged.
It produced32 uniform whole-source variants. The published winning macro
alone had retained-role estimate219. Several all-left-CD alternatives had
estimate220. Swapping registers can change physical cost despite preserving
the symmetric equality contract.

`heterogeneous_equality.cpp` then enumerated all32^4 =1,048,576 independent
assignments of those variants to the four equality occurrences. The exact
retained-role census found minimum219, attained by the published uniform
choice. The minimum among assignments without a right-child decrement was
220; even optimistically deleting state302 would leave219. Exactly19
assignments had estimate at most221, and all19 were uniform choices.
Every one of those19 near results agreed with the independent Python census.
This family ignores new aliases and does not prove an unrestricted bound.
Most nonpublished equality hits have only finite semantic screening, so no
universal equivalence theorem is inferred for them from this census.

The root agent's reusable-subtree search found18 DAG6 equality trees. Our
whole-source census is `dag6_equality/summary.json`. All18 have206 source DAG
nodes, depth38, and maximum zero run6. Entries0,3,4 have retained-role
estimate219; the others have220. A new all-left-CD macro, entry9, is

```text
P = (CD6, CC2)
U = (P, CB1)
V = (CD5, (P, CI6))
E = (V, (CD6, (V, U))).
```

This macro is logically new, and the root agent supplied an all-natural
termination/equality proof. It has12 macro DAG nodes and12 leaf occurrences.
Replacing all four occurrences produces4,752 source leaves. Its whole-source
estimate is220 because it loses the old shared `(CD5,CC1)` role at state122.
It also places CI6 at a previously unsupported right-child suffix. An
exhaustive existing one-row entry screen at the first such exact PC found no
finite survivor on either the220 or219 parent. That is an obstruction in the
tested fixed-interface family, not a general impossibility theorem.

## Reassociation and search checkpoints

`substitute_equality.py` considered205 stored earlier source files,107 unique
inputs, requiring exact original primitive word and both full source CFGs.
Replacing all four old equality subtrees yielded85 distinct219 sources.
Eight have only205 syntax-DAG nodes, but each has maximum zero run7 and a
fresh protected-hardware estimate of at least226. Their missing arithmetic
helper roles prevent turning the bare DAG saving into a machine-state saving.
Several206-node layouts have protected estimate219 and zero run6.

`retarget_anneal219.py` searches reassociations whose escaping CB/CC operands
are retargeted to preserve the ordinal successor graph. It rejects rotations
that would move the implicit fixed-depth CD zero target. It supports global
replacement, selective parent/grandparent replacement, and an optional CI
commutation search. CI permutations are allowed only within maximal straight
runs whose internal positions have no incoming control edge except their
predecessor; every emitted source checks the register-increment multiset of
each such run and both exact target resolvers. A finite sequence of such
increments has the same register effect and cannot halt internally, which
justifies the program equivalence at the run boundaries.

The main global and selective searches preserve the original first source
subtree for bootstrap stability. The separate commutation run permits that
subtree to vary; any result from it consequently needs a fresh exact blank
startup proof. All saved sources remain exploratory until allocation and
full runtime checks pass.

The optional annealing runs were stopped at saved checkpoints after the initialized218
core was found and remain incomplete bounded searches. Their checkpoint counts and
outcomes are in `retarget219_global/summary.json`,
`retarget219_selective/summary.json`, and
`retarget219_commute/summary.json`. They do not certify an exhaustive search.

## The initialized218 core and its startup obstruction

The jointly discovered core has native SHA-256
`cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f`.
It deletes state301, redirects its incoming edge to88, and uses

```text
88/0 = 0 L51       88/1 = 1 R103
51/0 = 0 R122      51/1 = 1 R51.
```

All6,167 literal-PC primitive interfaces passed a fresh unbounded derivation,
with1,515,192 symbolic rules and minimum constant duration13. The proof
allows all nine primary values independently arbitrary, arbitrary natural
extra gap, and a nonempty finite spare list with arbitrary natural entries.
It does not assume the source reachability masks.

`candidate218_decoder_audit.py` independently checks the exact three retained
row changes, deletion301, all4,743 internal prefix bindings, and the local
two-role lemma in `candidate218_audit/decoder_lemma.tex`. For
`P=(CD6,CC2)` and `U=(P,CB1)`, old301 carries `(CD5,U)` following a0,
while old88 carries `((CD5,CC1),U)` following a1. The new88/read0 path
distinguishes those preceding bits and reaches the appropriate old endpoint,
preserving the tape. The two branches take5 and3 steps respectively.

The51 scan exit is safe on its initialized contexts because its terminal0
has a1 immediately to its right, and states16 and122 have the same read1
row. Blank startup violates that premise: at step79 it reaches51/read0 at
head5, with a0 to the right and one-cells exactly at−3 and−2. The old path
writes the missing1; the new path eventually enters35 and writes1 forever
into the blank right exterior. This is an explicit startup failure, not an
unfinished bounded run. Therefore the core is not a solution to the user's
blank-tape218-state target.

## General clean seeds and source scheduling

`general_seed_lemma.tex` proves that a complete source-root frame with
logical values `[n,0,0,0,d,0,0,0,p]` is sufficient for every natural
`n,d,p`, including the allzero seed. No lower bound on nextproof and no
requirement that the additive parameter equal3 is needed. Soundness holds
through the current/stack theorem invariant. Completeness follows from a
uniform reset prefix and an unbounded family of padded successful proof
program codes. The lemma uses the inherited command compiler and calibrated
calculus; it does not replace the physical startup obligation.

We split the source into four closed phases: load the next proof (9 leaves),
read the command selector (14), read its additive field (14), and execute the
body (4,707). `phase_permutations.py` checks the complete guarded control
graph for every one of24 orders on both published and alternative layouts.
The cyclic orders ofABCD preserve the original schedule up to phase choice.
The cyclic orders ofACBD swap the first two encoded command fields and admit
the corresponding encoding adaptation. The other16 orders are explicitly
uncalibrated. All96 table/start screens (24 orders, two layouts,219 and218
versions) found no clean218 startup. Some unmerged219 phase tables do reach
clean generalized seeds, but they have not all received full primitive
verification.

The source read0 row36 participates in4,218 of the6,167 initialized-core
primitive families: every CI/CD family except register2. This was established
by a fresh complete row-usage derivation in `row36_usage/receipt.json`.
The proposed36/read0 bootstrap fixes reach clean frames but shift and split
primary register words during ordinary arithmetic; they were rejected.

## Homomorphic register transport

The original40,320-permutation census fixed logical0 and preserved literal
old syntax nodes. Its best nonidentity estimate226 was only a bound in that
fixed catalogue. It is not a lower bound on register renaming. Transporting
each physical state's entire set of logical source roles through a register
permutation preserves its internal decoder graph and can be much cheaper.

For example, exchanging logical2 and8 requires only five direct leaf-row
changes:27/0,138/0,123/0 now target56;43/0 and72/0 now target39. The changed
rows keep their write0 and rightward move. The resulting218 proposal
`rename28/published/candidate218.tm`, SHA-256
`75252ee15f2ec633195f9da453397c217f50f67eac209c091ce40fd886356158`,
passed all32 representative op/register/guard interfaces, each universal in
natural values at its literal PC. This is not a full6,167-case certificate.
Its blank startup fails. The complete876-action replacement screen for
123/read0 found only the intended0 R56 action after six additional exact-PC
interface probes. The four reused list schemas execute no123/read0 row,
as independently checked in `rename28/published/row123_block_reuse_audit.json`.

The conservative direct-selector transport admitted2,160 permutations per
layout; all4,320 resulting218 tables were screened from start0 with a3-million
step cap, without a clean seed. A broader generator keeps indirect/tagged
entries unchanged and transports their downstream direct selector rows
together. It considered all9!=362,880 permutations per layout;120,960
satisfy the shared direct-row constraints. The301→88 merge is transported
only when the new301/read0 and30/read0 actions agree. This is a candidate
generation rule, not an asserted correctness theorem for every permutation.

The complete tagged screen covered3,386,880 initial table/start
configurations. It consists of start0 for all16 calibrated phase/layout
combinations, and the six additional nontrivial first-write representatives
on each of the two base layouts. Every run closed by an exact repeated small
configuration modulo translation or by a self-loop moving into the blank
exterior before10,000 steps. There were no seed hits, timeouts, tape-limit
outcomes, or still-bounded runs. The authoritative compact receipt is
`register_transport_summary.json`.

All designated start states are covered for the two base layouts. Before
the first1 is written, the tape stays blank; a computation either repeats an
allzero state or reaches a row that writes1 on0. There are exactly eight such
states, unchanged by this generator:0,4,16,35,66,74,97,198. Starting at any
other state is therefore equivalent, up to translation and a finite allzero
prefix, to starting at one of these eight. Start35 is immediately a
blank-ray loop. Start0 and the other six were explicitly screened. The
additional phase layouts were screened only from start0.

## Bounded coordinated-row searches

The accepted alternative219 layout was also subjected to true four-row
merge/helper synthesis, including full startup windows. There were217
helper searches with keep88/drop301 and1,302 searches with the other six
keeps13,37,87,103,108,122. All1,519 searches completed without timeout or
candidate output at old-trajectory bound25, new-trajectory bound64, radius7.
These are finite topology and trace bounds, not a general impossibility
result.

On the initialized218 core, a separate identity-quotient solver resynthesized
all four rows of two retained states while preserving the checked initialized
window domain. The initial28 targeted pairs produced641 neutral solutions
and no bootstrap repair. An additional six pairs of137 with5,9,15,23,34,50
produced83 neutral solutions and249 explicit blank tests from0 and the paired
states, again without a hit. These six searches completed at radius7,
old bound25, new bound96, and a3-million-step startup cap. The expanded
630-pair run was stopped with124 recorded pair results (122 completed and
two timed out); it is incomplete and must not be presented as exhaustive.

## Remaining concrete directions

The immediate unclosed question is a bootstrap that works with the proved
218-state initialized core. Further source possibilities include joint
synthesis of a right CI6 entry with the new all-left equality macro, sharing
a new macro fragment with a retained arithmetic helper role, or removing302
without increasing source allocation cost. These remain proposals. Source
semantics, physical row roles, address contexts, complete unbounded primitive
interfaces, and exact startup must all be checked on the same final bytes.
