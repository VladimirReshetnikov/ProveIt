# Independent comparison of the three U211 proposals

## Scope and source identity

Sources were obtained from VladimirReshetnikov/ProveIt at commit
`da4ab9dd68ccfc47ac852118601eaf1fdae53795`, specifically the three U211 ZIP files in
`docs/incoming`. Their own historical comparison snapshot is
`9d50bf3df8c9e14941b549945c4f8400172d81f4`, where they compare the earlier U212
proposals. These are distinct snapshots serving distinct purposes.

All three U211 proposals start from the identical literal U212 native table,
SHA-256 `386ce16259d4c97e4af31b3ba494feaff11a0a1a066e0235dddc154b4cea38c4`, and
source SHA-256 `7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00`.
The previous U212 consensus is therefore real, but the three U211 tables are
**not identical and not merely relabelings**.

The literal/source census is freshly reproduced in
`work/comparison/comparison_census.json`. A deterministic breadth-first
canonicalization of the transition graph rooted at state 0, preserving the
read/write symbols and L/R labels, gives three different canonical graphs.
Every working state is graph-reachable, so this proves pairwise nonisomorphism
as rooted labeled transition graphs. This statement does not compare arbitrary
semantic equivalences or transformations exchanging tape directions/symbols.

## Comparison table

| Proposal | Rotations from U212 | Final local deletion | Extra runtime edit | Maximum source depth | Main comparative merit |
|---|---:|---|---|---:|---|
| Contextual | 6 | 180 -> 163; keeper 163/0 becomes 0L211 | 171/0 changes from 0L7 to 0L205 | 42 | Smallest rotation ledger and explicit repaired arithmetic reentry; substantial independent finite executor evidence |
| Research / Decoder Reassociation | 9 | 181 -> 220; keeper 220/0 becomes 0L129 | None | 42 | Useful independent predecessor-tag fold whose helper can remain fixed during the new continuation rotations |
| Rotated | 11 | 218 -> 157; no keeper row changes | None | 41 | Simplest final local proof: two cases, one old step replaced by three steps under predecessor-zero invariant |

All three have 211 working states, 422 binary rows, 3,909 primitive source
occurrences, 197 distinct source subtrees, 5,083 ordinal control-flow edges,
5,084 guarded primitive cases, and maximum source zero run 6. The primitive
word and complete ordinal control-flow graph agree across all three. Their
addresses differ. The startup is the same calibrated 48,140-step literal
blank initialization. All include initialization in the state count.

Native table hashes:

- Contextual: `ac75e2fa934e89b3c5b3e2ce5f05daa04bb71c4194566208efae03a21f7bc842`.
- Research: `7edae566b4c2e5c34d88030e0ae7caa49edda32c174b06b1a68bf9eb78567c8d`.
- Rotated: `72234980bd604524d5cd39e16f0e7f40c8547161334d65045fba5743e26db1c1`.

Pairwise differences among common native rows are 28 (Contextual/Research),
31 (Contextual/Rotated), and 29 (Research/Rotated). The deleted-state row pairs
are additional set differences. Their source addresses differ at 1,275,
3,096, and 3,096 primitive ordinals, respectively.

## Proof status and what was freshly reproduced

All three present conventional mathematical source/runtime/startup arguments
intended to formalize in PA. They explicitly inherit the numerical-calculus
and U/PA calibration; none exports a newly checked Lean, Rocq, MM0, or literal
PA endpoint for its U211 machine. The K215 formal result is relevant background
but does not certify the changed U proof-search program.

Fresh finite reproductions all pass in private copies, leaving the downloaded
sources unchanged:

- Contextual: `python3 -B reproduce.py`, return code 0, 4.556 seconds.
- Research: `python3 -B reproduce.py --quick`, return code 0, 3.399 seconds.
- Rotated: `python3 -B checks/verify.py`, return code 0, 4.060 seconds.

The logs and exact commands are in `work/comparison/replays/summary.json` and
adjacent logs. These runs freshly reconstruct the tables and sources and check
finite/source/local/startup obligations as implemented by each package. They
DO NOT freshly rederive each old package's complete 5,084 symbolic runtime
contracts. Full-runtime counts in the original packages remain inspected
historical receipts, not new runs. They report respectively 1,277,525,
1,280,108, and 1,245,944 symbolic inference applications. Those are checker-work
counts and should not be mistaken for machine runtime or a speed ranking.

No error was found in these freshly replayed finite obligations. This is not
an independent end-to-end formal validation of inherited logical calibration.

## Why the three savings cannot simply be added

The deleted states differ, but the source rotations alter overlapping decoder
rows. For example, the Research fold redirects state 220/0 backwards to
selector 129. Thereafter 129 is a live runtime helper as well as a source
decoder. Editing its rows, or rotating it as an inner node that must have one
incoming edge, can invalidate that fold. The Contextual construction instead
reuses 211 and repairs an arithmetic backward entrance to 7. Therefore the
state count arithmetic 212-1-1-1 is not itself a construction.

The useful compositional question is whether a new source parenthesization
can satisfy several local tag invariants simultaneously, while preserving
all helper semantics and the final zero-run exclusion.

## New U210 construction from Research and Rotated

The primary new composition keeps every literal row supporting the Research
181 -> 220 fold fixed. It transports the closed 78-primitive continuation at
native 116 through the changed source spine by eight new LEFT rotations:

| Step | Outer / inner | A, B, C primitive counts |
|---:|---|---|
| 1 | 162 / 203 | 503, 2515, 78 |
| 2 | 203 / 223 | 401, 2114, 78 |
| 3 | 223 / 188 | 56, 2058, 78 |
| 4 | 188 / 177 | 1042, 1016, 78 |
| 5 | 177 / 89 | 80, 936, 78 |
| 6 | 89 / 174 | 294, 642, 78 |
| 7 | 174 / 217 | 483, 159, 78 |
| 8 | 217 / 163 | 103, 56, 78 |

Each performs `((A,B),C) -> (A,(B,C))`. All 24 factors are closed: no halt and
no break, continue, or zero-decrement exit escapes a factor. Both full ordinal
control-flow resolvers agree before and after every step. Each inner physical
decoder has exactly the required single incoming edge.

The unchanged Research helper/support rows are 220/0, 220/1, 129/0, 129/1,
185/1, and 216/0. The arithmetic row 171/0 stays 0L7. Thus this composition
requires no contextual engine-entry repair.

The complete incoming inventory of state 218 becomes precisely:

- 158/0 -> (0,R,218).
- 163/0 -> (0,R,218).
- 211/0 -> (0,R,218).

Every entrance establishes a zero immediately to the left of the head. State
218 is not initial. It can consequently be replaced by 157 using the exact
whole-tape two-cell identities:

- Current bit 0: `(218,0) -> (90,1)` versus
  `(157,0) -> (67,-1) -> (151,0) -> (90,1)`.
- Current bit 1: `(218,0) -> (86,1)` versus
  `(157,0) -> (148,-1) -> (186,0) -> (86,1)`.

Only cells -1 and 0 are read. Every write preserves the scanned bit; the
exterior tape is arbitrary and untouched. The local fold therefore preserves
and reflects halting from state 0 on every common initial tape, with one old
step replaced by three and no internal halt. This all-tape claim applies to
the FINAL FOLD, not to the preceding source-address transformation as a whole.

The resulting U210 has 420 rows. Final source: 3,909 primitives, 197 distinct
subtrees, maximum depth 41, maximum zero run 6. Some intermediate layouts have
zero run 7; they are source-rearrangement intermediates, not claimed standalone
correct runtime machines. The complete final runtime remains an independent
obligation, being checked separately by the root agent.

Artifacts produced:

- `work/u210_composed/u210.native.tm`.
- `work/u210_composed/u210.tm` (dense working states 0..209, halt 210).
- `work/u210_composed/prefold211.native.tm`.
- `work/u210_composed/sites.json`.
- `work/u210_composed/recipe.json`.
- `work/comparison/compose_research_rotated.py` (discovery reconstruction).

U210 hashes:

- Native: `262032bf4237bd9c30e16ab7a3c2c4c50015a00c722ddf523e93cec0dbc51a37`.
- Dense: `9020e082ef6995d13cd571c325f4d83bf615f4d0a82e77c580353c1127a0d596`.
- Source: `a9693855883ba010144d9ac47f4c286e133b07301efb1b8379349824a2aa0669`.

## Independent U210 certificate audit

`work/comparison/check_u210.py` is independent of the builder and does not
import its source manipulation utilities. It supplies:

1. Strict table/source parsing, dense inverse relabeling, complete row equality,
   graph reachability, and target closure.
2. Source closure by leafwise counts of enclosing local 0/1 edges, independently
   of the builder's recursive signatures.
3. Two complete ordinal successor algorithms: subtree intervals and binary
   increment/cut with no-stray-one checks.
4. Fresh literal execution of ALL 3,908 internal-prefix bindings before and
   after every step, allowing the existing backward selector while rejecting
   unspecified tape reads and all writes changing a bit.
5. Complete 218 incoming inventory and both local whole-frame identities.
6. Explicit verification that the existing Research fold support and row 171/0
   are unchanged.
7. Nine semantic negative controls: wrong helper write, direction, first target,
   zero selector, one selector, zero endpoint, one endpoint, false predecessor-1
   premise, and an extra nonzero-tag entrance. They fail actual semantic/local
   checks, without relying on hash mismatches.

The audit PASSES normally and under `python3 -O`, with byte-identical JSON
results at `work/u210_composed/independent_check.json` and
`independent_check_optimized.json`. It uses explicit exceptions, not assertions.
The final prefix bindings require at most 49 literal steps.

The result is a concrete reduction below 211 relative to the supplied inputs;
no priority or global minimality assertion is justified. Further work is
exploring simultaneous preservation of the Contextual saving as well.

## Further result: all three mechanisms coexist in U209

The reduction agent subsequently found a 209-state composition at
`work/reduction_agent/u209`. Its independently audited native table is
`4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1`, dense table
`bda91bd40880f96edef104246d22797fe281355cf03610ab7e93e7923be8aa16`, source
`912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3`.

This is more than a literal union of historical patches. The U210 source
region at native174 is split into eight closed factors A..H, with lengths
26,134,52,108,136,27,103,134. It changes

    ((A,(B,(C,(D,(E,F))))),(G,H))

into

    ((A,(B,(C,D))),(E,((F,G),H))).

The old/new factor-relative addresses are respectively
`00,010,0110,01110,011110,011111,10,11` and
`00,010,0110,0111,10,1100,1101,111`. This directly exposes (F,G)=(90,211)
as native216, entered with predecessor0, while preserving the tested paths
of the existing Research helper. Native129 still has a backward call and is
not treated as a uniquely entered generic rotation node.

The three right rotations 206/199, 205/206, 7/205 retag native180's entrances
with1. Native171/0 must now be repaired to0L205. The final fold deletes180
in favor of216, with216/0 changed to0L211. Its complete incoming tag inventory
is214/0 for old216, and132/1,199/1 for old180. The two zero branches require
5 and3 new steps, respectively; both one branches require1. The5-step path
comes from composing the earlier218->157 saving with the contextual selector.

The exact paths, starting head0:

- Old216, predecessor0, current0: `(216,0)->(90,1)` versus
  `(216,0)->(211,-1)->(157,0)->(67,-1)->(151,0)->(90,1)`.
- Old180, predecessor1, current0: `(180,0)->(152,1)` versus
  `(216,0)->(211,-1)->(184,0)->(152,1)`.
- Current1 in either role: both take one step to211, head1.

All reads remain in cells-1 and0, every write preserves its bit, and no
internal halt occurs. The local final-fold time inflation is at most5;
that bound does not cover all earlier source changes.

The arithmetic repair has the original two whole-frame identities:
171->7->86 versus171->205->86 for predecessor0, and
171->7->205->164 versus171->205->206->164 for predecessor1. They take2 and3
steps and leave the complete tape unchanged.

The existing Research220 selector survives in four independently checked
cases. For predecessor0/current0 it reaches157/head1 in3 steps; for
predecessor1/current0 it reaches147/head1 in3 steps; for either predecessor
and current1 it reaches176/head1 in1 step. Its complete entrance inventory
is now185/1 and217/0. Row204/1 changes, but204 is read on0 in the relevant
helper case, and204/0 is unchanged. This context restriction is why the
bulk source rewrite can safely coexist with the helper use of129.

`work/comparison/check_u209.py` independently verifies the entire U210->U209
literal/source construction, every closed factor, both full CFG resolvers,
exact final 418 binary rows, dense isomorphism, all3,908 final internal
prefixes, all four final fold cases, both arithmetic-entry cases, all four
retained Research-selector cases, and11 semantic negative controls. It passes
normally and under `-O` with byte-identical results:
`work/reduction_agent/u209/independent_check.json` and
`independent_check_optimized.json`.

The final source has the same3,909 primitives and197 distinct subtrees;
maximum depth41, maximum zero run6. 847 addresses differ from U210.
Full source CFGs are checked at every intermediate stage, but the first two
retagging rotations produce seven-zero layouts and do NOT have a claimed
complete runtime/prefix theorem. The independent report explicitly records
these intermediate prefix failures as `NOT_A_RUNTIME_INTERMEDIATE` instead
of suppressing them. The final source and table pass every prefix check.

The reduction agent reports a fresh successful full5,084-case universal
symbolic runtime proof of this exact U209. The root agent owns its final
integration and startup/packaging validation. No new proof-assistant endpoint
is implied by that executable mathematical evidence.
