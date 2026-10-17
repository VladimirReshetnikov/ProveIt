# Upstream benchmark and broader bootstrap audit

## Exact comparison point

The merged `jeff87654/busy-beaver` default branch is pinned here to
`297ab8df7e5de329605c3875b4934643b371a5e3` (15 October 2026).
It contains Mira-Cult's 254-state machine and Jeff's Coq verification.
The stronger public comparison point is open PR 20, exact head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, with 253 working states.
The GitHub API returned the `zf253` check as completed successfully on that
exact head, at `2026-10-16T00:45:27Z`.

Primary sources:

- https://github.com/jeff87654/busy-beaver/pull/20
- https://github.com/jeff87654/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/README.md
- https://github.com/jeff87654/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/coq/e2e/E2E253.v
- https://github.com/jeff87654/busy-beaver/actions/runs/38829452130/job/116744580063
- https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/README.md
- https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/settheory/S_def.v
- https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/design/tm.md

The 253-state machine is binary, single-tape, with blank symbol 0, start state
0, working states 0 through 252 and a separate terminal state 253. It includes
every initialization state. The file contains 506 transitions and has SHA256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
The 254-state predecessor's file has SHA256
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.
Both exact hashes were independently recomputed locally.

The four old-label edits underlying the public 253-state reduction are:

| Old state/read | Write | Move | Target |
|---|---:|---|---:|
| 3/0 | 0 | L | 48 |
| 5/0 | 1 | R | 97 |
| 5/1 | 1 | R | 64 |
| 49/1 | 0 | R | 5 |

Old state 8 is deleted. Old state 5 becomes compact initial state 0, old
dispatcher 96 becomes compact 33 and old terminal 254 becomes compact 253.
The accepted boot takes 312,975 literal moves and reaches the 330th register
configuration, with gap 40, source-order registers `[5,0,0,0,2,0,0,0,0]`, and
158 spare blocks. Public source reports 160 rebuilt modules, 194 closed
assumption probes and recursive `coqchk` success. This audit inspected the
source and exact-head CI status; it did not rerun the complete Coq build.

## What is formally proved upstream

The endpoint is exact external equivalence between blank-tape halting and
finite classical natural-deduction refutations of SIR, closed ZF, or closed
ZF plus the choice-set axiom. `ZFc` uses universally closed Separation and
Replacement instances. The m253 README explicitly does not claim a new
internalized proof compiler or an internally proved consistency theorem.
This distinction matters for the user's stated ZFC-provability target.

The intervening nonextensional theory SIR has native equality, no
Extensionality axiom, and the following three components:

1. CP: every object belongs to a transitive container that contains, for each
   of its members x, an object collecting all raw subsets of x.
2. The full global-image collection schema GIC, with arbitrary formula
   matrices and parameters.
3. Irreflexivity: no object is a member of itself.

The formal comparison interprets ZF in SIR by a set-coded bisimulation
quotient, and interprets SIR in the constructible universe of ZF with
Regularity. An existing derivation-level Regularity transport removes that
extra assumption; an existing Choice transport supplies the ZFC endpoint.
Irreflexivity is used to interpret code 1, literally `v0 in v0`, as falsity
and to justify allowed binder collisions. It cannot simply be deleted from
the existing compact code/calculus while retaining that argument.

The merged README's 335-state own-line construction is not the numerical
benchmark to beat. The already public 253-state construction must be
credited to its upstream authors, even before its PR is merged.

## Extended literal audit of the already proposed sound-entry route

The already known 252-state *runtime* folds old state 5 into old state 64.
Its 504 transitions implement the original register program from an
adequate prepared tape. It loses the public initializer. ProveIt's Batch 153
source 35 at commit `ba00775e2bf56b184d071346867db74f2eb0c621` already
establishes arbitrary-cutoff safe starts and dirty-root absorption, and
examines this runtime's short-gap orbit. In particular, its diagnostic
recognizes an interior gap-32 frame after 999,186 literal moves from old
state 64; its affine checker fails after 641 further register instructions,
but that concrete instruction works in 2,794 literal moves. Its fixed-gap
model then completes a bounded million register instructions with 124
distinct local contracts. These ideas and earlier results are prior work,
not contributions of this audit. The present experiment recognizes arbitrary
complete register frames, with arbitrary unused tail blocks, arbitrary
absolute tape position, arbitrary decoded PC, and arbitrary register values.
It extends the literal full-table inspection to 100 million moves, records
all recognized gap counts and exact boundary tapes, and extends the local
contract census to every program site.

A frame is recognized only if all tape cells are accounted for: exactly one
marker to the left of the current head, a prefix decoding through the actual
6,459-node `Prog254.v` tree, all-zero padding up to the header, and a complete
finite suffix of blocks `0 1^(v+1)` with at least nine primary blocks. No
unexamined nonzero exterior is allowed. Source 35's dirty-root theorem means
zero current, cache and formula stack suffice for the structured formula
invariant; the six other fields may be arbitrary. The original diagnostic's
`sound_zero_seeds` field tests a stronger sufficient subset that also zeros
the selector and scratch fields. This naming is diagnostic, not a theorem.
No complete frame of any kind was found with gap at least 38.

The fold's blank starts collapse, before their first written 1, into seven
writer starts (old 0,7,20,42,83,95,112), or three all-blank drift classes
(old 2,10,84). The potentially complicated starts old 0,83,112 were inspected
through 20 million literal moves, as was old 95. Old 64 reaches the same
long-running trajectory as old 0. The nontrivial trajectory was then checked
from old 0 through 100 million moves. This is bounded execution only.

| Quantity, old-0 start at 100,000,000 moves | Observed value |
|---|---:|
| Dispatcher visits | 34,073 |
| Recognized frames with gap at least 38 | 0 |
| Recognized frames with gap 32 | 13,815 |
| Recognized gaps | 18,19,21,24,26,28,30,32 |
| Final state | old 131 |
| Final head | 4,720 |
| Final number of 1 cells | 5,429 |

The last recognized frames are inside AX arithmetic, at gap 32. For example,
at move 99,983,956 the site is a decrement of source register 6, path
`1110100100101001000011011010`; the physical primary values are
`[0,4,2,579,398,0,0,169,0]`, with 4,247 spare blocks. These scratch and
partially built formula values do not constitute a sound root seed. The
trajectory could still be carrying out a very long finite constructor;
this evidence does not prove divergence, eventual halting, or failure to
initialize at a later time.

The first gap-32 frame occurs at move 125,326. The maximum gap does not
increase during the remaining checked prefix. `runtime252_seed0_1m.json`
contains exact complete tapes for the record-setting frame episodes.
`runtime252_seed0_100m.json` contains the complete final tape and last frame
samples. The current inspector adds extra record-frame diagnostics to the
version used for the 100-million-step run; its actual transition loop and
acceptance predicate are unchanged.

A useful exact endpoint precedes it. From old state 0, at move 60,606 the
machine is at old dispatcher 96, head -4, PC `000` (the actual root's first
decrement), gap 19, and physical registers `[0,2,2,0,0,0,1,0,0]`, with 60
spare blocks. In source order this is
`[N,T,W,A,D,H,X,Y,L] = [1,0,0,2,2,0,0,0,0]`.
Thus `(T,W,H)=(0,0,0)`. The dirty-root formula maps it to the virtual clean
state `[2,0,0,0,2,0,0,0,7]`: here `unP(1)=(1,0)` and `P(3,0)+1=7`.
This is an admissible *structured* seed using the existing theorem. Gap 19
does not meet a uniform binary-to-register simulation bound, so this is
not a calibrated binary initializer. Source 35's theorem cannot simply be
applied through that missing tape-level bridge. The identical frame from
old state 64 occurs at move 60,614, with head 4.

## Affine gap census

The next experiment varies the affine header-gap parameter in Jeff's
attributed symbolic executor while retaining the same four register-box
summaries. All 6,460 literal instruction sites and both branches of every
decrement produce 8,391 cases. The known 252-state runtime gives:

| Gap D | Passing cases | Rejected by this checker |
|---:|---:|---:|
| 32 | 6,357 | 2,034 |
| 33 | 7,169 | 1,222 |
| 34 | 7,806 | 585 |
| 35 | 8,150 | 241 |
| 36 | 8,311 | 80 |
| 37 | 8,376 | 15 |
| 38 | 8,391 | 0 |
| 40 | 8,391 | 0 |

At gap 32, 130 cases require a leaf longer than the gap and are rejected as
negative input padding. The other failures ask the abstraction to peel a
cell from a run of length n with no positive constant term; this requires a
case split that the inherited checker does not perform. There are no fuel
exhaustions or unexpected halts in this census. The full file records every
rejected case, site, branch and message. Failure of this sufficient checker
does not prove semantic failure of the corresponding case.

The value 38 itself is **not a new discovery**: upstream `design/tm.md`
already gives it for the 254-state table. The present census confirms it for
the known folded 252-state runtime and relates it to the broader blank-run
inspection. The accepted Coq site interface still fixes D0=40. Lowering that
formal constant to 38 requires rebuilding the relevant checked theorem;
the Python census alone is not that theorem. The four generic box summaries
are gap-independent, but their actual correctness is inherited from the
published Coq development, not independently re-proved here.

## New all-site fixed-gap census and concrete obstructions

Source 35 already supplies a fixed-gap mode that replaces the affine
padding run `n+c` by the concrete run `c`, while leaving the whole register
file symbolic. Applying that existing mode to all 8,391 cases gives:

| Exact fixed gap | Passing cases | Rejected by this checker |
|---:|---:|---:|
| 32 | 7,756 | 635 |
| 33 | 8,135 | 256 |
| 34 | 8,311 | 80 |
| 35 | 8,376 | 15 |
| 36 | 8,391 | 0 |
| 37 | 8,391 | 0 |
| 38 | 8,391 | 0 |
| 40 | 8,391 | 0 |

The full gap-32 rejection taxonomy is 130 `path exceeds header`, 190
`box touched in state 73`, 154 `box touched in state 43`, and 161
`box touched in state 42`. At gap 35 the only remaining failures are the
15 depth-34 increments of source register 1, rejected as touching the box
in state 73. No fuel exhaustion or unexpected halt appears. The accepted
fixed-gap contracts continue to quantify register contents and spare data
through the inherited box summaries; only the gap is specialized. Each
gap is a separate finite check. In particular, passing 36 does not by
itself prove the universal statement for every gap at least 36. A formal
proof could combine fixed 36 and 37 with the existing affine argument
starting at 38, after porting these checks into the proof assistant.

The all-site bound 36 is an additional diagnostic result of this audit.
It improves on the prior documented affine sufficient bound 38 without
changing the transition table or program grammar. It is not a new kernel
theorem and does not alone give a smaller initialized machine: the known
blank orbit's greatest recognized gap remains 32.

Literal prepared-tape examples show that the remaining failures are not
all harmless abstraction failures. The selected depth-34 increment site
is path `1110100100101010001110000110110110` (case 763 in the census).
Start with gap 35, all nine physical registers equal to 1, and spare values
`[0,1,0]`. After 702 literal moves the first subsequent complete dispatch
frame has the intended successor PC, but gap 38 and physical registers
`[1,1,1,1,2,1,0,1,0]`. The intended result had gap 35 and
`[1,1,1,1,1,1,1,2,1]`. With gap 36, the otherwise identical input reaches
the exact intended target in 416 literal moves.

The supplied representative audit checks four value patterns (all primary
values 0,1,2,4, with the tested zero-decrement register forced to 0) at three
gap-32 rejected sites and the gap-35 site. All 16 first complete returns
differ from the intended target; four corresponding gap-36 controls return
the exact target. The file preserves input, expected and actual whole tapes
and a SHA256 digest of every executed row. These finite mismatches obstruct
the conventional instruction interpretation. They do not prove that the
TM can never accidentally reach the intended target later, or that some
different simulation invariant is impossible. The same script independently
reproduces source 35's positive 2,794-move literal check, correctly crediting
that prior affine false alarm.

Simple program/header overlap also has a direct obstacle. Of the 85 leaves
at depth 33, 50 require bit 0 at offset 32 and 35 require bit 1. Of the 30
leaves at depth 34, 15 have suffix `10` and 15 have suffix `11` at offsets
32 and 33. A fixed header 1 followed by the first register delimiter 0
therefore cannot encode every intended leaf. For example, the depth-33
decrement path `111010010010101000111000011011010` is changed by that forced
header into its depth-34 increment sibling. This rules out the simplest
literal overlay invariant, not all alternate encodings.

There remain two concrete objectives: rebracket or otherwise change the
grammar to reduce the deepest decoder paths without increasing the count;
or prove that the actual short-gap bootstrap has a restricted safe
instruction sequence until it produces a sound root at a sufficient gap.
The latter needs a proof about reached data and PC, because arbitrary
short-gap instructions genuinely alter the decoded registers. No such
all-future or finite complete-bootstrap invariant is proved here.

An absent primary register cannot simply be treated as a zero register on
the existing tape representation: value zero is encoded by `01`, whereas
the exterior is all zero. A rigorous lazy-allocation variation would need
instruction-dependent bounds proving every selected block already exists;
positive decrements append one zero block. No missing-block inference was
used by this experiment.

## Reproduction and dependencies

Run from any directory with Python 3 and the preserved local layout:

```sh
python inspect_runtime252.py --start 0 --limit 1000000 --output runtime252_seed0_1m.json
python inspect_runtime252.py --start 0 --limit 100000000 --output runtime252_seed0_100m.json
python affine_gap_audit.py --output runtime252_gaps.json
python exact_gap_audit.py --source35 ../source35_runtime252_short_gap.py --output runtime252_exact_gaps.json
python representative_gap_checks.py --source35 ../source35_runtime252_short_gap.py --output runtime252_representative_gaps.json
```

The scripts require exactly these upstream functional inputs:

- `upstream/ZF/m254/machine/zfc_254.tm` (exact pinned original table).
- `upstream/ZF/m253/tools/generate_candidate.py` (public four-row reduction
  and explicit old/compact bijection; it verifies the original table hash).
- `upstream/ZF/m254/coq/tm/Prog254.v` (literal program tree).
- `upstream/ZF/m254/tools/tm/symexec.py` (only for the gap audit).
- The exact prior `source35_runtime252_short_gap.py`, supplied at the
  explicit `--source35` path, for the fixed-gap and representative audits.

The scripts do not access the network or invoke a proof assistant. Their
simulator and frame recognizer are new diagnostic code. The affine executor
and register-box summaries are Jeff's existing code, the fixed-gap adapter
is ProveIt's prior source 35, and the 253-state generator is the public PR's
existing code. Preserve their authorship and
provenance rather than describing the complete audit as independently
implemented or formally verified.

## Notices

The retrieved upstream tree has no repository-wide top-level LICENSE file.
Its supplied component notices include Wade's MIT No Attribution notice,
busycoq's MIT notice, LibTactics' MIT-X11 notice, and the Coq Library of
Undecidability Proofs' MPL-2.0 notice. Copies are preserved under their
original paths in `upstream/`. The m253 README says it adds no new license
grant. Do not infer that one component's license relicenses all contributed
proofs or optimization artifacts. The audit records these source facts and
does not supply legal advice.
