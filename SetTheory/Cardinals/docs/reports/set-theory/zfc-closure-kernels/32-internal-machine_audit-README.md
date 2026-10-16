# Independent finite audit of the public 253-state ZF/ZFC machine

This package contains independently reproducible finite results about the
attributed public machine. It does **not** claim a new blank-tape machine
equivalent to consistency with fewer than 253 working states.

Run from any working directory:

```sh
python3 verify_audit.py
```

Only Python's standard library is required. The checker validates hashes,
every partition-refinement step, the exact rejected table modification, four
complete finite tape endpoints, and the decoded instruction-path census. It
writes `audit_summary.json`.

## Source and verification status

The original Mira-Cult 254-state machine is preserved and verified in
`jeff87654/busy-beaver`, main commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. Its table SHA256 is
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.

The subsequent 253-state reduction is existing work by mira-emmy, in public
PR 20, pinned at `0d544f2a2e3c18f12278441a74b7879f31cbe856`. At this audit's
retrieval on 2026-10-16, the PR was open and its `zf253` CI job had succeeded.
The exact table is included as `data/published_zfc253.tm`, SHA256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
There are 253 working states, two symbols, 506 transitions, start state 0,
blank symbol 0 and a distinct terminal state numbered 253.

The PR's Coq endpoints relate literal blank-tape halting to finite classical
refutations of SIR, closed ZF, and the specified ZF plus choice theory.
The published job log, retrieved independently through GitHub, reports
160 rebuilt modules, 194 closed assumption reports, Coq 8.20.1 and successful
recursive `coqchk`. The selected evidence is retained in
`data/ci253_evidence.json` and `data/ci253_excerpt.txt`. This audit did not run
Coq locally. A source description, successful public CI, and a new independent
local rebuild are distinct verification claims.

The public development calls its final theory ZFC; its literal object theory
is the upstream closed ZF theory plus the specified choice-set axiom. The
development reuses the upstream relative-consistency transports for regularity
and choice. Its README explicitly distinguishes the external Coq theorem from
an internalized arithmetic consistency/proof-compiler theorem. The report must
make that distinction when discussing the user's requirement of a proof in ZFC.

Primary references:

- [Accepted 254-state development](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254)
- [Public 253-state PR](https://github.com/jeff87654/busy-beaver/pull/20)
- [Pinned 253-state README](https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/README.md)
- [Pinned endpoint theorems](https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/coq/e2e/E2E253.v)
- [Observed successful CI job](https://github.com/jeff87654/busy-beaver/actions/runs/38829452130/job/116744580063)

## Result 1: the exact 253-state table has no smaller exact state quotient

Let `P_0` identify all working states, keeping the terminal state separate.
For each subsequent round, two working states remain equivalent exactly when
their write/move actions agree for both symbols and their corresponding target
states have equal labels in the previous partition. This is a finite
transition-table computation; it makes no blank-tape reachability assumption.

The numbers of working-state classes, including round zero, are:

```text
1, 14, 60, 128, 195, 228, 235, 242, 247, 249, 251, 252, 253.
```

The next round remains at 253. A full certificate stores every class label at
every round. The last pair separated is compact states 89 and 152, with formal
branch word `101000000000`, of length 12. A formal branch word need not be a
realizable sequence of scanned symbols on one physical tape; the result here
is about an exact transition quotient.

**Proof of the obstruction.** If a transition-preserving state map identifies
two source states, it must preserve terminal status and both write/move
outputs. It must also identify the two targets obtained on each input symbol.
Induction on the refinement round therefore puts any identified states in
the same class at every round. Round 12 is discrete, so the state map is
injective on all 253 working states. Consequently no smaller machine is the
image of this literal table under an exact state quotient.

This does not exclude contextual state reuse, different initialization,
different encodings, a different interpreter, or a different proof system.
It is not a lower bound on machines with the same halting predicate.

## Result 2: shortening the zero detector breaks the existing runtime invariant

The accepted program has 6,460 instruction leaves and 6,459 internal decoder
nodes, with maximum leaf depth 34. Every instruction path has zero runs of
length at most seven. Exactly eighteen paths end in seven zeros, and all
eighteen are decrement instructions. These facts are independently regenerated
from the pinned `Prog254.v`, SHA256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.

A tempting state saving removes one step from the dispatcher's nine-zero
detector. In original 254-state labels, replace `58/0 -> 0,L,74` by
`58/0 -> 0,L,84` and delete state 74. In the public 253-state compact labels,
this changes the target of state 30/read 0 from 31 to 32, deletes state 31,
and renumbers all later states down by one. The complete resulting 252-state
table is included as `data/rejected_detector252.tm`. Its name deliberately
records that it failed the intended proof interface.

The reason the seven-zero path bound does not justify an eight-zero detector
is the phase bit following a path: it can supply an eighth consecutive zero.
The concrete path `111010010010000000` is an actual `CD 1` instruction
(logical register 1, physical register 7). Use header gap 40, all nine primary
registers zero, and three zero spare blocks. The complete initial tape is
stored in `data/detector252_counterexample.json`.

At public-machine step 205, the detector is scanning the run at head position
11. Its subsequent correct dispatch occurs at step 238, head 0. In the
shortened table, the corresponding interior detection occurs at step 203;
it reenters the dispatcher at step 205, head 11. Ones remain at positions
`-1,0,1,2,4,7`, strictly left of the apparent marker at position 10. Thus the
claimed blank-left-exterior dispatch invariant is false for that configuration.
The checker compares every cell of all four finite endpoint tapes, including
the zero exterior, by representing each tape by its complete finite set of ones.

An exploratory run-length checker additionally found 36 failed instruction
cases after this deletion, corresponding to the eighteen offending decrement
sites and their two branches. The standalone package establishes the simpler
exact finite counterexample; the count 36 is supplementary experimental
evidence, not needed for the invariant-failure proof.

The finite witness does not establish that the rejected table's blank-tape
halting predicate differs from the original one under every possible argument.
It rejects the proposed unchanged universal instruction interface. A useful
future compression target is a semantics-preserving grammar rewrite removing
all eighteen problematic trailing-zero sites without adding enough decoder
states to consume the one-state saving.

## Attribution and included data

The published table and register program are retained verbatim with their
upstream provenance. They are not new constructions by this audit. Existing
upstream author and license notices remain applicable; this package grants no
new license to third-party material. The small Python verifier and finite
certificates are accompanying audit artifacts, with the precise scopes above.
