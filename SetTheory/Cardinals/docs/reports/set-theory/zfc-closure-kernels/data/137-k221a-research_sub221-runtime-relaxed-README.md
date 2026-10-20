# Runtime reduction modulo clean resource tails

No state reduction is certified in this directory. The searches below are discovery screens. A bounded negative result is not a minimality theorem. The generalized endpoint checker is an acceptance route for future candidates, not evidence that a candidate exists.

## Observational relation and simulation argument

A source state consists of its exact logical PC and nine natural-valued logical registers. Its machine representations have dispatcher state 84 (legacy 96), a head-adjacent marker 1, the exact PC, a zero gap whose header is at distance at least 64 from the head, a header 1, nine primary blocks in the fixed physical order, and at least one spare block. Write B(v)=0 1^(v+1). The spare portion is an arbitrary nonempty finite B-list. Both exterior half-lines are zero. Absolute head position, gap excess, spare count, and spare values are not observable source data.

Suppose the exact blank startup reaches one such frame with a source-adequate initial register vector. For every source primitive and both decrement guards, require a universally quantified positive finite machine block from every related input frame to a related frame for the exact source successor, or to halt exactly for a source halt. The input quantification includes nine independent natural registers, arbitrary natural gap excess, an arbitrary first spare value, and an arbitrary finite remaining spare list.

These obligations imply source/machine halting equivalence by induction over source steps and determinism of the literal machine. Each block has strictly positive duration, so an infinite source execution produces infinitely many machine steps. The nonhalting primitive blocks do not pass through halt. A source halt produces a machine halt. Each completed block preserves a clean nonempty finite resource list and sufficient gap, so the next block's universally quantified input hypothesis holds again. No monotone spare growth is required: preservation of this invariant for every primitive already prevents resource exhaustion. Translation is harmless because the tape is two-way unbounded and the relation is expressed relative to the current head.

This argument is conditional on all primitive obligations, exact startup, and source adequacy. Finite fixtures alone do not establish any of them.

## Symbolic checker

`relaxed_runtime.py` reuses the pinned executable-induction engine from the verified K221 packet. Its literal rules, arbitrary-unary scan induction, and arbitrary finite-list traversal lemmas are unchanged and are rederived on the actual table. Only the endpoint matcher is generalized.

The matcher checks all represented tape: the left marker and full zero exterior; exact PC and nine primary affine values; a universally nonnegative gap excess; and a clean finite right tail containing at least one explicit nonnegative-valued B-block. Arbitrary finite forward B-list atoms may occur among explicit spares. It rejects reliance solely on an unconstrained list atom, which could be empty. This is conservative: some valid representations requiring a stronger count invariant are rejected. It does not silently accept junk or discard tape cells.

`verify_relaxed_candidate.py INPUT OUTPUT` snapshots a literal candidate and source, performs two independent exact startup replays, rederives the list lemmas, and attempts every guarded source primitive under this relation. It retains the fixed physical register map and native start/dispatcher/halt labels 0/84/254. Changed-source adequacy remains a separate obligation. The driver has been syntax-checked, not run as a complete new candidate certificate.

Reproduce the positive/negative unit controls with:

    python3 research_sub221/runtime/relaxed/check_matcher_controls.py

The controls cover representative CD-zero, CD-positive, CB, CI, CC, and CH cases of the exact baseline. They accept changed clean spare values/count and gap, and reject a potentially empty spare list, gap 63, a wrong primary register, and junk before the marker. The receipt explicitly does not claim a complete new runtime proof.

## Completed discovery screens

All use the exact K221 table and the 14,232 seed-invariant-admissible finite complete-frame examples from `../seed_frames.txt`. Their relaxed matcher preserves exact target PC bits and primary values while allowing clean nonempty spare-list variation, any gap at least 64, and translation. Finite buffers and fuel bounds remain discovery limitations.

- The companion `../../novel/relaxed_spare_merges.cpp` completed all 9,604 unordered pairs involving a nondecoder state and all four choices of the two original branch rows. It found no candidate after 2,076,900 checks and 591,386,090 simulated steps.
- `relaxed_eliminate.cpp` changed the incoming rows of one nondecoder state, allowing arbitrary write/move/retained-target rows. It found no candidate after 808,347 checks and 1,111,934,373 steps. It skips seven states with more than three external incoming edges, and five drops reach a node/time cap. This is not an exhausted unrestricted incoming-deletion family. Exact limits and terminal status are in `seed_eliminate.log`.
- `drop198_helper.cpp` deletes append/discriminator state 198, changes its caller 66/0, and jointly frees one of eleven kernel/caller rows: both rows of 40, 54, 97, 113, and 94, plus 66/1. Both replacement rows may target any retained working state. It found no candidate after 446,768 checks and 360,068,898 steps; none of the eleven instances capped. This screen retains old local meanings at the helper's baseline entries.

The whole-kernel screen `kernel_joint.cpp` is deliberately different: it tests only external entries of the kernel and complete source frames, permitting internal states to change meaning jointly. With state 198 deleted, fixed exit row 40/0, targets among the five retained kernel states or exit 4, and at most three changed kernel rows, it reached its 150-second limit without a candidate: 75,965 lazy nodes, 1,900,537 checks, and 363,369,539 simulated steps. This family is not exhausted. The terminal receipt is `kernel_joint3.log`.
