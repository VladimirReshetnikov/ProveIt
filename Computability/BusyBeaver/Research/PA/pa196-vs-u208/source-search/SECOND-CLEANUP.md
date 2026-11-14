# A second reachable cleanup in the PA196 source

A three-category invariant identifies a second source specialization beyond
[ZERO-TRANSFER.md](ZERO-TRANSFER.md). In the original PA196 source, old site 7
tests register 6 and takes the zero branch to site 9. The positive branch
would visit site 8, which is unreachable from the clean source seed. Replacing
the source subtree at path `00011` with its right child removes sites 7 and 8.
The tree changes from 3,812 to 3,810 leaves; its distinct internal node count
increases from 159 to 161. Its clean start is site 23, corresponding to old
site 25.

The subtree is `((dec 6, continueTo 2), breakTo 1)`. The relevant old rows
are:

| Site | Instruction | Successors |
| --- | --- | --- |
| 7 | decrement register 6 | zero: 9; positive: 8 |
| 8 | `continueTo 2` | 5 |
| 9 | `breakTo 1` | 11 |

This is a source-level reduction related to the three-category cleanup in the
incoming [PA208 optimization dossier](../../docs/pa_consistency_research_2026-10-29/).
No physical machine has been allocated from the edited source. The increase
in DAG nodes is evidence that fewer source sites do not directly imply fewer
binary machine states.

## Invariant

Start from `commandConfig 25 2 0 0 zeroStore`: the registers are
`(2,0,0,0,0,0,0,0,0)`. Track only register 6 in categories `0`, `1`, and
`≥2`. Increment maps 0 to 1 and each positive category to `≥2`. Decrement of
0 takes the zero branch; decrement of 1 takes the positive branch and yields
0; decrement of `≥2` takes the positive branch and may yield 1 or `≥2`.
Operations on other registers preserve the category, and both branches of
other-register decrements are admitted. Jumps preserve the category.

The checked inductive overapproximation contains **9,413** site/category
pairs. The possible categories at sites 0 and 4 are `{0,1}`; at site 5 and
site 7 the only category is `{0}`; site 8 has no category. The verifier checks
the initial category and every abstract successor separately after computing
the fixed point. Induction on the concrete run proves that site 7 always
has register 6 equal to zero and that site 8 is unreachable. The initial
site is well outside the removed segment.

## Halting-preserving source projections

For the second patch alone, delete old ordinals `{7,8}`, map old site 7 to
the new image of old site 9, and map all other sites by their order among the
retained leaves. The verifier compares every one of the 3,810 retained rows
under this projection, including both branches of every retained decrement.
It checks that no retained edge targets deleted positive-loop body site 8.
The removed site's reachable zero step changes no register, and its zero
successor is retained. Thus each new step matches one or two old steps; no
infinite sequence of skipped tests is possible. An induction on the matched
runs proves both directions of source halting equivalence from the clean seed.

The two patches are disjoint. Applying the earlier transfer-loop removal and
then this cleanup, or applying them in the opposite order, gives exactly the
same source tree. The combined patch deletes old ordinals
`{7,8,3773,3774,3775}`; the resulting tree has **3,807** leaves and **162**
distinct internal nodes. Mapping the two removed zero tests respectively to
the retained old sites 9 and 3776 gives equality of all 3,807 retained rows,
including both branches. The seed maps from old site 25 to new site 23. The
same bounded-stuttering induction, using the independently checked register 1
and register 6 invariants, proves halting equivalence of the combined source
from the clean seed. Both zero successors are retained, and every retained
edge into a deleted site must target one of the two forced-zero tests.

The finite graph checks use two independent resolvers: a path-bit
successor/cut implementation and an ancestor-interval/ordinal implementation.
The argument is ordinary finite mathematics and a PA-formalizable proof
outline, not an exported Lean or PA proof. It is conditional on the imported
source-to-machine startup and execution interface when used to reason about
the original literal PA196 machine; that interface is not reverified here.
Neither source edit by itself supplies a 195-state machine or the missing
internal `Con(PA) → ¬Halt(PA196)` implication.

## Reproduction

From the repository root, with Python 3.10 or later:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/verify_second_cleanup.py --output /tmp/pa196-second-cleanup.json
```

The verifier pins the source and seed definitions, checks the 9,413-pair
register-6 invariant and the previous 6,275-pair register-1 invariant, checks
both independent source resolvers, and verifies every projected retained row
for the second patch alone and both patches together. It also checks that the
patches commute and the clean seed maps to site 23. The output must match
[second-cleanup-receipt.json](second-cleanup-receipt.json). Checks use explicit
exceptions and run under `python3 -O` as well.
