# Literal-table reduction searches from K224

The reference is `portable/machine/results/candidate224.k.tm` in
`K224_Construction_2026-10-20.zip` at ProveIt commit
`49ee7cfdc8e0364c6db3614675d141d66f9350ed`.
Its SHA-256 is `f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f`.
It has 224 working states. No candidate with fewer states was found by these searches.

## Search models and results

1. Direct removal of one state, redirecting all incoming edges to an existing state: no result with a 20-step positive simulation block.
2. Contextual merging of two states, synthesizing both rows of the retained state: no result with 18-step blocks and all 4 x 225 possible first actions per row. Initial local facts were inductive intersections of incoming-transition facts in a radius-six window.
3. Direct removal with a head displacement of +2 or -2, obtained by reversing all incoming directions to the deleted state: no result.
4. Contextual merge with that head displacement and resynthesized retained rows: no result.
5. Direct removal with a bounded common continuation, allowing up to five reference steps and sixteen candidate steps: no result.
6. The same full contextual merge screen on the root agent's `All_ab_0` helper variant (225 states): no result.
7. An alternative 224-state fold of Rel225 was found and checked, but it has no further fold in the full contextual screen described above.
8. There were 448 individually sound row replacements preserving the state count. The known-cell backward-action fold screen found no smaller table after any one of these rewrites.
9. Seventeen further macro row replacements were found, allowing up to three reference steps and twelve candidate steps. Full contextual resynthesis found no smaller table after any one of these rewrites.
10. A deterministic random walk accepted 1,600 composed sound neutral row replacements, resetting to the baseline every fifty iterations. No smaller table was found by the known-cell fold screen.
11. A stronger finite-window abstraction computes reachable sets of complete bit patterns rather than a conjunction of constant bits. With radius six, it retains 295,165 abstract state/window configurations. Full contextual resynthesis found no fold using either conditional constant facts derived from those patterns or the full relational pattern sets.
12. No fold was found using those full relational pattern sets together with a +2/-2 displaced representation.
13. No fold was found using a manufactured predecessor tag: flip the write bit of every transition entering a deleted state whose incoming moves are all rightward, map that state to an existing state, and restore the predecessor bit within a positive simulation block. This representation was checked against the original full tape, so the manufactured bit was never treated as semantically disposable.

These are scoped negative search results, not lower bounds on machine size. In particular, the first-action restrictions in the fast known-cell screen, local block limits, conjunction approximations, bounded tape windows, fixed source program, and the chosen representation changes limit coverage.

## Alternative 224-state fold

Relative to the pinned Rel225 parent, identify K191 with K157 and use:

```
157 0 0 L 67
157 1 1 L 187
```

All other rows are unchanged after the state identification. This differs from the released K224 fold only in the target of K157/read1, where the released table uses K148.

The four blocks are:

- K157/read0: 157 -> 67 -> 151 -> 90, three steps.
- K157/read1: 157 -> 187 -> 186 -> 86, three steps.
- K191/read0: 157 -> 67 -> 152 -> 159 -> 118 -> 155, five steps.
- K191/read1: 157 -> 187 -> 76 -> 148 -> 173 -> 182, five steps.

They preserve the whole tape and the original one-step endpoint, under the same predecessor tags as the released fold. This is an equivalent 224-state table, not an improvement on the user's requested bound.

## Finite-window invariant method

For radius r, an abstract configuration consists of a control state and all
2r+1 bits at offsets -r through r around the head. Initially every binary
window is allowed at state 0, so the invariant is valid for every binary
initial tape and initial head position. Each literal transition writes its
bit, shifts the window by one cell, and permits both values of the newly
entering exterior bit. Reachability in this finite directed graph is a sound
inductive overapproximation of concrete configurations.

The relational search restricts symbolic branches by membership in the
reachable window set. It checks exact whole-tape endpoints; every exterior
cell is represented by an arbitrary initial bit, and a modification to an
exterior cell is rejected unless equality with its required final value is
proved. All accepted simulation blocks have positive length and no interior
halt. This method can be packaged as an independently checked finite
certificate if it eventually yields a useful reduction.

## Important rejected shortcut

Shortening the eight-zero reset to seven still fails when the spare list
contains only ones. The retained counterexample source instruction
`11101001001000000 / CD1`, all nine logical registers zero, fails with one
spare of value 1 and with 167 spares all of value 1. Thus the actual bootstrap's
nonzero spare invariant does not repair the reset shortcut.

## Files

The scripts in this directory are research tools and currently refer to this
conversation's input paths through `search_folds.py`. `TABLE_INPUT` overrides
the K-label input table. Every claimed positive rewrite is rechecked against
the mutated table, so self-referential parent/child detours that would become
loops after merging are rejected. The Rel225 control search correctly
rediscovers the released K157/K191 fold.
