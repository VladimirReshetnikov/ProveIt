# Calibrated rank conditional on realization of the dummy selector

`CompactChosenRankIfRealizable.chosen_rank_if_realizable` connects the
chosen-power symbolic controller to the conditional rank-variation theorem
on one author-side provider. **Its central physical realization assumption
is not proved here.**

For arbitrary model `T, MC, HP, c`, the theorem assumes a definable base word
`X0` satisfying the full `PackingInput` for the actual symbolic
`paramKernel rho` at the chosen `N` and `w`. It additionally assumes that,
for **every** definable Boolean selector `δ` satisfying the controller's
positive and nonwrapping support bounds, one can supply a definable modified
word `X1` which satisfies the same full `PackingInput` and

```
X1(j) = X0(j) + 2^(67*1063) * δ(j),  j < N.
```

Under those explicit hypotheses the theorem chooses one controller selector
and its supplied modified word, retaining their definability, support,
packing and cell-change facts, and proves the modified window rank is
`590069*w` modulo `590069*N`. This is a Lean theorem about arbitrary IΣ₁
models and their definable functions; the quantified realization assumption
has not been supplied or formalized as an internal iPRA derivation.

The bounded author-side compile actually exited 0 in 2.779 seconds without
warnings or `sorryAx`. Its axiom report lists `propext`, `Classical.choice`,
and `Quot.sound`. The source is byte-for-byte the successful input; its
opening comment describing an uncompiled bridge is historical. The command,
source and object hashes, direct checked input hashes, dependency listing,
log and terminal result are retained under `observations/`.

This is an incremental single-author build on the symbolic controller
provider, not a paired replay or freshly authenticated project/package
closure. Earlier provider warnings, transitive/dynamic ancestry and
between-check limitations remain. In particular, the theorem does not prove
that the base or modified words exist, that selected positions are physically
safe dummy cells, that retained bytes or displayed coefficients match the
symbolic K, that a positive graph zero exists, or that iPRA proves the intended
equivalence.
