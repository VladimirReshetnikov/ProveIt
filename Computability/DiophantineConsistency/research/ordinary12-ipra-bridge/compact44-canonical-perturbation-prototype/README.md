# Canonical dummy perturbation, conditional on packing preservation

`CompactCanonicalPerturbation.perturb` explicitly defines the modified cell
word

```
X1(j) = X0(j) + 2^(67*1063) * δ(j).
```

The checked `perturb_definable` instance shows this word is Σ₁-definable when
the base word and selector are. Thus the exact cell-change equation and the
modified-word definability no longer need to be supplied as independent
witnesses.

The checked `chosen_rank_if_stable` theorem still has two essential
assumptions: the base `X0` satisfies the full compact `PackingInput`, and
**every** definable Boolean selector satisfying the chosen controller's
positive and nonwrapping support bounds yields a canonical `perturb X0 δ`
that also satisfies the **full** `PackingInput`. Under those assumptions it
chooses a selector and proves the explicit perturbed word has the calibrated
rank congruence. This remains a Lean theorem about models of IΣ₁ and their
definable functions, not an internal iPRA derivation.

The bounded author-side compile exited 0 in 3.508 seconds with no warnings or
`sorryAx`. Both printed axiom reports contain `propext`, `Classical.choice`,
and `Quot.sound`. The checked source is byte-for-byte the successful input;
its opening “bounded attempt” comment is historical. Direct input object
hashes, source and output hashes, dependency listing, command, log and
terminal observation are in `observations/`.

This is an incremental single-author result over the existing symbolic
controller provider, not a paired replay or a freshly authenticated closure;
inherited warnings, package/transitive/dynamic ancestry and between-check
limitations remain. The theorem does **not** establish base packing,
packing preservation, physical safety of dummy positions, retained-byte or
display binding, a positive graph zero, or iPRA provability. The outstanding
packing fields are mapped [here](../compact44-packing-obligation-map/README.md).
