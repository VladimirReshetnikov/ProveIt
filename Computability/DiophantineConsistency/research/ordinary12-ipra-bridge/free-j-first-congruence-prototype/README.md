# Exploratory first-root graph congruence

`FreeJGraphCongruenceExplore.lean` proves, in an arbitrary `IΣ₁` model, a
new first-root congruence using the actual positive 12-variable graph zero.
Let `b = v 0 * p 0`, `q = 1+b`, and `C = q-v 1-v 2`. The theorem
`graph_congruence` assumes every coordinate is positive, `p 0 > 0`, the
literal graph zero, and the explicit alignment `v 5 = q*w`. It proves

```
0 < b,  v 1 < b,  ((p 1 + w) * C) % b = v 1.
```

The proof obtains the first root's divisibility, cancels the positive `q³`
factor via `ArithmeticModularCancellation.mul_mod_mul`, uses the positive
first-root gap to justify the natural subtraction, and verifies the output
remainder bound. The intermediate `first_pair_mod` gives the oriented pair
congruence before the alignment substitution.

`graph_aligned_congruence` composes that result with
`FreeJRadixAlignment.graph_alignment`: it assumes the explicit graph zero,
positive coordinates, port bounds `0 < p 0`, `p 2 < p 0`, `p 3 < 2*p 0`,
`46 ≤ p 0`, `4 ≤ d`, and `p 0 = Exp.exp d - 1`. Its existential `N,w`
includes `N>0`, `q=Exp.exp(d*N)`, the graph index `R` defined in the source,
`d*N≤R`, `w=Exp.exp(R-d*N)`, `v 5=q*w`, and the congruence above. All
ports are natural parameters; in particular `p 1` has not been identified
with retained compact44 K. This does not establish the weighted-word
coefficient decomposition, carry hypotheses, local decoder, actual tuple,
or an internal iPRA theorem.

Single-side exploratory session 49384 exited 0, without warnings or errors,
and printed the three axiom reports in `observations/attempt01.log` (each
`propext`, `Classical.choice`, `Quot.sound`). Source SHA-256:
`ae61e987e28267e6579c21843d989d0a960d782aa5905bc97b78d9ce28c98537`;
log SHA-256: `4419a6a1a9e55640bc29ed3ac399f4fbe600aadccdc4e12778406c840fc4717b`.
The exact command, from `Computability/DiophantineConsistency`, was:

```
LEAN_PATH=/tmp/ipra-compact-graph-derived-radix-pair-01/author/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false research/ordinary12-ipra-bridge/free-j-first-congruence-prototype/FreeJGraphCongruenceExplore.lean
```

This run used the author overlay from the graph-derived-radix pair. Its
`CompactGraphDerivedRadix.olean` SHA was
`07055d515d9fe0de2ec42196d7adca8e8eb2bb8d9195d78d4d33cb1af952ae83`;
its imported `ArithmeticModularCancellation.olean` SHA was
`c48382ae6b1af87fa6adab6ab5f54ad74d83a00d1e110fa611cf53ac57288448`.
This is an observed exploratory provider, not a new coherent source freeze,
paired replay, or independent artifact audit. Imports and their complete
ancestry were not independently authenticated by this compile.
