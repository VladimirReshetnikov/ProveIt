# The literal 254-state table has no noninjective exact step quotient

Lean source check completed on 16 October 2026. The theorem
`SetTheory.BusyBeaver.ZFC.NoQuotient254.exactQuotient254_injective` in
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NoQuotient254.lean` states:

```lean
TransitionQuotient f typedMachine254 reduced → Function.Injective f
```

The target state type is arbitrary. `TransitionQuotient`, defined in
`StateReduction.lean`, requires the write bit and move to agree for **both**
read symbols at every working state, and the successor to agree after
mapping working states by `f`. The separate terminal state remains `none`.
Thus an exact one-step state quotient cannot merge any two of the literal
machine's 254 working states.

This excludes one reduction method. It does not exclude a smaller machine
with the same blank-tape halting behavior, a macro simulation with different
step lengths, a reduction depending on tape invariants, or a new compiled
program. It is not a global 254-state lower bound and proves no ZFC
consistency endpoint.

The certificate uses 14 lists of 254 cached colors, including the initial
row and 13 refinement rounds. Every initial working-state color is 1.
The terminal successor has color 0; a working successor receives its prior
color plus 1. An action is hashed from its write bit, move and successor
color, and a state is hashed from the two action hashes, using fixed
multiplier 65537 and modulus 2147483647. The argument does not assume this
hash is collision-free: collisions can only prevent distinctions. Lean
checks every cached recurrence and proves that the final 254 colors are
pairwise distinct.

The generic proof shows that states mapped to the same quotient state have
equal colors at every round. Distinct final colors then force the original
states to be equal. The final theorem's printed assumptions are exactly
`propext` and `Quot.sound`; no new axiom, `sorry`, or `native_decide` is used.

`generate_no_quotient.py` reads the pinned literal table and rejects a wrong
SHA-256, start state, terminal label or working-state label set. It generates
the cached data and the complete Lean source; its output is independently
checked by Lean. From the repository root, the inexpensive reproduction
check is:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/generate_no_quotient.py --check
```

The generated Lean source is about 42 KB. Kernel checking the finite
certificate is deliberately an optional heavy check: the observed run took
about two minutes and several GB of memory. It should be run serially and
kept outside the default lightweight umbrella. The durable record in
`results/no-quotient254-verification.json` includes the exact compiler,
source hashes, build result and printed axiom audit. Its sampled memory
figure is not a measured peak.
