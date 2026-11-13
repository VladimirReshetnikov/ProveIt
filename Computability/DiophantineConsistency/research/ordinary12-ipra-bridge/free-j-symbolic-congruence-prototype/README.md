# Exploratory same-witness symbolic digit and congruence client

The source is a separate extended copy of the first-root congruence source in
`../free-j-first-congruence-prototype/`; it does not modify that packet or
its source pin. It adds `symbolic_aligned` and `fixed_symbolic_aligned`.

For the fixed symbolic beta, low mask and high mask, arbitrary natural `K`,
and positive variables satisfying the literal graph zero, the latter
obtains **the same** model values `N,w` with `N>0`,
`q=Exp.exp((67*8807)*N)`, the repunit identity for `v 0`, the graph alignment
`w=Exp.exp(R-(67*8807)*N)` and `v 5=q*w`, the strict bound `v 1<q-1`, the
congruence `((p 1+w)*C)%(q-1)=v 1`, `dig 67 C 0=1`, and all digits of `C`
below `8807*N` bounded by three. Here `p` is the specified symbolic tuple,
`q=1+v 0*p 0`, `C=q-v 1-v 2`, and `R` is the exact expression in the source.
The proof obtains the witnesses from the aligned congruence theorem and calls
`CompactGenericGraphDigits.graph_digits` with that same `N`; it does not
identify unrelated existential witnesses. The generic preceding theorem
retains explicit model beta and low/high natural-port equalities.

Actual exploratory session 2091 exited 0 without warnings or errors using
this source; the five exact axiom reports are in `observations/attempt01.log`.
Each reports `propext`, `Classical.choice`, and `Quot.sound`. Source SHA-256
`d748f8bbad7a45a328322eec1acd4643bc3e2c3f40d015b6b653f790fd8978d0`;
log SHA-256 `1ba65911276460756f4614b964722ab6a249af780818c8055b2119bb379ae15b`.
The command, from `Computability/DiophantineConsistency`, was:

```
LEAN_PATH=/tmp/ipra-compact-graph-derived-radix-pair-01/author/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false research/ordinary12-ipra-bridge/free-j-symbolic-congruence-prototype/FreeJGraphCongruenceExplore.lean
```

This is a single-side exploratory compile against the author graph-derived
radix provider, not a coherent paired source freeze or independently audited
artifact. It does not bind K or the symbolic masks to retained bytes, construct
weighted cyclic words or a carry argument, decode the machine, or give an
internal iPRA proof.
