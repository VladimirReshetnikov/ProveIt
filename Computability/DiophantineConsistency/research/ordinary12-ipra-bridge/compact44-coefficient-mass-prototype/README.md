# Finite compact44 coefficient mass and carry slack

For the separately checked Lean list of 943 compact rows, the source evaluates
the selector payload `v = west + 2^8 north + 2^17 east + 2^25 south + 127·2^34`
and its coefficient `1 + 2^10(2^41−v)` for each row. It checks all payloads
are strictly between zero and `2^41`, and proves the exact natural-number
totals

```
selector sum     = 12734826094758831
41 copy weights  =  2251799813684224
coefficient sum  = 14986625908443055
stencilMass      = 29973251816886116 = 2·coefficient sum + 6.
```

It also proves `3·stencilMass + 1 < 2^66` and the two concrete inequalities
`3·stencilMass + 1 + 2^66 < 2^67` and
`3·stencilMass + (2^67−1) + 1 ≤ 2(2^67−1)`. These are the numerical forms
needed by a possible half-radix predecessor reset and a heterogeneous-cap
carry bound, respectively. They do not supply the graph-specific hypotheses
needed to apply either bound in a model.

The exact Lean table and its comparison with the retained JSON were previously
paired and independently reviewed. The recipe's identification of the 41
weights and `2·coefficient sum+6` with its actual current, spatial and
temporal stencil remains a separately checked finite source interpretation;
this file does not establish a Lean equality to K, an all-model decomposition,
a cyclic rotation bound, a carry reset, machine simulation, or an iPRA proof.

The first exploratory session 74571 exited 1 because two `decide` tactics
were invoked after `rw` had already closed their goals. The corrected session
63389 exited 0 for the original five declarations. Session 74385 exited 0
after adding the payload range and two explicit slack declarations; all eight
reports list only Lean metatheory `propext` and contain no warnings or
`sorryAx`.

The paired replay was run as

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-coefficient-mass-prototype/replay.py --output /tmp/ipra-compact-coefficient-mass-pair-01
```

Outer session 96941 actually exited 0; both Lean children exited 0, with
matching objects and exact axiom reports, and the independent 943-row parent
audit was rerun before and after. The evidence and exact terminal observation
are retained here. This packet awaits independent audit. The inherited window
provider lacks a complete printed axiom inventory; package-transitive and
dynamic ancestry are not fully authenticated, and reported RSS is sampled.
