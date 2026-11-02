# Unique ordinary carrier index

`FreeJMainIndexUnique.graph_ordinate_index_unique` proves in any model of
`IΣ₁`, for the exact free-J literal, positive coordinates, `p₀ > 0`,
`p₂ < p₀` and `p₃ < 2p₀`, that **any** index `m` satisfying

```
ycoord m (v₅v₆+v₆) = v₈+v₆(v₈+v₉)
```

equals the literal's rank `R`. The proof composes the independently audited
exact-ordinary theorem, which constructs such an index `π=R`, with strict
monotonicity of the Pell y-coordinate. In particular, the index extracted by
the prior main-carrier comparison is equal to `R` once its displayed
ordinate equation is supplied. This makes reusable a step previously local
to `FreeJPowerFinish.graph_power`; this theorem does not need that theorem's
additional `β≥46` hypothesis.

The result is a conditional model-level theorem. It does not calibrate the
compact44 ports or checker, establish machine simulation, construct an iPRA
derivation, or identify an index lacking the displayed y-coordinate equation.
The first exploratory session 20475 exited 1 because the namespace
containing `y_strictMono` was not open; its [source](observations/attempt01.lean)
and [log](observations/attempt01.log) are retained as failure evidence, not
proof. The corrected session 64701 exited 0 with the expected axiom report
and no warnings.

The paired replay was run as

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-main-index-unique-prototype/replay.py --output /tmp/ipra-freej-main-index-unique-pair-01
```

Outer session 55299 actually exited 0 after two matching compilations and
before/after reruns of the exact-ordinary parent audit. The author and peer
reports list Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`,
with no warnings or `sorryAx`. The packet awaits independent review. The
graph manifest-at-read qualification, Foundation's unobserved outer-wrapper
exit and package-transitive/dynamic ancestry limitations are inherited;
reported memory use is sampled, not a whole-process quota.
