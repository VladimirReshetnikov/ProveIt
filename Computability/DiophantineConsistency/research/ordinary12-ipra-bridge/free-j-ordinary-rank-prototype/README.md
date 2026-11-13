# Ordinary Pell rank intermediate for the free-J graph

`FreeJOrdinaryRank.graph_ordinary_rank` proves an intermediate ordinary
Pell-rank conclusion in every `IΣ₁` model, under the exact existing
95-operation free-J graph hypotheses: natural ports `p` with `0<p₀`,
`p₂<p₀`, `p₃<2p₀`, all twelve coordinates positive, and an internal zero of
the literal. These are conditional model hypotheses; the compact44 port
interpretation and checker calibration remain separate.

For the graph's natural abbreviations

```
c=η+Y(η+ζ), a=XY+Y, Δ=(a+1)(a+3), f=1+t,
Q=Δ(f²−1),
```

the theorem retains the previously constructed signed multiplier `i₀`,
positive natural witnesses `i,Z,y`, both sign alternatives, the actual
graph ordinate `z=ιZ`, `c<Z`, the ordinary strong norm and the positive
auxiliary norm. It additionally constructs positive model indices `p,m`
satisfying

```
c = ycoord p a,          p | m,
f = xcoord m a,          i c² = Δ · ycoord m a.
```

The proof combines the noncircular early main-index/size result with the
previous positive ordinary strong norm and invokes
`ArithmeticPellIntegralSolution.integral_solution_tsub`. It does **not**
assume or conclude `Δ | i`. Here `p` indexes `c` and `m` indexes `f`; the
later main-carrier index target is `p=R`, and it does not assert `m=R`. The
exact carrier index and the remaining carrier and checker bridges are still
open. The auxiliary norm is retained in the output for subsequent work but is
not used to manufacture the early size estimate.

This is a conditional model-level theorem, not an object-level iPRA proof or
an end-to-end consistency equivalence. The signed multiplier and auxiliary
witnesses are proof coordinates, not new variables of the literal equation.

## Paired current-provider evidence

The [replay](replay.py) pins the independently audited positive-auxiliary
parent and matched seed objects, verifies the inherited project-object
set/hashes and parent 70-source comparison, then compiles this source
separately over fresh author and peer overlays. It checks the exact direct
imports, source/object hashes and axiom reports; it does not independently
rebuild the inherited parent chains. The graph parent's manifest-at-read
qualification, Foundation outer-wrapper and package-transitive/dynamic
ancestry limitations remain. Its monitor samples RSS and free space rather
than enforcing hard quotas or measuring a whole process tree.

Actual wrapper session `46503` exited `0`, printing receipt SHA
`fc8653e042d8a04a0a304820251d9315f43360c915d31116368cd76261a23ee6`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
check exits `0`, matching objects and reports, and sampled peak RSS. The
[author](evidence/author.log) and [peer](evidence/peer.log) logs contain no
warnings or `sorryAx`; the theorem's report lists only `propext`,
`Classical.choice`, and `Quot.sound`. Exploratory session `45197` previously
exited `0`. Independent audit of this new packet remains required.

When the pinned temporary parent artifacts remain available, and after
coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-freej-ordinary-rank-new
```
