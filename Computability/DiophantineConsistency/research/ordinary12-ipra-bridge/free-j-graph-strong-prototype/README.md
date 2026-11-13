# Positive ordinary strong norm for the free-J model graph

This packet derives the ordinary strong norm in every `IΣ₁` model from a
zero of the exact **95-operation free-J graph**, under the existing explicit
model hypotheses: natural ports `p` with `0<p₀`, `p₂<p₀`, `p₃<2p₀`, all
twelve coordinates positive, and `InternalZero` of the exact literal. It
is conditional on these port inequalities; it does not establish the
compact44 tuple's model interpretation or checker calibration.

In the model's difference ring, evaluate the actual graph expressions
`q,d,z,n` selected by `FreeJOrdinaryTransport.parts`, and write

```
w=n+z, h=(1−q)w²+qz²−1, b=2(1−q)w,
A=dh+q(1−q), D=db, Y=wD−A.
```

The independently audited graph integrality theorem gives `D | Y` and the
graph norm gives `A²−dqb²=0`; the prior graph composition gives `D≠0`.
`graph_signed_multiplier` constructs a **signed difference-ring** element
`i₀` such that

```
A = D i₀,       d i₀² = q.
```

It obtains `D | A` from `Y=wD−A`, then cancels the nonzero product `db²`.
The abbreviations `D`, `A` and `i₀` are proof expressions/witnesses, not
literal gates or additional quantified coordinates.

For the actual graph natural expressions

```
c=η+Y(η+ζ),  a=XY+Y,  Δ=(3+4a)+a²,  f=1+t,
```

`graph_positive_strong` binds `d=ι(c⁴)` and `q=ι[Δ(f²−1)]`, proves `i₀≠0`,
and constructs a model natural `i>0` with the explicit sign alternative
`ιi=i₀` or `ιi=−i₀`, while preserving `A=Di₀`. It proves in model naturals

```
(ic²)² = Δ(f²−1).
```

No `Δ | i` premise is assumed or derived. The theorem supplies the ordinary
strong norm, not the auxiliary positive witness, later rank recovery,
compact44 checker calibration, or an object-level proof in iPRA. The
`Classical.choice` in its Lean metatheory report is not an assertion about
which axioms occur in an iPRA proof.

## Paired evidence and limitations

The [replay](replay.py) pins the independently audited graph-integrality join
and its exact paired seed objects. Before and after the new suffix it checks
all 70 current-provider objects on each side, the graph suffix objects, and
the joined signed-integrality seed hashes, plus the matched provider
comparison. It then separately compiles the source on both sides, verifies
its exact direct import, and compares source/object hashes and axiom reports.
It reuses rather than rebuilds those audited parent chains. The graph
parent's manifest-at-read qualification, Foundation outer-wrapper,
package-transitive and dynamic-loading ancestry limitations remain.

Actual wrapper session `72917` exited `0` and printed receipt SHA
`59d42977f9c3d3969c4d115d83a2ec33fa24aba55cad87ca6dae780995f8ab58`.
The [receipt](evidence/receipt.json) records both compiler and dependency
check exits `0`, matching object hashes/reports and sampled peak RSS. The
[author](evidence/author.log) and [peer](evidence/peer.log) logs have no
warnings or `sorryAx`; both the signed multiplier and positive strong-norm
reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
reviewed monitor samples process RSS and free space, not hard quotas or
whole-process-tree usage. This new packet still needs independent audit.

The [observations](observations/) retain the actual exit-1 exploratory
sessions `82324` (parser failure and style warnings), `24761` (incorrect
case split on signed magnitudes), and `31510` (left-associated multiplication
rewrite). Their failed reports included `sorryAx`. Exploratory session
`45911` then exited `0` without warnings; the paired replay above is the
retained evidence for the current source.

When the pinned temporary parent artifacts remain available, and after
coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-freej-graph-strong-new
```
