# Positive ordinary auxiliary witness for the free-J graph

`FreeJGraphAuxiliary.graph_positive_auxiliary` constructs the ordinary
strong and auxiliary witnesses together in every `IΣ₁` model, conditional
on the exact **95-operation free-J graph** hypotheses: natural ports `p`
with `0<p₀`, `p₂<p₀`, `p₃<2p₀`, all twelve coordinates positive, and
`InternalZero` of the literal. It does not prove those port bounds for the
compact44 tuple or calibrate its checker.

Evaluate the actual graph expressions `q,d,z,n` in the model's difference
ring, and put

```
w=n+z, h=(1−q)w²+qz²−1, b=2(1−q)w,
A=dh+q(1−q), D=db,
c=η+Y(η+ζ), a=XY+Y, Δ=(3+4a)+a², f=1+t,
Q=Δ(f²−1).
```

The theorem constructs a signed difference-ring `i₀` and model naturals
`i,Z,y` such that

```
i>0,  ιi=i₀ or ιi=−i₀,  A=D i₀,
(ic²)²=Q,  c<Z,  z=ιZ,
y>0,  w−i₀=ιy or w−i₀=−ιy,
Q Z²=(Q−1)y²+1.
```

Both sign alternatives are explicit. The graph ordinate itself is proved
positive and larger than `c`; the auxiliary ordinate `y` is the positive
magnitude of the signed witness `w−i₀`. The proof uses the independently
audited ordinary strong-norm multiplier and the graph's cleared auxiliary
identity. It substitutes `A=Di₀`, cancels `D²` using the proved `D≠0`,
proves the signed auxiliary witness is nonzero from `q>1` and the early
graph bound, and transports its square to model naturals. No `Δ | i` is
assumed or asserted.

This is a model-level witness/norm result. It does not yet establish final
Pell rank identities, compact44 checker calibration, or the existence of an
object-level iPRA proof of the target equivalence. The proof-only witnesses
and abbreviations are not extra quantified coordinates of the literal
Diophantine equation.

## Paired evidence and limits

The [replay](replay.py) pins the independently audited strong-norm parent,
its two matched seeds and all inherited audit/provider pins. On each side it
compares the inherited project `.olean` set and hashes with the previous
join, checks the 70-source parent, and builds the source in a fresh overlay.
It checks exact direct imports, axiom reports and matching sibling objects.
This reuses rather than independently rebuilding the prior chains. The
graph parent's manifest-at-read qualification and inherited Foundation
outer-wrapper, package-transitive and dynamic-loading ancestry limitations
remain. RSS/free-space stops are sampled, not hard quotas or whole-tree
resource measurements.

Actual wrapper session `53593` exited `0`, printing receipt SHA
`db0dce9fb7f47c6d52c18789d717d126b175df14611d05cf9719cb17b85af5f6`.
The [receipt](evidence/receipt.json) records both compiler and exact
import-check exits `0`, matching source/object hashes and reports, and
sampled peak RSS. The [author](evidence/author.log) and
[peer](evidence/peer.log) logs contain no warnings or `sorryAx` and list
only `propext`, `Classical.choice`, and `Quot.sound`. Independent audit of
this new packet is still required.

[Observations](observations/) retain the failed exploratory compiler session
`80390` (actual exit `1` on elementary rewrite/simplification errors) and the
first paired wrapper attempt (actual exit `1` before output creation or a
Lean launch because its manually transcribed provider-script pin was wrong).
Exploratory session `99715` subsequently exited `0` without warnings; the
paired replay above is the retained evidence for the current source.

When the pinned temporary parent artifacts remain available, and after
coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-freej-graph-auxiliary-new
```
