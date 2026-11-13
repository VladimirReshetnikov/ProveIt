# Independent audit of the 91-operation X=q·w candidate

The pinned 91-operation graph is the pinned 92-operation graph after
replacing the positive witness `X` by `q*w` and factoring two shared
expressions. It has exactly 91 live binary operations: 50 multiplications,
24 additions and 17 subtractions. `w` replaces `X`; all other positive
witnesses and all four fixed ports retain their positions. This count excludes
a later `x+1` substitution.

An independent node-map comparison checks every old and new graph row,
including all changed operands, the input order, topology and output
reachability. Exact sparse integer-polynomial calculations certify the two
factoring identities, using independent ring variables:

```
Bt_old = C*(X + K0*q) - F*q = q*(C*(w+K0)-F)
U*gamma + E*q = U*(gamma+w),  where X=q*w, E=X*Y, U=Y*q².
```

The checker additionally evaluates both complete graphs at 400 positive
integer assignments. Those samples are sanity checks; the exact graph and
polynomial checks do not rely on them. The graph correspondence remains an
external check, not a Lean expression equality theorem.

## Degree

The fixed-coefficient polynomial has exact total degree **172**. The exact
identity `h=(V+n)²−1−Q*n*(2V+n)` gives the upper bounds
`deg Q≤14`, `deg V≤8`, `deg h≤23`, `deg den≤20`, `deg polarT≤28`,
`deg polarA≤43`, `deg polarCorrection≤78`, and `deg N≤86`; the output degree
is at most 172. Hash-checked retained fixed payloads with witness number `i`
substituted by `(i+2)*t` give a degree-172 polynomial modulo 1,000,000,007
with leading coefficient 960910299. This proves the matching lower bound.
The calculation and the external coefficient-file binding are not Lean
file or polynomial-degree theorems.

## Scope of the proposed model bridge

A checked 91-graph Lean bridge is not yet available. The existing
`FreeJCompactBeta.compact_graph_alignment` supplies a route for the fixed
symbolic ports, subject to its actual hypotheses. It requires an internal zero
of the **95-operation free-J literal**, strictly positive coordinates,
positive beta, `MC < beta`, `MF < 2*beta`, and the natural-number equality
`beta = 2^590069−1`; under those conditions it constructs a model element
`w` with `X=q*w`.

For a positive zero of the 92 graph, the already checked 92-to-94 transformed
model theorem and 94-to-95 bridge provide the required old literal zero at
`Y=q³*s`, without changing `X` or `J`. `CompactFixedBeta.bounds` provides the
three model port inequalities for the symbolic port tuple. Its beta is
`2^(67*8807)−1`, and `67*8807=590069` supplies the required numeral equality
without expanding the large exponent. Since the old `X` is positive, the
alignment witness `w` cannot be zero. Replacing `X` by that positive `w`
and using the two exact graph identities would give the reverse existence
map; substituting `X=q*w` gives the forward map because `q>0`.

This argument is conditional on the fixed symbolic ports and their bounds;
it is not an arbitrary-port equivalence. The necessary Lean 91 expression,
all-model proof, coherent provider join, serialized ancestry checks,
file/PDF binding and internal iPRA endpoint remain separate work. The
existing `FreeJCompactBeta` result has a historical paired suffix replay,
with its own inherited provider and package/dynamic ancestry qualifications;
its compatibility with a new combined provider still needs to be checked.

Run `python3 -I -S -B check.py` from this directory, or pass its path from
another directory. The checker pins both graphs, the supplement binding and
all four compressed payloads before and after; its captured run exited zero
with empty stderr in `observations/stdout`. No Lean process was started.
