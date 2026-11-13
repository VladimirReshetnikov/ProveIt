# Eta-zero index route: bounded source-interface audit

This packet investigates a possible future removal of the positive shift on
`eta` in the pinned 13-input graph. It does **not** contain a modified graph,
prove that an eta-zero graph has no zeros, establish two zero maps, or claim
an operation reduction. The source inventory is lexical; it is not Lean
elaboration or an iPRA proof. The pinned graph and source hashes, exact tested
rows, checked declaration names, and reproducible controls are in `check.py`.

Run from this directory with

```
python3 -I -S -B check.py > /tmp/eta-zero-index-audit.json
cmp result.json /tmp/eta-zero-index-audit.json
```

## Conditional parity route

Let `ycoord(t,a)` denote the main Pell ordinate in the pinned recurrence.
If a putative eta-zero graph zero could be shown to give all of the following
facts in the relevant arithmetic domain,

* `eta = 0`, `c = eta + Y*k`, and `k` is even;
* `c = ycoord(R,a)` and `2*n = R+1` for natural `n,R`;
* `ycoord(R,a)` has the same parity as `R`,

then `c=Y*k` is even, while `R` and therefore `c` are odd: a contradiction.
For ordinary integers, the parity statement follows by induction from
`ycoord(0,a)=0`, `ycoord(1,a)=1`, and the pinned `y_two_step` identity

```
ycoord(t+2,a) + ycoord(t,a) = 2*(a+2)*ycoord(t+1,a).
```

The model-level version still needs an explicit internal induction proof,
including the definability/induction interface for the recurrence. The
checker's 2,160 finite modular controls are illustrations only; they do not
prove either the parity lemma or the remaining bullets in an arbitrary
IΣ₁ model. The existing `ArithmeticPellFirstNorm.even_ordinate` source gives
an even-ordinate theorem when its first-Pell norm hypothesis is supplied;
using it here also requires a graph-specific extraction and identification of
the positive parameter, including the predecessor at `m-1`. No graph zero is
claimed to provide these hypotheses by this packet.

## Exact index interface

`P72Exact.indices_ordinary` concludes `13 ≤ n`, `n < m`, `m = R`, and
`2*n = R+1`. Its hypotheses include `0 < eta` and `c = eta + Y*k`, plus
first-Pell indexing and congruence, a main-Pell index and norm, a strong norm,
and an auxiliary offset equation. Consequently it cannot be instantiated at
`eta=0` as written. `check.py` pins and extracts the literal lines containing
`hη` in the two relevant declarations:

* `index_window` uses it for `c>0`, `k<c`, and `2*R<c`.
* `indices_ordinary` passes it to `index_window` and uses it to prove `2≤c`.

There is a plausible replacement for these **specific** uses, conditional on
the remaining hypotheses: obtain `k>0` from the existing rank/congruence
argument, then derive `c=Y*k>0`; derive `k<c` from `Y≥2` and `k>0`; retain
the strict first step `2R<2(R+1)` in `2R<2(R+1)≤2k≤Y*k=c`; and derive
`2≤c` from `k≥1` and `Y≥2`. This is a proposed proof adaptation, not a
checked generalized theorem: binder dependencies, rewrites, all hypotheses,
and elaboration still have to be established. The scan is restricted to
literal `hη` occurrences in these two pinned declaration bodies; it is not a
proof that no other source dependency on positive eta exists.

The hypotheses most requiring a graph-specific bridge include the first norm
and its index congruence, the `q⁴` congruence/rank bound, signed main-root
orientation, strong norm, and auxiliary offset equation. In particular, the
modified graph's carrier and valuation must be matched directly: a theorem
for a different literal graph or carrier cannot simply be instantiated by
analogy. The index theorem's variables `n` and `m` are Pell indices; they are
not the scale `m` used below.

## Auxiliary-offset interface

For one possible route, suppose a graph-zero extraction has already supplied
natural `X,Y,k,f,i,T,R,y` and signed `V`, with `X,Y,i>0`,

```
scale = X*Y² > 0,       k ≥ 8*scale+4,
a = Y*(X+1),            A = a+2,
c = Y*k,                Delta = A²−1,
I = i*c²,               I² = Delta*(f²−1),
V = f²*(T*c−R)−c,       Q = I²,
(Q−1)*(y²−V²) = V²−1.
```

These are **assumptions**, not facts extracted from the pinned graph by this
packet. Under these hypotheses ordinary ordered integer arithmetic gives
`c>A`, `c>1`, and `0<Delta<c³`. If `f²≤c+1`, the strong norm would give
`I²≤Delta*c<c⁴≤I²`; thus `f²>c+1`. Since `V+c` is divisible by `f²`,
`|V|≤1` would force a positive multiple of `f²` between `c−1` and `c+1`,
impossible. Hence `|V|>1`; also `Q=I²>1`, and the last displayed equation
gives `y²>V²`, so the natural `y` satisfies `y>|V|` and `u=y−V>0`.
This explains a potential positive offset without assuming the desired
positivity at the outset. An IΣ₁-model client must still supply the signed
ring/absolute-value and order reflection steps, exact graph bindings, and
all displayed hypotheses.

`AuxRootBounds.first_ordinate_large` is an unelaborated source draft with
hypotheses `scale>0`, `k>2`, and `tau²=1+scale*(scale+1)*k²`; it concludes
`k≥8*scale+4`. Establishing its hypotheses for this graph, including
excluding `k=1,2`, remains work. `AuxGeometry.geometry_of_large_k` is also a
source draft and explicitly requires positive eta, so it cannot be applied
unchanged at eta zero. `AuxRootBridge.positive_aux_coordinate_iff` is a
source-draft interface that requires its own `Q>1` and `z²>1` hypotheses and
specific five-squares expressions. Its existence does not establish their
binding to the product graph.

## Outstanding proof boundaries

1. Derive factor units and the needed first, main, strong and auxiliary
   equations from a zero of a precisely defined eta-unshifted graph in every
   intended model, with the pinned compact ports and their representation
   assumptions. The existing standard-integer factor argument and theorems
   for other graphs cannot substitute automatically.
2. Prove positivity and bound prerequisites without assuming eta positivity,
   including `X>0`, the rank facts, root orientation, `k>2` and the displayed
   auxiliary hypotheses; justify each signed-to-natural conversion.
3. Prove and elaborate the eta-zero generalization of `P72Exact`, and construct
   its first-index, congruence, main-index and offset witnesses from that graph.
4. Prove the parity invariant internally for all indices, not merely standard
   numerals, using a suitable model induction/definability interface. Compose
   it with the exact graph and both zero maps, then establish the applicable
   endpoint and port provenance separately.

None of these obligations is discharged by the finite controls or this source
inventory, and the user's existing displayed equation is unchanged.
