# Independent review: 87/36 to 88/30 auxiliary coordinate audit

This review concerns the pinned source and graph bytes listed in `pins.json`.
The author receipt reproduces exactly. The underlying source packets are
unelaborated proposals; this review proves no Lean theorem, model graph binding,
endpoint equivalence, iPRA proof, provider coherence, or physical-PDF binding.

## Mathematical and interface findings

The positive 88/30 graph uses coordinate `u` at slot 11 and the positive 87/36
graph uses `y` there. Its other coordinates and four ports agree. With the
actual common graph fields `z=V`, `Q` and substitution `y=z+u`, the two
auxiliary residuals agree in any commutative ring, since
`u*(y+z)=(y-z)*(y+z)=y²-z²`. Both outputs are the four squared residuals
`A0²+A1²+(Fa-1)²+g72²`; the field and row checks make clear why the same
substitution leaves the other residuals unchanged. The author checks the exact
row delta and polynomial identity; our independent checker evaluates both full
graphs on 180 signed cases and compares all named fields and output. These
finite controls are not a proof of the all-model binding.

The witness construction is valid with the stated **strict** bounds. At an
auxiliary zero, `(Q-1)*(y²-z²)=z²-1>0`; hence `y²>z²`. In the old-to-new
direction, positive `u` makes `y>z`, which together with the square inequality
implies `y>0`, even for negative `z`. In the new-to-old direction, positive
`y` and the square inequality force `y>z`, so `u=y-z>0`. In an intended
IΣ₁ model these are signed difference-ring inequalities: a graph client
must supply positive model-natural witnesses from the natural cone, not
interpret signed `z` as a natural or use truncated subtraction naively. The
fact-level theorem states both bounds explicitly and uses `nonneg_iff` for
these representations. Its proof and order/cast rewrites remain unelaborated.
The checker exercises 40 positive direct and old auxiliary roots, including
both signs of `z`, and 214 elementary scaled-square cases; these bounded
controls only supplement the displayed argument.

The scaling distinction in the audit is essential. The graph first residual is
`Z²-M²*(1+m*(m+1)*k²)`, with `m=X*Y²`, `k=eta+zeta`, and
`M=q³*(J*beta)`. Positive `J` and a represented **strictly positive** beta
make `M>0`. The main residual uses `U=Y*q²>0`, with
`Dstar²=U²*(1+Delta*c²)`. A natural magnitude of each signed root plus the
positive-scale square-divisibility theorem is required before natural Pell
norms can be supplied. No `q³ | Y` premise is needed for these two root
extractions. In particular, `first_norm_of_ring_residual` accepts an already
unscaled natural `tau`; it cannot directly consume the graph's scaled `Z`.
The source-only `root_of_scaled_ring_square` proposes the missing fact-level
extraction for either sign, but actual graph residual/port casts and positive
scale bindings remain explicit work.

The common strong residual gives `(i*c²)²=Delta*(f²-1)=Q`; after moving
`Delta` across the equality this yields the natural strong norm. The proposed
bounds client additionally requires positive `X,Y,eta,zeta,i`, the precise
first and main norms, `c=eta+Y*(eta+zeta)`, the Delta identity, and the
signed field equation `z+c=f²*t`. Its use of first-Pell descent and the
main-square exclusion produces the large-k/geometry hypotheses; no positivity
of the auxiliary witness or sign/representation of `z` is assumed there.
The scaled first norm, exact field identities, and all helper proofs still
need connection and checking in a coherent model environment. The beta
representation, not a compact K0 sign, is the extra port condition claimed
by this local argument.

No concrete mathematical mismatch was found in the bounded review. The 88/30
model/endpoint and inherited 88/46/free-J ancestry are also source-only or
separately qualified; neither this audit nor its author establishes the
combined endpoint or an internal proof.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive87-to88-aux-independent/check.py | cmp - reviews/ordinary13-positive87-to88-aux-independent/receipt.json
```
