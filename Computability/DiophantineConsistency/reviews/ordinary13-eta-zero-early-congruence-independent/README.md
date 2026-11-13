# Independent source review: eta-natural early congruence

The pinned source in `research/ordinary13-eta-zero-early-congruence-model-draft/`
is a conditional, unelaborated fact-level proposal. Its author's deterministic
checker reproduces. This review adds separate source pins, exact free-ring
identities, graph-cut checks, and 3,500 finite factor-cancellation controls;
run `python3 -I -S -B check.py | cmp - receipt.json` in this directory. The
finite controls do not prove the imported theorem in arbitrary models, and
neither checker runs Lean.

For `Y=q³s`, the source's `U=Yq²=q⁵s`. With `a=XY+Y` and `H=3+4a`,
the defect of the asserted oriented balance

```
U*main + H*k = U*(X+a*c) + H*(U*gamma+R+1)
```

is the negative of the defect in the additive identity used for the modular
reduction. Therefore a zero balance defect gives
`H*(R+1) ≡ H*k (mod q⁵)`. The proof requires `q>0` so the modulus is
positive. `dvd_magnitude_of_mod` takes the residues in exactly this order and
returns divisibility of `magnitude (H*(R+1),H*k)`. The magnitude definition
is the sum of both truncated differences, so multiplication by model-natural
`H` yields `H*magnitude (R+1,k)` provided the claimed `mul_tsub` rewrites
elaborate. No order between `R+1` and `k` is assumed.

The imported `cancel_factor_three` takes **exactly** `q>0`, `q³ ∣ Y`, and
`q⁵ ∣ (3+4Y(X+1))*t`, and returns `q⁴ ∣ t`. Here `t` is the natural magnitude,
`q³ ∣ Y` uses witness `s`, and `H=3+4Y(X+1)` is a free-ring identity. Its
source handles both `3 ∣ q` and `3 ∤ q` by cases; the client supplies no
extra `q=3t+2`, coprimality, or Bézout assumption. This review verifies the
interface and algebra, not the imported source's Lean elaboration or an axiom
report.

For the signed main norm client, `DirectMainNorm.direct_main_orientation`
expects exactly `P=U*(X+a*c)+H*(U*gamma+R+1)`, `N=H*k`, and the magnitude
square `U²*(1+(H+a²)c²)`. Its conclusion has the orientation
`P=N+U*main`; negating that balance yields the equation above. The call uses
`U>0`, derived from the explicit `Y≥8` and `q>0`, plus explicit `k>0`.
The prototype's checked cut has `kbase=k−1` in the difference ring and
`Dstar=P−N`, with **no `X*Y*q` term**. Extracting that natural signed pair,
including the graph rank representation and actual factor equations, remains
a separate model-level obligation. No eta-positive premise is used in this
fact-level source.

The first-index call passes `(q,X,Y,k,R,tau,s)` in the declared order,
including the positive `Y` derived from `Y≥8`, the first natural norm,
`R≥24`, the full rank window, and the preceding magnitude divisibility.
Its returned witnesses are the same `n,w` across the eight result conjuncts:
`13≤n`, `n≤k`, first x coordinate, doubled y coordinate, the q⁴ remainder,
the two lower bounds, and the exact `k=2n+4XY²w` decomposition. In
particular, `(2n)%q⁴=R+1` is an **early residue**, not `2n=R+1`; the later
`R≥26`, exact-index and auxiliary facts are not supplied. The finite
recurrence/model source remains a separate unelaborated dependency.

No mathematical interface mismatch was found in the inspected cuts. This
is not a complete graph-to-norm or iPRA proof: `q,Y,X,k` positivity, the graph
first/main norms, rank/window and compact port casts, the actual graph-zero
to unit-factor argument, provider compatibility and Lean elaboration are
still separate obligations. The prototype is a structural experiment rather
than an established equation reduction.
