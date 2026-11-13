# Proposed zero-ordinate main-norm obstruction

This is an unelaborated fact-level source proposal, not a graph-zero theorem,
a zeta-forcing theorem, an equation reduction or an internal proof. It assumes
model naturals `q,Y,X,w` and signed z,t satisfy

```
q≥2,  q³≤Y,  X=q*w,
U=Y*q²,  H=3+4*Y*(X+1),
z=U*X+H*t,  z²=U².
```

The proposed conclusion is falsehood. It is tailored to the eta=zeta=0
boundary of the separate 85-row structural probe, where k=c=0 and the
actual main root is `U*X+H*(U*gamma+R+1)`. A literal graph zero has not been
shown here to yield the required main norm: the product-of-factors unit
extraction and all graph/model/port bindings must be reproved for the changed
literal.

The mathematical route is independent of the sign or natural representation
of t or R. The square equation gives z=U or z=−U in the difference-ring
integral domain, hence H divides U*(X−1) or U*(X+1), respectively. Since
X=q*w and q≥2, X is either zero or at least two. Thus each branch supplies
a natural L=|X−1| or L=X+1 with `0<L≤X+1` and H dividing U*L. If
`U*L=H*t0`, the explicit certificate

```
3*q²*L = H*(q²*L−4*(X+1)*t0)
```

follows from `H−4*Y*(X+1)=3`. Signed-to-natural divisibility reflection then
gives H|3q²L. But `Y≥q³≥q²` yields
`0<3q²L≤3q²(X+1)<3+4Y(X+1)=H`, contradicting the positive divisor bound.
The source proposes both sign cases and uses the existing unelaborated
model-divisibility patterns; all tactic, cast and provider obligations remain.

The 300 exact probe-graph controls confirm the specialized main-root form;
3,780 bounded q/Y/X/sign controls exercise the strict-divisibility argument.
They do not establish the claims in arbitrary IΣ₁ models. In particular, this
only addresses eta=zeta=0 **conditional on the main norm and q≥2**; it says
nothing by itself about eta>0 with zeta=0, an existential witness replacement,
compact source bindings, or the complete zeta-unshift goal.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta-zero-main-obstruction-draft/check.py | cmp - research/ordinary13-eta-zeta-zero-main-obstruction-draft/receipt.json
```
