# Checked split-source degree and carry interfaces

[`SplitSourceBounds.lean`](Lean/DiophantineConsistency/SplitSourceBounds.lean)
proves the generic polynomial degree estimate

```
deg(encoded(w,y)^2*D2+encoded(w,y)*D1+D0)
  <=max(2*W+degBound(D2), W+degBound(D1), degBound(D0))
```

when each weight is at most `W`. Signed coordinate values, zero polynomials,
and cancellations are permitted. With weights at most 116 and the existing
`SplitWordBounds.KernelBounds`, the three channel bounds are 2161, 2143,
and 1719. Thus every assignment has natural degree below 2162. The proof
requires no target isolation or source identity.

[`SplitSourceCarry.lean`](Lean/DiophantineConsistency/SplitSourceCarry.lean)
instantiates the generic two-block decoder with low length 117 and high
coefficient length 2162. It derives all degree and quarter-base coefficient
conditions from those weight/kernel bounds and `4096*H*b^2<=B`, `H>0`.
The low range `g<B^117`, high integer nonnegativity, powers-of-two base and
digit cap, and target positions below 2162 remain explicit.

`tau_product_iff` gives existence of bounded digits `z_i<b`, their exact low
code `g`, and zero monitored coefficients of the polynomial at positive
coordinates `z_i+1`. `tau_targets_iff` states the same condition for an array
`q : Fin r -> Nat`, with coefficient zero at every `q_j`. The latter does
not need target injectivity for this logical conversion; the separate mask
population theorem still needs it to determine the target count.

These generic interfaces do not import a literal source system, fixed
coefficient binding, machine, or consistency interpretation. The selected
source's positivity and packing range are supplied by separate word bounds;
its coefficient extraction and semantic endpoint are separate bridges.

Checks attain the top degree 2161 with one top-position digit, permit a zero
assignment, and exercise the complete carry theorem at `b=1` with a monitored
constant coefficient. The carry check proves positivity symbolically and
does not materialize its large packed integer. All audited proofs use only
the standard Lean axioms.
