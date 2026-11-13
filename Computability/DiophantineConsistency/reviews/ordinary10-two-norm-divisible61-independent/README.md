# Independent source and standard-integer review of the 10/61 reduction

The reviewed witness maps are valid for natural ports with `beta>0` and `K0>0`, assuming the stated standard-integer semantics. The ten-variable, 61-live-operation graph has the same zero-existence status as the pinned nine-variable, 64-operation **relaxed two-norm child** under those assumptions. Its total degree is exactly 60 when beta is nonzero. This is not a proof of a reverse bridge to the original 85-row parent, a Con(ZFC) equivalence, an internal iPRA theorem, or Lean elaboration.

## Main norm excludes X=0

The actual pinned graph has `q=1+beta*J`, `Y=q³*s>0`, `U=Y*q²>0`, `a=Y*(X+1)`, `H=4*a+3`, and `Delta=a²+H`. From the unaltered main equation, integer square divisibility yields `Dstar=U*d` and `d²=1+Delta*c²`. At `X=0`, the literal main root is `Dstar=U*a*c+H*shift`. Thus `H | U*(d−a*c)`. The norm also gives `(d−a*c)*(d+a*c)=1+H*c²`, so `d−a*c` is invertible modulo H and `H | U`. But then `H | 4U=q²*(H−3)` and hence `H | 3q²`, impossible since `H=4q³s+3>3q²`. This works for both signs of d; it does not assume the first norm or bounds on the mask ports.

## Positive carrier and the two maps

Write `b=beta*J`, `B=C*(X+K0)−F`, `C=q−F−alpha`, `ell=X*Y²*k`, with `F,alpha,s,k` strictly positive because of their input shifts. The old signed root is exactly

`Z=b*(ell+k+r−k*B)−B`,

and its first residual is `Z²−b²*(1+ell*(ell+k))`. The new graph replaces this by `B−b*h` and `tau²−(1+ell*(ell+k))`, keeping the actual main expression tree.

At `J=0`, C<0 and B<0. The old first root would be `Z=−B`, so the old first norm cannot vanish; the new carrier equation would give B=0, so it cannot vanish either. Thus b>0 at either zero. For an old zero with C≤0, B<0, giving `Z>b*(ell+k)` because r≥0. Meanwhile `1+ell*(ell+k)≤(ell+k)²`, since `ell*k+k²≥1`, a contradiction. In the new graph, B=b*h≥0 and F>0 directly rule out C≤0. Therefore C≥1 in either case. From `F+alpha≤q−1` and alpha≥1, `F≤q−2`. Main-norm positivity gives X=q*w with w≥1. The stated K0≥1 now gives `B≥q+1−(q−2)=3`.

At an old zero, `b² | Z²` implies `b | Z` over the integers. The displayed first-root equation then implies `b | B`; put `h=B/b≥1` and `tau=|Z|/b`. Both new first constraints and the unchanged main residual vanish. At a new zero, B>0 and B=b*h imply h≥1. The normalized norm gives `tau²=1+ell²+ell*k>ell²`, hence tau>ell. The integer

`r=tau−ell−k+k*b*h+h`

is natural, since `b*h≥1`. Direct substitution gives `Z=b*tau`, including the `−B` term. Thus the old first norm and unchanged main norm vanish. The construction of the new-to-old witness chooses the positive first-root sign; the old-to-new direction permits either sign and uses the absolute value. Other witness coordinates are retained. These are zero-existence maps, not pointwise equality of the two output polynomials.

## Counts, degree and checks

The separate checker reconstructs actual ordered expression trees from both JSON graphs, checks the first-root rows and both new residuals, and traverses all dependencies from the output: all ten witnesses and 61 operation rows are live. The parent and child main trees are identical. It independently evaluates the output as an exact univariate polynomial on the stated witness ray for beta 1, 2 and 7, finding degree 60 and leading coefficient `64*beta^42`. The general upper bound follows from the pinned parent main-norm cancellation, which gives degree ≤30 for A1; the new carrier residual has degree ≤3 and the normalized first residual ≤22. Squaring and summing gives degree ≤60. The parent checker supplies the beta-symbolic ray calculation, showing the coefficient is nonzero for every fixed beta≠0, rather than only for the three checked values.

The checker also exercises both signs of the scalar first-root map on finite Pell instances, and checks finite controls of the X=0 numerical inequality. These controls are not a proof of arbitrary witness existence or the quantified implications above. The original author receipt, pinned parent files, and source hashes are verified read-only. Reproduce from `Computability/DiophantineConsistency` with:

```sh
python3 -I -S -B reviews/ordinary10-two-norm-divisible61-independent/check.py | cmp - reviews/ordinary10-two-norm-divisible61-independent/receipt.json
```

No Lean, model lifting, axiom audit, provider authentication, physical PDF binding, or graph build was performed.
