# Independent mathematical review

Reviewed the finite arithmetic core, analytic applications, efficiency
section, and category/model/topology contribution. The review concerns
mathematical validity and the proposed iPRA boundary, not typography.

Files reviewed:

- `work/paper/sections/02_core.tex`
- `work/paper/sections/05_analysis.tex`
- `work/paper/sections/06_efficiency.tex`
- `work/category_topology.tex`

The existing-source distinction was also checked against
`work/paper/sections/01_scope.tex`.

## Findings requiring clarification or correction

### 1. Decidable does not imply primitive recursive

The core initially described a primitive-recursive characteristic accumulator
for any “decidable arithmetic condition.” This is too broad. The construction
requires a fixed primitive-recursive Boolean test, or a bounded formula built
from such tests whose Booleanization has been proved. A merely recursive
(decidable) predicate need not have a primitive-recursive characteristic
function. This finding was sent immediately to the parent. The remedy is a
wording restriction, not a change to the finite rational applications.

### 2. Uncertain-distance complexes must have labeled vertices

If represented points `x_i` can coincide, the clique complex on index labels
is not literally a subcomplex of a Rips complex whose vertices are the
quotient set `{x_i}`. Exact equality of represented points cannot be silently
decided. The correct sandwich is on the common labeled index set, endowed
with the pseudometric `d(i,j)=d(x_i,x_j)`. Alternatively, a separation
certificate can ensure distinctness. The labeled formulation preserves all
the proofs, needs no extra hypothesis, and is preferred.

This correction was communicated and is now present in the latest agent
source: its uncertain-distance paragraph explicitly uses labels and a
pseudometric. The rest of the metric correspondence argument needs only the
pseudometric laws; strict separation is not used there.

### 3. Rational sensitivity weights need an integer rounding convention

The integral-logic sensitivity theorem initially called `W_phi` an integer
while allowing rational local sensitivities. Its shift is valid after taking
an integer upper bound, e.g. by first replacing every local coefficient with
its ceiling. This correction was communicated and is present in the latest
agent source. The resulting error recurrence remains an upper bound.

### 4. Holomorphic boundary and represented-argument guards

The remainder estimate is correct whenever both `z` and `z+h` lie inside the
chosen closed disk `|z|≤r`. That restricted estimate alone does not prove the
full complex derivative test at a point on the boundary `|z|=r`.

Use a wider rational guard `r'=(1+r)/2<1` when proving differentiability at
such a point. For sufficiently small `h`, both arguments lie in the wider
disk. The same enlargement allows ordinary rational approximants to a
represented `z` to be evaluated even if an approximant lies just outside the
original disk. The local remainder and approximation bounds then use the
constants computed from `r'`. The exact mathematical bounds stated for
arguments in the original disk remain unchanged. This supplies the missing
finite production detail and makes the differentiability claim complete.

For the promised all-rational implementation, it is useful to state explicitly
that `|a+ib|≤Q`, with rational `Q≥0`, means `a²+b²≤Q²`. Triangle and product
bounds then use rational bound certificates; the algorithm need not compute
an exact square root for a complex norm.

### 5. Bilinear extension with different advertised input bounds

The bilinear extension theorem is true. The displayed same-name rapidness
calculation is correct. A direct cross-name estimate, however, can involve a
mixed constant such as `M(S+R')`, whereas the two outputs may have been built
using shifts derived separately from `(R,S)` and `(R',S')`.

To make independence of advertised bounds fully explicit, compare the two
outputs at arbitrarily fine common indices under the maximum of their four
bounds, then use each output's own rapidness to return to its requested
index. The remaining arbitrarily small rational error is removed by the same
rational-separation argument used for equality transitivity. Equivalently,
first prove that increasing a bound/reindexing does not change the represented
value, then compare both names using the enlarged common bounds. The text
asserts these facts, but spelling out this argument removes a proof shortcut.

### 6. Small input conventions

For the `L1`-to-uniform upgrade, replacing the supplied modulus `N` by its
prefix maximum before reindexing gives an immediately rapid construction.
The stated Cauchy-index bound itself is correct even without monotonicity.
The core already provides this monotone-hull convention; a reference suffices.

State positive net radii and nonnegative distortion/error tolerances
explicitly. In particular, the completion-point selector construction using
an approximation of error `epsilon/2` presumes `epsilon>0`.

## Checks with no mathematical defect found

### Core equality and induction

The cross-precision equality
`p(u_k-v_l)≤2^-k+2^-l` is a valid equivalence on regular names. Its
transitivity proof reduces a failed rational bound to one positive rational
gap and uses a sufficiently fine intermediate approximant. No real equality
test is needed. Regularization by a monotone Cauchy modulus is correct.
The shift `h(C)` is a bounded primitive-recursive search for rational C.

The bounded replay theorem uses the quantifier-free guarded invariant
`i≤B -> I(a,i,z_i)`. At the last step the next guard is false. It does not
induct on the universally quantified validity of an analytic name. The text
correctly keeps program totality/batch witnesses and local producer
hypotheses explicit.

### Integral operators and resolvent constants

The column norm, not product `L1`, is the correct finite kernel norm for an
operator `L1(t)->L1(x)`. The spike counterexample computes correctly.

For the resolvent schedule, `C=b+Mb²`,
`s=k+h(4C)`, `R=k+h(4Mb)+1`, and `N=bR` give

- `C 2^-s ≤ 2^-k/4`;
- `Mb q^N ≤ 2^-k/8`;
- hence the stated `3/8` cross-name bound.

The finite operator power telescope is correctly ordered for noncommuting
operators. The perturbation constant `b+Mb²` follows from the finite
geometric and differentiated-geometric sums. The residual identity and
uniqueness via an explicit rational norm bound are correct.
The worked solution to `K(x,t)=xt/2`, `g=1` is indeed
`f(x)=1+3x/10`, and the column norm is `1/4`.

### Holomorphic transform constants

The two denominator identities, input sensitivity `b`, argument sensitivity
`Mb²`, derivative input sensitivity `b²`, and quadratic remainder constant
`Mb³` are correct. The derivative-kernel Lipschitz bound `5b^4` is valid.
Midpoint quadrature uses a mesh refining the input step partition, avoiding
any discontinuity of the input density at cell boundaries. The coefficient
formula and the tail `Mb r^N` are correct, and the geometric iteration count
is primitive recursive. The only missing production detail was the guard
enlargement described above.

### Shared graph budgets

Reverse propagation adds sensitivities before a shared predecessor is
substituted, giving exactly the sum-of-path-products weights. No independence
of the errors is assumed. The invariant of processed residuals plus
unprocessed weighted errors is valid. One rational multiplication and
addition per edge is the correct arithmetic-operation count for the reverse
pass. The bound does not claim a bit-complexity result. The allocation
`eta_v≤epsilon/(1+sum w)` gives a strict final bound below epsilon.

### Model semantics and regularity upgrade

The bounded-compression pullback estimate is correct on exact finite
partitions and extends with the required error budgets. Projections and
coordinate permutations preserve the product measure. Diagonal substitution
and supremum are correctly rejected as arbitrary `L1` operations; both
counterexamples have norm tending to zero while the proposed output remains
one.

The `L1`-to-uniform estimate uses a cube of volume `delta^d` containing the
point; its maximum-metric radius is at most delta. The constants
`a=k+h(8L+1)` and `r=k+da+1` give an error at most
`2^-k/4+2^-k/2`, as claimed. The procedure needs both a common Lipschitz bound
and a supplied `L1` Cauchy modulus, which the theorem states explicitly.

### Topological chain and interleaving calculations

The mod-two prism formula is valid, including degenerate simplices and the
unaugmented degree-zero convention. The distortion correspondence yields
maps at shift eta and composites contiguous to inclusion at shift `2 eta`.
Different finite selections are contiguous already at shift eta.
The finite complexity estimates are valid coarse bounds.

For an epsilon-net selector, forward scale shift `2 epsilon` and backward
shift zero give the stated asymmetric interleaving. The inclusion map from
scale r to scale `r+2 epsilon` factors through the finite net complex,
so its rank is at most `binomial(|A|,q+1)`. This does not assert homological
reconstruction at one exact scale; the text correctly preserves that boundary.

## Existing-source and verification distinctions

The scope section correctly identifies the failing independently truncated
tail shortcut while explicitly preserving the repository's valid
common-envelope object-iPRA theorem in `Probability.TruncationEstimate`.
The reviewed analytic and topology sections do not claim new completed
`Prf PRAAx` derivations. The standalone checked rational kernel and the
remaining object-language obligations are kept distinct.

## Overall conclusion

No counterexample was found to the principal mathematical theorems, their
quantitative constants, the graph-sharing estimate, or the homology-rank
factorization. The findings above concern a necessary PR restriction, a
literal vertex-set correction, and several explicit proof/representation
steps. After those changes, the reviewed arguments give a sound finite
constructive route to the stated represented conclusions, subject to their
listed input certificates and the remaining object-level formalization.
