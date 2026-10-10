# Proposed manuscript integration and editorial changes

Reference snapshot: `a2a4cf58c49c745058c40e4a6748d472a3420f18`.
These are proposals, not changes already made to GitHub. Review any later
repository changes before applying them. No complete manuscript build was run.

## Integration placement

Copy this package into
`Analysis/Polylogarithms/docs/reports/lerch-zero-bifurcations/`.
Copy `integration/09-lerch-endpoints-bifurcations.tex` into the manuscript's
`chapters/` directory. At the end of `chapters/09-zero-geometry.tex`, add:

```tex
\input{chapters/09-lerch-endpoints-bifurcations}
```

Insert `integration/bibliography-item.tex` into the existing bibliography in
`references.tex`. Keep the full standalone proofs and certificate code with the
report. The short insertion is not a replacement for those proofs.
All new integration labels start with `lerchcont:`. A standalone smoke build of
the insertion was performed; the complete repository manuscript was not rebuilt.

## 1. Definite notation error in the half-unit proof

In `chapters/09-zero-geometry.tex`, near source line 473, replace:

```tex
The root of $P_1$ is $-\gamma$, so
```

with:

```tex
The root of $Q_1$ is $-\gamma$, so
```

Reason: the source defines `P_1(t)=1+t` but `Q_1(x)=x+gamma`. This is a
notation correction, not a failure of the half-unit bracket theorem.

## 2. Duplicated sentence at the start of the same proof

Near source lines 434–435, replace:

```tex
The endpoint signs in the endpoint signs and the Laplace representation above
and the bound of one zero prove existence, uniqueness, and simplicity.
```

with:

```tex
The endpoint signs, the Laplace representation above, and the bound of one
zero prove existence, uniqueness, and simplicity.
```

## 3. Update the zero-geometry research programme

In `chapters/10-discovery.tex`, the subsection “Zero geometry beyond a fixed
Laurent index” currently begins by leaving small derivative orders for n >= 5
unresolved and closes by mentioning the suggested higher-branch monotonicity.
A proposed replacement paragraph is:

```tex
The fifth Laurent index is now settled at every classical derivative order:
there are three simple positive zeros at $k=1,2$ and five at every $k\ge3$;
see Theorem~\ref{lerchcont:n5}. Exact small-order counts for $n\ge6$ remain
open in this continuation. Critical-point descent adds a way of proving
root deficits below a saturated order, not only propagating saturation.
Effective uniform thresholds still require quantitative Appell-root
separation and concentration remainders. The spectral expansion for
$n=O(\log k)$ does not itself give moving-zero asymptotics throughout that
range. Monotonicity must distinguish two regimes: all branches decrease for
fixed $n$ and sufficiently large $k$, whereas at $(n,k)=(2,1)$ the lower
branch has a unique nondegenerate interior minimum. The singular endpoint
expansion explains its reversal near $\rho=1$.
```

The existing global upper bound, n <= 4 saturation theorem, and uniform
large-k location expansions should be retained. None has been disproved.

## 4. Do not extrapolate endpoint smoothness

Any new prose about differentiation in rho at 1 should reflect the exact
threshold: the family is C^(k-1), not C^k. In particular, the k=1 family is
continuous but has a logarithmically divergent first rho derivative.
This corrects a possible inference; the source's continuity theorem is valid.

## 5. Preserve the n=3 endpoint exception and the open global question

At rho=0 the index-three elementary function has a double zero at a=1 and a
simple zero at a=e^3. The one-zero small-parameter theorem concerns strictly
positive rho. The interior fold theorem is localized to 0<a<3/2. It does not
prove that an extra pair cannot occur entirely to the right of 3/2 below the
fold threshold. The stronger global statement is explicitly a conjecture.

## 6. Claims not changed by this report

Do not mark the mixed S4 identity, higher golden ladder conjectures, or
numerical period-independence questions as solved by these results. The
polylogarithmic finite-part identities arise from a classical Lerch expansion;
no global-priority or new arithmetic-independence claim is being made.
