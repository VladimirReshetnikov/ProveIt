# Precision-safe fast Cauchy feature transforms

## Status and novelty boundary

The reviewed checkout is `VladimirReshetnikov/ProveIt` at
`a7ae5ab55f9627f5af7bf77443b3c34ef8ef1be4`. The source identities and normalized
features below come from `Research/eth_joint_cauchy/report.tex`, Sections 3–5.
The strongest prior local realizations build feature tables or apply streamed
row recurrences in quadratic work; see `sat_frontier_improvements/report.tex`,
`subsat_contraction_tree/report/prefix_theorem.tex`, and
`eth_adaptive_exact_kernels/report.tex`, Sections 10–11. Searches of the 29
packets' `.tex` and `.md` files found no product-tree, multipoint, convolution,
or fast Cauchy matrix-vector application. This is a corpus-relative finding,
not a literature-wide novelty claim.

Fast polynomial products, monic multipoint evaluation, transposed polynomial
algorithms, and diagonal/Toeplitz structure are classical. The contribution
here is an explicit representation and precision guard for this exact normalized
2-adic feature interface, with an independently executable prototype. It is a
local polynomial-factor improvement. It neither proves a new worst-case SAT
exponent nor implements a complete SAT counter.

## Exact interface

Let `L=2^a`, `N=L/2`, `R=2^i`, `0<=i<a`, and

    s_j = (j mod R) + 2R floor(j/R),  0<=j<N.

Let `T` be a specified, precision-extendable element of valuation `i` in an
unramified 2-adic coefficient ring. The preprint's `T=t+2^(a+1) zeta` has this
form. One may also allow coefficients in the finite free nilpotent extension
`O[V]/(V^ell)`; denominators remain in the unramified subring. For sign
`epsilon` in `{+1,-1}`, put `x_j=epsilon*s_j`, `z_b=epsilon*s_b`, and

    E_b = 2 floor(b/R) - popcount(floor(b/R)),
    F[j,b] = 2^(-E_b) T/(T+x_j-z_b)
               * product_{h<b} (x_j-z_h)/(T+x_j-z_h).

For positive sign these are the target-side normalized F features. Negative
sign gives the source-side G features. All these entries are integral and
vanish when `j<b`, by the existing packet's exact proof. Its source form is
precisely `(G^T v)_b = sum_j G[j,b] v_j`, with omitted real ports allowed.
There is no need to construct a dense N-by-B matrix to evaluate all these
forms at one assignment v.

We prove fast synthesis `F c` and analysis `F^T v`, for any first `B<=N` modes
and any specified list J of real port indices. Arbitrary input coefficients
modulo `2^p` may be canonically lifted to the working ring: integrality of F
makes the output modulo `2^p` independent of the lifts. This observation does
not identify the canonical lifting map with a ring homomorphism.

## Denominator valuations and guards

Let `D_B(X)=product_{h<B}(T+X-z_h)`, and define

    kappa_j = v2(D_B(x_j))
            = sum_{d=1}^i #{h<B : h == j (mod 2^d)}.

Indeed, each denominator has valuation `min(i,v2(j-h))`, including value `i`
when j=h. Counting the divisibility levels proves the equality. Since each
congruence class contains at most `B/2^d+1` indices,

    kappa_j <= B(1-1/R)+i.

Set `kappa=max_{j in J} kappa_j` and `H=E_(B-1)`. Then

    H <= 2(B-1)/R,
    H+kappa <= 2B+i,
    H+2kappa <= 2B+2i.

The exact kappa formula is used by the prototype, so the loose bounds need
not be paid in practice. All valuations concern fixed, known denominators;
no valuation of an arbitrary polynomial sum is guessed.

## Synthesis by a rational Newton product tree

Put

    A_I(X)=product_{h in I}(X-z_h),
    B_I(X)=product_{h in I}(T+X-z_h).

For the consecutive interval I=[l,r), define

    C_I(X) = sum_{b in I} w_b
                product_{l<=h<b}(X-z_h)
                product_{b<h<r}(T+X-z_h),
    w_b = c_b 2^(H-E_b) T.

For consecutive halves I=L union R,

    C_I = C_L B_R + A_L C_R.

This is a division-free recurrence. At the root,

    (F c)_j = C_[0,B)(x_j) / (2^H D_B(x_j)).

Compute all product-tree polynomials and their evaluations at x_j modulo
`2^(p+H+kappa)`. Evaluate with monic product/remainder trees: all polynomial
leading coefficients are one, so polynomial division requires no nonunit
inverse. Each value of C is divisible by `2^(H+kappa_j)` by the pre-existing
integrality theorem. Divide that power of two exactly, invert the remaining
odd/unit part of D, and reduce modulo `2^p`. The working precision leaves at
least p bits after the exact division. The normalized denominators can be
batch-inverted, paying one unit inversion and linear multiplication work.

No dense feature table is formed. Full table construction remains subject to
its quadratic output-size lower bound; the changed interface has only B+|J|
input/output entries.

## Source forms by a transposed product tree

The transposed map needs a different precision argument; blindly transposing
an algorithm containing divisions by powers of two would be invalid.

Let `P=p+H+kappa`. First build and evaluate D at the higher precision
`P_hi=p+H+2kappa`. Thus every normalized unit

    u_j = D_B(x_j) / 2^kappa_j

is known modulo `2^P`. Batch-invert these units at precision P and put

    w_j = 2^(kappa-kappa_j) u_j^(-1) v_j  (mod 2^P).

Let `N_b(X)=product_{h<b}(X-z_h) product_{h>b}(T+X-z_h)`. We need
`q_b=sum_j N_b(x_j) w_j`. Obtain the monomial dual coefficients

    m_k = sum_j w_j x_j^k,  0<=k<B,

from the first B coefficients of

    sum_j w_j/(1-x_j Z).

A divide-and-conquer numerator/denominator construction followed by power
series inversion computes them; the series denominator has constant term 1.
Newton inversion `g <- g(2-fg)` is valid over the coefficient ring even when
2 is not a unit. Transpose the division-free C-tree using the identities

    child_left_dual[k]  = sum_t B_R[t] parent_dual[k+t],
    child_right_dual[k] = sum_t A_L[t] parent_dual[k+t].

Each is a polynomial correlation. At the leaves this yields q_b. Finally,

    (F^T v)_b = T q_b / 2^(kappa+E_b).

Its numerator is divisible by the displayed power, because F is integral.
The core precision P leaves at least p bits after this division. The high
precision denominator preparation is necessary: the smaller synthesis guard
alone does not in general make all normalized inverses known to core precision.
This distinction is implemented and tested explicitly.

## One-convolution specialization at valuation zero

For i=0, `s_j=2j`, put

    f_j=v2(j!)=j-popcount(j),  o_j=j!/2^f_j,
    D_j=product_{h=0}^j (T+2 epsilon h),  D_(-1)=1,
    u_j=o_j/D_j,  v_j=D_(j-1)/o_j.

All D_j and o_j are units. The exact feature formula becomes

    F[j,b] = epsilon^b T * 2^(f_j-f_b-f_(j-b)) u_j v_(j-b), j>=b.

The exponent is `v2(binomial(j,b))>=0`. This is a diagonal/Toeplitz
factorization with known factorial valuations. Let K=f_(N-1). At precision
`p+2K`, set `V_t=2^(K-f_t) v_t`.

For synthesis, convolve

    c'_b = c_b epsilon^b T 2^(K-f_b)

with V. At j, multiply the convolution coefficient by u_j, divide by
`2^(2K-f_j)`, and reduce to p bits.

For source forms, correlate `a_j=v_input[j] 2^f_j u_j` with V. At b,
multiply that correlation by `epsilon^b T`, divide by `2^(K+f_b)`, and
reduce to p bits. One reversed polynomial product supplies all correlations.
Both exact divisions are justified by the feature identity. All preparation
is linear work with one batch inverse, followed by one convolution. This
specialization is particularly simple at the i=0 Hermite nodes and is useful
in practice; arbitrary missing ports are handled by zero-filling the input.
The prototype currently exposes the full N-by-N specialization, with the
general product-tree implementation covering truncated mode and port lists.

## Complexity and the precise scope of the gain

Let m=B+|J| and let M_A(m,P) denote the cost of multiplying degree-m
polynomials over the actual coefficient algebra at P-bit precision. Standard
balanced product/remainder trees and the displayed transposed recurrences
cost `O(M_A(m,p+O(B+i)) log m)` plus linear unit arithmetic and one unit
inversion. A straightforward stored tree uses `O(m log m)` coefficient
storage; no quadratic table is necessary. The i=0 specialization costs
`O(M_A(N,p+2v2((N-1)!)))` plus linear unit arithmetic and one inversion.

This is an asymptotic local improvement over the reviewed quadratic
streamed application. It is not legitimate to say merely "quasi-linear at p
bits": the guard bits must be paid. In the scalar ring, using quasi-linear
integer multiplication and Kronecker substitution, the general bound is
`soft-O(m (p+B+i))` bit operations; for p>=B+i it becomes `soft-O(mp)`.
The coefficient algebra's explicit finite free rank introduces the cost of
its ring arithmetic. Alternatively retain M_A rather than hiding that rank.
The repository's active-node precision `p≈MD/u` and `N=L/2=RD/2` give
`p/N≈2M/(Ru)`, so the O(N) guards are lower order under its fixed schedules
with `R<=2^u`, `u=O(log s)`, and a strict exponent gap between R and M.
This must be checked for any proposed schedule outside that regime.

The Python implementation uses exact integer Kronecker substitution; CPython
uses its own integer multiplication algorithm, not a quasi-linear FFT backend.
Consequently its empirical timing should not be advertised as an implementation
of the optimal bit-complexity bound. Benchmarks compare full source-form
application including preparation, guards, and output verification with a
quadratic streamed baseline using one batch inverse and fused prefix ratios.
The general product-tree prototype is slower at the supplied moderate sizes;
those regressions are retained. The specialized one-convolution timings are
reported separately.

Changing this local linear transform does not reduce the number of nonlinear
mode-exponent tuples or paid recursive child contractions. Thus the 2^(C s/
sqrt(log s)) contraction exponent and the density-dependent SAT exponent
remain unchanged by this kernel alone.

## Reproducibility

Run `python3 fast_cauchy_transform.py --benchmark --output results.json`.
The tests include 246 independently computed rational-matrix cases (10,160
individual feature entries), 27 larger cases against a separate streamed
recurrence, and 96 specialized one-convolution cases. They include p=1,
positive/negative signs, nonzero interpolation parameters of different signs,
truncated mode lists, missing ports, and adjoint identities. These finite
checks verify the prototype; the displayed algebraic argument establishes the
general theorem. The code currently implements the scalar ring only. Its
unramified/nilpotent-ring extension is a mathematical statement using the same
monic polynomial operations; an extension-ring optimized implementation is not
claimed here.
