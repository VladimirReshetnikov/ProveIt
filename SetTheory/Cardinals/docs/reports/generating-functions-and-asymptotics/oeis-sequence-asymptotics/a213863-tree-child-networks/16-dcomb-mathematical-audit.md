# Audit of fixed d combining network asymptotics

Date: 2 October 2026

## Verdict

The argument in the reviewed `maximal-proof.md` supports a strictly positive limiting amplitude and every finite Airy correction for the maximal-reticulation sequence, for each fixed integer d ≥ 3. I found no substantive analytic obstruction after checking the changed recurrence, the global spectral argument, the moving ground-state projection, and the transfer from formal profiles to the exact endpoint. The same argument specializes correctly to the supplied binary proof.

This is an independent mathematical audit of a research draft, not external peer review, publication, a computer-verified theorem, or certification of the numerical amplitude. Two small precision repairs should be made before freezing the text: correct the row index in the discussion of the q boundary, and explicitly restrict the all-orders approximate solution to the occupied parity. Additional clarifications below make several compressed analytic steps easier to verify.

The warranted conclusions are:

- A positive amplitude and all finite Poincare orders for a[n] and T[n,n−1]
- Only a leading equivalent for total T[n], using the published total/maximal ratio for d ≥ 3
- Finite-order inversion for the diagonal and maximal sequences, with integer bracketing and with an exact but not numerically certified amplitude

The audit does not establish novelty against every possible later source. It does not justify all-orders expansions for total counts, convergence of the infinite correction series, or an unconditional ceiling rule for integer thresholds.

## Source verification and scope

The primary source consulted was Chang, Fuchs, Liu, Wallner, and Yu, *Enumerative and Distributional Results for d-combining Tree-Child Networks*, March 25, 2024 manuscript, [primary PDF](https://web.math.nccu.edu.tw/mfuchs/d-comb-journal-rev.pdf). The relevant locations are Theorem 1.8 on PDF page 5, Corollary 1.11 and Remark 1.12 on page 6, Proposition 3.7 on page 20, and the maximal-count identity and equation (17) on page 22. These establish the recurrence, the factorial-times-word-count identity, the two-sided Airy scale, and total/maximal convergence for d ≥ 3. They do not establish the new amplitude limit.

The binary comparison used `oeis-a213863-research/release/tree-child-asymptotics.tex`, particularly the spectral, quasimode, amplitude, boundary-smoothing, and zero-limit-bootstrap sections. The general-d argument was checked on its own coefficients rather than accepted from the binary case. The later binary total-count identity was not used for d ≥ 3.

## Exact reduction and small boundaries

Write C[n,m] = binom(d n+m−2,d−1). Dividing the source recurrence by C[n,m] gives q[n,m] = sum from j=1 to m of b[n−1,j]. Consequently

q[n,m]−q[n,m−1] = C[n−1,m] q[n−1,m]

on the defined triangle, with the previous b row zero beyond its diagonal. Setting A[n,k]=q[n+1,k+1] gives precisely the claimed coefficient binom(d n+k−1,d−1). The initial value q[1,1]=1 holds because C[1,1]=1. At the right boundary,

q[n+1,n+1] = q[n+1,n] = sum from j=1 to n of b[n,j] = c[n].

Thus A[n,n]=A[n,n−1]=c[n], including n=1, and the first column is the asserted binomial product.

**Precision repair 1.** The draft says “the q equation at m=n+1.” With its current row labels q[n,m] is defined only for m≤n. Replace this sentence by the displayed identity for q[n+1,n+1] above. There is no error in the actual A recurrence or its numerical implementation.

The normalization is also exact. The down-step coefficient is

binom(d n+k−1,d−1)/(Lambda n^(d−1))

with n=(N+j)/2 and k=(N−j)/2. Factoring the binomial gives the stated product p_N(j). At j=N the up-step is zero, and the down-step recovers the initial column. At j=0 the down-step is absent. N=1 is reproduced by S_1 e_0 after the gauge. These observations rule out an untracked boundary source term.

An independent exact-rational check in this audit computed the normalized values directly from source b rows, without reusing the A update, and verified every physical recurrence position through N=20 for d=2,…,12. It also checked positivity, monotonicity, and exponent identities. The supplied replay was run separately for d=2,…,8.

## Positive contractive gauge

For every h from 1 to d−1,

1−2(j+h)/((d+1)(N+j)) ≥ 1/(d+1)

for N,j≥1. The equivalent inequality is dN+(d−2)j≥2h, whose minimum is 2d−2. Each factor is at most one and increases strictly with N. Therefore G_(N−1)(j)/G_N(j) lies in (0,1]. The product definition of G may be used at all nonnegative j; restricting the matrices to their declared finite supports then gives the desired zero-padding convention.

Gauge conjugation converts the two unsymmetrized edges into the same square-root edge on either side, proving v_N=S_N Q_N v_(N−1). The norm bound follows from ||Q_N||≤1 and ||S_N||=lambda_N; positivity gives entrywise domination by half-line adjacency. These are genuine fixed-d estimates. No uniform bound as d tends to infinity is implicit.

## Global spectral gap

Let b_j=sqrt(p_N(j)). The exact form is the sum over edges of b_j|v_j−v_(j−1)|² plus the diagonal potentials 2−b_j−b_(j+1), with the appropriate endpoint terms. Splitting the left endpoint term as 1+(1−b_1) supplies the fictitious Dirichlet edge to x=0.

The lower edge bound controls the discrete gradient. The potential estimate

1−b_j ≥ (1−p_N(j))/2 ≥ (j+1)/((d+1)(N+j))

follows already by retaining the h=1 factor. Since j≤N+1, multiplication by N^(2/3) yields a uniform positive multiple of x_j=(j+1)N^(−1/3), apart from harmless endpoint bookkeeping. Hence bounded scaled form energy forces tight L² tails. On compact x intervals the edge coefficients tend to one, while the scaled potential tends uniformly to c x. Local H¹ compactness plus tightness gives the stated compact form convergence. Smooth compactly supported Dirichlet recovery functions provide the reverse bound.

These facts justify min–max convergence for each fixed low eigenvalue, including the first two. This is a global gap argument; a local Airy test function alone would not suffice. The parity issue is treated correctly: −lambda_N is present, so a full spectral-radius gap would be false. On the map between opposite parity spaces, the largest singular direction is simple and the remaining singular values are separated on the N^(−2/3) scale.

For maximum readability, explicitly state that the interpolation of a unit discrete vector uses values epsilon^(−1/2)v_j. This normalization is implicit in the draft's form-convergence discussion.

## Frozen quasimodes and drift estimates

Expanding the exact product gives p_−=1−c x epsilon²−kappa0 epsilon³+O(epsilon⁴). The two-edge coefficient at epsilon³ is −(c/2+kappa0), and

c/2+kappa0 = (d−1)²/(d+1) = 2 eta.

Thus the N^(−1) eigenvalue correction is indeed −2 eta. This d-dependent term is essential; retaining the binary value would produce the wrong power of n.

The polynomial Airy inverse is valid: after eliminating P', the coefficient on x^j of the triangular operator is c(2j+1), never zero. A scalar eigenvalue adjustment shifts Q by a nonzero constant. It can enforce Q(0)=0, and the free constant of P then enforces P(0)+Q'(0)=0. Both the boundary condition and the derivative normalization are therefore available at every finite order, with no unresolved solvability condition.

Matching through epsilon^5 leaves a normalized residual O(epsilon^6). The global spectral gap costs epsilon^(−2), producing an eigenvector error O(epsilon^4), not an incorrectly assumed uniformly bounded resolvent. The cutoff j≤2 sqrt(N) is adequate: its scaled position is of order N^(1/6), where the Airy envelope is exponentially small in N^(1/4). Rational and shifted-profile Taylor remainders have fixed polynomial Airy envelopes on that support.

The derivative of the normalized explicit samples with respect to continuous N is O(N^(−1)); the quasimode approximation error O(N^(−4/3)) is smaller. This proves the claimed consecutive-time eigenvector drift. Integrating the logarithmic derivative of each factor and summing to j gives 1−Q_N(j)≤C_d j(j+d)/N². Airy moments then give O(N^(−4/3)) on the quasimode; contraction handles its approximation error. These estimates establish both occurrences of the Q drift bound.

Finally F'(0)/sqrt(integral F²)=sqrt(c). The sampled normalization gives psi_N(0)=sqrt(c)N^(−1/2)(1+O(N^(−1/3))). The pointwise quasimode error is smaller than the stated endpoint error. No invalid recovery of a leading coordinate from a large global error occurs here.

## Moving amplitude and strict positivity

The equal parity masses of the Perron vector justify the sqrt(2) normalization of g_N and h_N. Projection away from g_N followed by S_N has the reduced singular norm; putting Q_N before S_N preserves the estimate because it is contractive. Ground-state drift then forces a transverse error O(N^(−1/3)).

The exact adjoint formula M_N* g_N=Q_N h_N is decisive. The unit-vector identity makes the overlap defect from h_N−g_(N−1) quadratic, while the Q defect is O(N^(−4/3)). Thus t_N−1 is summable, and the cross term is O(N^(−1)) times O(N^(−1/3)). The scalar increments are summable and A_N has a limit. Merely knowing O(N^(−1)) drift would not have established this conclusion.

The Catalan estimate is exact: ||e_0^T J^L||²=(J^(2L))[0,0]=Catalan(L). On L≤N^(2/3), the eigenvalue denominator costs only a bounded factor. Duhamel therefore yields

L^(−3/4)N^(−1/3) + N^(−1) sum_(l<L)(l+1)^(−3/4) = O(N^(−5/6)).

This verifies the endpoint recovery needed for strict positivity. Summing log lambda_N produces P_N with power −eta and a positive convergent product constant. If A_infinity vanished, the endpoint would be smaller than its source lower bound by N^(−1/3). The published two-sided estimate therefore implies A_infinity>0. This reasoning does not assume the sought limit beforehand.

Substituting N=2n gives gamma_d=kappa_d A_infinity sqrt(c) 2^(−eta), as claimed.

## Transfer of every finite formal order

**Precision repair 2.** Explicitly say “cut off and restrict to j congruent to N modulo 2” when defining Z_N and z_N in Section 6. Otherwise the displayed sample norm sqrt(I/2)N^(1/6), and the decomposition in the occupied parity, do not literally apply. The binary proof spells this out. With that convention the argument below is valid.

The nonautonomous arguments (x±epsilon)(1−epsilon³)^(−1/3) and profile factors (1−epsilon³)^(−r/3) are correct. At order three the forcing has F coefficient −kappa0 and F' coefficient (c+2/3)x. Integrating xFF' gives

s_3 = −kappa0/2−c/4−1/6 = −eta−1/6.

This independent check agrees with the scalar product and the endpoint power. The same triangular polynomial inverse works at every finite matching order. Fixing the leading multiplicative constant of H_N is necessary and is correctly done.

On the cutoff support, G_N^(−1)≤exp(C_d), and on each fixed scaled window it tends to one with error O(N^(−1/3)(1+x)²). Consequently multiplication by the inverse gauge does not destroy the arbitrary-order residual bound. The H_N/P_N factor N^(−1/6) cancels the parity sample norm N^(1/6), giving a common q_0 for every truncation.

The zero-limit bootstrap is sound. From alpha_N=O(N^(−q)), the gap recurrence gives W_N=O(N^(−q−1/3)+N^(2/3−p)). The adjoint recurrence is absolutely summable, and its zero limit allows summation backwards. This improves alpha to O(N^(−q−1/3)+N^(1−p)). Finitely many repetitions reach q=p−1; substituting once more gives ||e_N||=O(N^(1−p)). Duhamel smoothing gives endpoint error O(N^(1/2−p)), hence relative error O(N^(1−p)). There is no illicit division by a small gap without accounting for its size, and no free undetermined homogeneous scalar remains.

## Coefficient field and exact algebra

The natural variables t=(N/2)^(−1/3), y=(j+1)t give the Airy equation with potential ((d−1)/(d+1))y+B/3. The shifted product, time dilation, polynomial inverse, and scalar-ratio matching then have rational coefficients for fixed integer d; divisions are only by nonzero rational constants. The boundary derivative cancels from normalized endpoint coefficients. Thus Q[B] is justified without a grading assumption about irrational powers of two or d+1.

The supplied symbolic recursion was replayed through degree six for d=2 and d=3. It cancels each finite residual coefficient exactly. For d=2 it agrees with the frozen binary proof's frozen corrections and logarithmic diagonal terms ell²/4, 0, −2/9 in time N. For d=3 the logarithmic diagonal terms in time N are

ell²/36, 11 ell/108, (16 ell³−729)/1944.

Converting N=2n and B=3z/2^(2/3) gives exactly the draft's B²/162, 11B/324, and 4B³/6561−3/16. These are symbolic identities, not fitted coefficients. The old binary wording in the general script's docstring and its final comment should be updated, but its executed formulas use the general c correctly.

## Leaf shift and inversion

T[n,n−1]=n!a[n−1] changes the amplitude to gamma_d/Gamma and the power to alpha=rho−(d−1). The factorial shift is exact; the remaining exponential and polynomial shifts admit ordinary finite Taylor expansions. Hence all finite maximal-count orders follow, and the total-count leading equivalent follows from the source ratio alone.

The Lambert-W seed solves p x log x+(log Gamma−p)x=y exactly on the principal branch for sufficiently large positive y. The displayed first correction divides the omitted lower-order terms by p log x_0+log Gamma. Effects of the omitted derivative terms and quadratic reversion are bounded by O(x_0^(−1/3)/log x_0); the leading omitted Airy term has that same allowed order. Higher orders can be generated by explicit smooth-model Newton or Taylor reversion.

The claim should continue to refer to the derivative of the explicit smooth model, never to a differentiated unknown remainder of the integer sequence. The existing neighboring-integer warning is correct. Numerical certification of a threshold additionally needs actual amplitude and remainder enclosures; the existence proof alone does not supply those. The report should say this explicitly if inverse computations are presented as certified numerical results.

## Reproducibility and limitations

The audit directory contains a fresh source-array check, exact-rational results, copied replay scripts and their logs, and a hash receipt identifying reviewed inputs and audit outputs. Input artifacts were not edited. Finite computation checks identities and implementation; the analytic estimates above provide the asymptotic justification. Numerical diagnostics were inspected as diagnostics only and were not used to prove convergence or positivity.
