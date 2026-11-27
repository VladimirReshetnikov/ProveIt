# Lean formalization roadmap

## Status

This document is a mathematical plan for a future Lean formalization. The archive
does not contain a new Lean theorem or claim that its new results have been checked
by the Lean kernel. The accompanying Python programs perform exact finite checks
and numerical evaluations; they are not formal proofs of the asymptotic theorems.
No validation of the upstream RH/GRH development is needed for the finite-field
theorem proved here.

The proposed identifiers below describe mathematical interfaces. They are not
claims that matching declarations already exist in the repository or in Mathlib.
Implementation should start by checking the repository's pinned Lean and Mathlib
versions and available bilinear-form, submodule-counting, and summability APIs.

## 1. Basic objects

Fix a finite field K with q elements. The construction should quantify over K,
rather than try to manufacture a field from an arbitrary natural number q.
All constants may depend on q, and no implicit constant may depend on the two
dimensions or on their difference.

For every even D, choose the standard nondegenerate alternating matrix J_D,
formed from 2-by-2 blocks with rows (0,1) and (-1,0). State alternation explicitly:
in characteristic two, skew symmetry alone does not assert that a form is
alternating. Dimension zero should be supported for auxiliary counts even though
the main theorem assumes positive dimensions.

For positive even a and b, define the finite frame set

    Frames(a,b) = { X in Mat_(a+b,b)(K) : X^T diag(J_a,J_b) X = J_b }.

The Gram condition implies that X is injective. Define A to be the first a rows
of a uniformly chosen element of this set. Define U to be uniform on all a-by-b
matrices, and T_b to be uniform on alternating b-by-b matrices. The residual is

    Lambda(M) = J_b - M^T J_a M.

The probability spaces are finite. Uniform probability and total variation can
therefore initially be implemented with rational-valued probability mass
functions and finite sums. Use nullity = dimension of the kernel throughout;
the conversion to rank is a final application of rank-nullity.

Prove that the frame model agrees with the projected columns of a uniformly
chosen symplectic group element. Transitivity follows by extending an isometry
between nondegenerate subspaces to their nondegenerate complements. Equal fiber
sizes then identify the two uniform distributions. This avoids importing an
unnecessary measure-theoretic notion of Haar probability.

## 2. Exact finite lemmas

The exact statements can be formalized independently of all infinite products.

| Suggested interface | Mathematical content | Dependencies |
|---|---|---|
| alternating_rank_even | The rank of an alternating form is even, including characteristic two. | Linear algebra of alternating forms. |
| alternating_isometry_class | Alternating forms of the same dimension and rank are isometric. | Splitting into radical and symplectic pairs. |
| frame_embedding_count | Count isometric injections of a j-dimensional form of rank 2s into a nondegenerate D-space. | Successive choices of symplectic pairs and radical vectors. |
| subspace_type_count | Count j-subspaces on which the ambient form has rank 2s. | Embedding count divided by the isometry group of the source. |
| gaussian_subspace_count | Gaussian binomial coefficients count subspaces. | Finite vector-space counting. |
| block_kernel_moments | Exact Gaussian-binomial moments of nullity(A) and nullity(U). | The previous three counts. |
| residual_kernel_moments | Exact Gaussian-binomial moments of nullity(Lambda(U)) and nullity(T_b). | Isometric injections and independent linear pairing constraints. |
| residual_likelihood | The likelihood ratio depends only on the residual nullity. | Count hidden blocks by their kernel and quotient form. |
| residual_likelihood_sign | The ratio is below one exactly for nonsingular residuals. | Elementary finite-product inequalities. |
| optimal_residual_test | Residual singularity attains total variation exactly. | Likelihood-sign lemma and finite probability algebra. |

### Embedding count

For a form of dimension j and rank 2s, write

    E_D(j,s) = q^(Dj - j(j-1)/2) Phi_D(j,s),

where Phi_D is the finite product of (1-q^(-2i)) for
D/2-j+s+1 <= i <= D/2 when j-s <= D/2, and is zero otherwise.
The infeasible case must be explicit. The formula is an equality in the
rationals after interpreting negative powers there; the left side is an integer.

### Exact moment identities

Let d=a-b with a>=b. Put

    gamma_j = product_(i=1)^j (1-q^(-i)),
    m_j^d = q^(-j(j+d))/gamma_j,
    m'_j = q^(-j(j-1)/2)/gamma_j.

For H uniform on alternating j-by-j matrices, use s=rank(H)/2. The four
identities to formalize for 0<=j<=b are

    E [nullity(A) choose j]_q = m_j^d E_H(Phi_b^2/Phi_(a+b)),
    E [nullity(U) choose j]_q = m_j^d E_H Phi_b,
    E [nullity(Lambda(U)) choose j]_q = m'_j E_H(Phi_a Phi_b),
    E [nullity(T_b) choose j]_q = m'_j E_H Phi_b.

For the third identity, if K is a j-subspace contained in the residual radical,
the restriction U|K must be an isometric injection: if Ux=0 for x in K, then
J_b(x,y)=0 for every y, hence x=0. Once U|K has been chosen, each remaining
column has j independent prescribed pairings. This is the main linear-algebra
step and should be proved directly, rather than inferred from the square case.

## 3. Infinite products and limiting probability laws

Pass to real-valued probabilities and establish positivity and convergence of

    gamma_infinity = product_(i>=1)(1-q^(-i)),
    eta_infinity   = product_(i>=1)(1-q^(-2i)),
    theta_infinity = product_(i>=1)(1-q^(-(2i-1))).

Prove gamma_infinity = eta_infinity theta_infinity. A reusable lemma for
products of (1-x_i), with 0<=x_i<1 and summable x_i, gives positivity and
explicit tail estimates. Prove first-order expansions with an actual bound on
the remainder before using asymptotic notation.

The classical rectangular and even alternating limiting nullity laws are

    pi_d(k) = gamma_infinity q^(-k(k+d))/(gamma_k gamma_(k+d)),
    lambda(2k) = theta_infinity q^(-k(2k-1))/gamma_(2k),
    lambda(2k+1) = 0.

They are probability laws and have Gaussian-binomial moments m_j^d and m'_j.
One formal route derives these from finite matrix counts, proves a summable
upper bound uniform in the finite dimension, and passes to the limit. The
classical formulas should be recorded as antecedent lemmas, not as new results.

## 4. Uniform error estimates

Define W(H)=(q^(2(j-s))-1)/(q^2-1). Prove

    E_H W(H) = (q^j-1)/(q-1).

This follows by counting pairs (H,x) with nonzero x in the kernel. Prove the
product estimate

    Phi_D = 1-q^(-D)W + O_q(q^(-2D)q^(4j))

on both feasible and infeasible ranges. In the infeasible range Phi_D=0 and
q^(-D)W>=1, which controls the apparent first-order term. For j<=b<=a,
Phi_(a+b) is feasible and at least eta_infinity, so division is uniformly safe.

The required error bounds are genuinely uniform. In the rank calculation the
initial remainder contains q^(-2b)m_j^d q^(4j). At j=0 the error is exactly
zero. At j>=1, use q^(-dj)<=q^(-d) to obtain

    C_q q^(-(a+b)) q^(-j^2+4j).

Without this step the proof establishes only a weaker, gap-dependent estimate.

For the residual calculation use the product directly:

    Phi_b(Phi_a-1) = -q^(-a)W + O_q(q^(-(a+b))q^(4j)).

This avoids weakening the rectangular error when a is much larger than b.

## 5. Recovering distributions from their moments

### Rank law: Gaussian-binomial inversion

Formalize finite inversion first:

    p_k = sum_(j>=k) (-1)^(j-k) q^((j-k)(j-k-1)/2) [j choose k]_q mu_j.

The sum is finite for a finitely supported law. The column's absolute sum is
exactly product_(i=0)^(j-1)(1+q^i), by the q-binomial theorem, and hence is at
most C_q q^(j(j-1)/2).

Introduce the signed sequence

    xi_d(k) = (1+q^(-d)-q^k) pi_d(k)/(q-1).

Its moments follow from

    (q^k-q^j)[k choose j]_q
      = q^j(q^(j+1)-1)[k choose j+1]_q.

The rank-law correction is q^(-b)xi_d. To justify infinite inversion, prove
absolute convergence of the double sum before interchanging it. The bound
on the scaled sequence chi_d=q^d xi_d is uniform:

    |chi_d(k)| <= C_q q^(-k^2+k) for k>=1,

with k=0 treated separately. Also

    sum_(j<=k) q^(j(j-1)/2)[k choose j]_q
       <= C_q q^(k(k-1)/2).

Their product is summable. For moments with j>b, only the signed correction
remains; its error is still bounded by
C_q q^(-(a+b))q^(-j^2+2j). Summing all inversion columns gives the claimed
L1 remainder through the convergent series
sum_j q^(-j^2/2+7j/2).

### Residual law: interpolation on the even grid

Use polynomial indicators on the grid 1,q^2,...,q^b. Their coefficients are
bounded by the even-grid estimate given in the manuscript. The power-moment
error leaves a summable quadratic exponent. The limiting signed correction
is supported on even nullities, which is essential: ordinary-grid estimates
lose too much for this slower-decaying family of moments.

Handle the infinite signed tail separately. Its first point beyond the grid
is b+2, and its contribution after the factor q^(-a) is bounded by
C_q q^(-a-b^2/4+1). This is O_q(q^(-(a+b))) uniformly over positive even b;
the finitely many small b are absorbed into a q-dependent constant.

## 6. Main theorem and precise quantifiers

The uniform statements should be proved with quantifiers of the following
mathematical form before introducing big-O notation:

    There exists C_q>0 such that for every positive even a>=b,
    the specified L1 remainder is at most C_q q^(-(a+b)).

There is one constant for all gaps d=a-b. The theorem does not mean that for
each fixed d there is a separate constant. The full-matrix expansion similarly
has one C_q multiplying (q^(-a)+q^(-b))^2.

For total variation of the rank laws, prove that xi_d has total mass zero and
has only one positive mass, at k=0; the coefficient at k=1 can be zero when
q=2 and d=0. This gives the explicit leading coefficient without needing an
exact finite-dimensional optimality statement for the rank-only test.

For full matrix total variation, combine the already proved exact optimal
residual test with the residual-law estimate at zero and the finite-product
expansion of the likelihood normalizer. The coefficient is

    C(q) = theta_infinity (q-(q+1)eta_infinity)/(q^2-1),

which is negative. The limit is
Delta(q)=theta_infinity(1-eta_infinity)>0.

Finally convert nullity distances to rank distances by the bijection k -> b-k.
State the statistical interpretation separately: with equal prior probabilities,
optimal classification success is (1+TV)/2.

## 7. What would count as completed formal verification

A completed formalization would include all transitive dependencies of the
new theorem, compile against a recorded Lean/Mathlib revision, and expose the
assumptions of the final declarations. Imported counting results would have to
be checked Lean theorems, not axioms mirroring the desired conclusion. Any
remaining analytic or combinatorial assumptions would need explicit theorem
parameters and a corresponding conditional status.

The Python certificates can guide finite sanity checks during implementation.
They do not replace the uniform product bounds, the infinite summability
arguments, or the universal quantifiers over all finite-field dimensions.
