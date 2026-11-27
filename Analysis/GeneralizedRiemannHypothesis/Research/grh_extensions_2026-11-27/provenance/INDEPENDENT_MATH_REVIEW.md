# Independent verification of the rectangular rank-blindness theorem

This review is independent of the proposed proof and uses exact finite-field counting formulas in the inspected Article. It verifies the algebra and asymptotic estimates below. No claim of literature priority is made here.

## Parameters

Fix a prime power q, put Q=1/q, and let n>=c>=1 with b=n+c even. Set m=b/2 and h=n-c (so h is nonnegative and even). Let H be a nondegenerate alternating b-by-b matrix. Let X0 be an injective 2n-by-b frame with Gram matrix H. For uniform g in Sp(2n,q), let A be the upper n rows of gX0, and let U be a uniform n-by-b matrix.

Write a_j=product_{i=1}^j (1-Q^i), a_infinity=product_{i>=1}(1-Q^i), and

C=product_{j=h/2+1}^n (1-Q^(2j)).

## Exact density

For M with kernel K and k=dim K, the density of A relative to U is

L(M)=1_{K is H-isotropic} Q^(-k(k-1)/2)/C.

For a direct independent count, reduce M by invertible row and column operations to a rank-r diagonal block, r=b-k. Then B in the lower n rows has blocks of sizes r and k in its columns, and r and n-r in its rows. The equation M^T B-B^T M=H fixes the upper-right block, leaves a symmetric part of dimension r(r+1)/2, and leaves (n-r)b further free entries. Solvability is precisely isotropy of K. Since H is nondegenerate, every solution (M;B) is automatically injective. The number of B is

q^[nb-b(b-1)/2+k(k-1)/2].

The number of H-frames in a symplectic 2n-space is

q^[2nb-b(b-1)/2] C.

Division gives the displayed density, in every characteristic, with alternating understood to include zero diagonal in characteristic two. Every positive density is greater than one.

## Nullity law and exact sign threshold

For k>=c the uniform nullity probability is

u(k)=Q^[k(k-c)] a_n a_b/[a_k a_(k-c) a_(b-k)].

The probability that a uniform k-subspace is H-isotropic is Q^[k(k-1)/2] R_k, where

R_k=product_{i=0}^{k-1}(1-Q^(b-2i))/(1-Q^(b-i))

for k<=m, and R_k=0 otherwise. Thus the ratio of the A-nullity law to the U-nullity law is r_k=R_k/C.

Define D=product_{j=n+1}^{n+c}(1-Q^j), E=product_{j=m+1}^n(1-Q^(2j)). Then R_c/C=1/(DE)>1.

If h=0, k=c is the only supported nullity. If h>=2,

R_(c+1)/C=(1-Q^h)/[(1-Q^n) D E]<1.

For completeness, the strict inequality follows from 1-product(1-x_i)<=sum x_i and

1-(1-Q^n)DE <= Q^n(1-Q^(c+1))/(1-Q)+Q^(n+c+2)/(1-Q^2).

After division by Q^h, the right side is

f_c=Q^c(1-Q^(c+1))/(1-Q)+Q^(2c+2)/(1-Q^2).

The quantity f_c decreases in c>=1. Since Q<=1/2,

f_c<=f_1=Q+Q^2+Q^4/(1-Q^2)<=5/6<1.

Further factors of R_k are in [0,1], so all k>=c+1 have r_k<1. Consequently the optimal rank-only distinguishing event is full row rank, k=c, and

d_TV(rank A,rank U)=(a_n/a_c)(E^(-1)-D).

## Uniform asymptotic for rank distance

As c tends to infinity, uniformly over n>=c with the required parity,

d_TV(rank A,rank U)=Q^n/(q-1) [1+O_q(Q^c)].

Indeed a_n/a_c=1+O_q(Q^c),

1-D=Q^n/(q-1) [1+O_q(Q^c)],

and E^(-1)-1=O_q(Q^(n+c+2)). This requires no assumption that h=n-c tends to infinity. At h=0 it reduces to the probability that a uniform n-by-2n matrix fails to have full row rank, as it should.

## Full-matrix overlap and the endpoint factor

Because every supported density is greater than one,

1-d_TV(A,U)=P(ker U is H-isotropic)
          =sum_{k=c}^m u(k) Q^[k(k-1)/2] R_k.

The first summand is exactly

T0=Q^[c(c-1)/2] (a_n/a_c) product_{j=h/2+1}^{h/2+c}(1-Q^(2j)).

For k=c+j, j>=1, division by T0 gives the useful bound

Tj/T0 <= a_infinity^(-2) Q^[2cj+(3j^2-j)/2].

This uses R_(c+j)<=R_c and

u(c+j)/u(c)<=a_infinity^(-2) Q^[cj+j^2].

The entire remaining sum is therefore O_q(Q^(2c+1)) times T0. Let

B_h=product_{j=h/2+1}^infinity(1-Q^(2j)).

It follows uniformly in even h>=0 that

1-d_TV(A,U)=Q^[c(c-1)/2] B_h [1+O_q(Q^c)].

The replacement B_h=1+o(1) is valid if and only if h tends to infinity. At h=0, B_h is the nontrivial even Euler product; omitting it would be an error. In every regime c tends to infinity, the full-matrix distance tends to one while the rank distance tends to zero.

## Rank-only sample complexity

Let P be the rank/nullity law of A and Qlaw the corresponding law of U. Then

chi^2(P||Qlaw)=Q^(2n-c)/(q-1) [1+O_q(Q^c)],

uniformly as c tends to infinity, including h=0.

Proof: write j=k-c for row deficiency. The j=1 term dominates:

u(c+1)=Q^c/(q-1) [1+O_q(Q^c)],
1-r_(c+1)=Q^h [1+O_q(Q^c)].

The second identity is exact with value one when h=0. The j=0 contribution is O_q(Q^(2n)), hence a factor O_q(Q^c) smaller than the claimed main term. For j>=2,

u(c+j)<=K_q Q^[j(c+j)],
|1-r_(c+j)|<=K_q Q^[h-2(j-1)].

For j<=h/2, the latter follows by bounding the defect of the product of the additional isotropy factors; for j>h/2, r=0 and the displayed right side is at least one. Dividing the j-th chi-square contribution by Q^(c+2h) gives

at most K_q Q^[(j-1)c+(j-2)^2].

Summation gives a relative O_q(Q^c) error.

For t independent matrix samples, the product rank-law chi-square divergence is exactly (1+chi^2(P||Qlaw))^t-1. Thus no rank-only test has asymptotic distinguishing advantage when t=o(q^(2n-c)).

Conversely, count full-row-rank samples. The difference of the success probabilities is Delta~Q^n/(q-1); each variance is at most the U failure probability, asymptotic to Q^c/(q-1). A midpoint threshold and Chebyshev's inequality give total error O_q(q^(2n-c)/t). Therefore t much larger than q^(2n-c) suffices for both errors to vanish. The sample-complexity scale q^(2n-c) is sharp in this sense.

## Novelty boundary

The existing Article already gives exact arbitrary symplectic compression laws, so the exact density and the general counting method should be credited as a specialization/closed-form extension. The principal new contribution relative to that Article is the asymptotic regime where full-matrix distance tends to one, the uniform endpoint factor, and the sharp rank-only sample-complexity scale. Article's square nondegenerate result had a positive limiting full-matrix distance strictly below one and did not establish this rectangular information-theoretic amplification.
