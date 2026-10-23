# Selective monomial isolation with overlapping target intervals

## Scope

This is a new source-layer construction. It does not change the native compiler
coefficient tuple, the number-theoretic finalizer, or the domain of its final
unknowns. Those interfaces must be inherited from one coherent source package.
In particular, package45 changes the old positive transport variable by
`z_old=z+1`. Its row15 is the old row15 minus `beta*(n_J+1)` after shifting to
nonnegative source coordinates. The support code below works for either
version, but their coefficient recipes and completeness arguments must not be
mixed. The independent checker verifies the exact transport difference.

## 1. A certificate weaker than a Sidon set

Let `r_k(x)=sum_alpha p_(k,alpha) x^alpha`, for `1<=k<=m`, be fixed integral
polynomials of degree at most two in `n` nonnegative coordinates. The polynomial
coefficients can depend on a fixed tuple of integer ports. Let `S_k` be the
support with those ports treated formally. Introduce a padding coordinate
`x_0=1` and assign positive integer weights `w_1,...,w_n`, with `w_0=0`.
A degree-at-most-two multi-index is padded with zeros to an unordered pair;
write `e(alpha)=sum_i alpha_i w_i`.

Choose distinct nonnegative targets `q_k`. It is enough to certify:

1. `q_k-e(alpha)>=0` for every `alpha in S_k`.
2. For every `k,j`, every `alpha in S_k`, and every multi-index `beta` of degree
   at most two,

   `q_k-e(alpha)+e(beta)=q_j` if and only if `k=j` and `alpha=beta`.

The reverse implication in condition2 is automatic. The forward implication is
one finite check. It does not require different absent monomials to have
different sums, or the intervals occupied by different residuals to be disjoint.
Only a monomial used in a residual needs to be isolated from all possible
monomials in the square of the input code. In the present system there are
71 used padded pairs, including32 constant/linear pairs and39 genuine
quadratic pairs, rather than all528 padded pairs.

Define

`c_(k,alpha)=(2-|alpha|)! product_i(alpha_i!) p_(k,alpha)`,

`D(t)=sum_(k,alpha) c_(k,alpha) t^(q_k-e(alpha))`,

`C_x(t)=(1+sum_(i=1)^n x_i t^w_i)^2`.

Then for every integer source vector x,

`[t^q_j](C_x(t)D(t))=2 r_j(x)`.

Indeed, the coefficient of `x^beta t^e(beta)` in C is
`2/((2-|beta|)! product_i beta_i!)`. Condition2 selects exactly the term
`k=j,alpha=beta`; the factorials cancel. This is a polynomial identity, not
merely a numerical test on small source values.

## 2. Why coefficient bounds do not inflate

Condition2 itself implies that the exponents of all displayed terms of D are
distinct. If `q_k-e(alpha)=q_j-e(gamma)`, then multiplying either term by the
monomial at `e(gamma)` lands at `q_j`. Condition2 therefore forces
`k=j` and `alpha=gamma`. Thus overlapping *intervals* do not entail overlapping
*coefficients* in a valid isolation certificate.

Consequently, if `A=max_(k,alpha)|c_(k,alpha)|`, then every coefficient of D has
absolute value at most A. For nonnegative x,

`|[t^s](C_x D)| <= A (1+sum_i x_i)^2`.

This follows by the triangle inequality and the sum of the nonnegative
coefficients of C. There is no factor m and no overlap multiplicity.

Assume the maximum target Q belongs to a residual with positive constant
coefficient, and all input weights are positive. Then the leading coefficient
of D is `2 r_last(0)>0`, its degree is Q, and `D(B)>0` for integral `B>A+1`:
the absolute lower-degree contribution is at most
`A (B^Q-1)/(B-1)<B^Q`, whereas the leading coefficient is a positive integer.

## 3. Carry decoding and the inherited source contract

Put `M=max_i w_i`, `H=Q+2M`, `ell=sum_i B^w_i`, and
`A_targets=sum_k B^q_k`. Let `B=beta_source b^2`, where beta_source is the
same sufficiently large even power of two used by the coherent parent.
For the present n=31 source the inherited estimate
`beta_source>4*33^2*L`, with `L=max|p_(k,alpha)|`, remains sufficient because
`A<=2L` and Section2 preserves the original D-coefficient bound.

Use the original source definitions with

`N0=B^(M+1)`, `N1=4 B^(H+1)`, `N=N0 N1`, `cap=b B^M`,

`Mcode=N0-1-(b-1)ell`,

`T=Mcode+(B-2)A_targets N0`,

`J=2(1+g)^2 D(B)+B sum_(s=0)^H B^s`,

`S=g+J N0`.

For square b as in the parent bridge and `0<=g<2cap`, the old estimates still
apply: `0<=Mcode<N0`, `0<T<N`, `0<J<N1`, and `0<=S<N`. Specifically the mask
has distinct target cells below `B^(Q+1)<=B^(H+1)`, while the bound for J uses
only `deg D=Q`, the unchanged A, and `g<2bB^M`. Neither argument needs uniform
target spacing or monotone input weights.

When b is a power of two, the low mask decodes g uniquely as
`g=sum_i x_i B^w_i`, with `0<=x_i<b`; distinct weights suffice for this step.
The base-B digits of

`J/2=C_x(B)D(B)+(B/2) sum_(s=0)^H B^s`

are strictly between0 andB because
`|[t^s] C_x D|<=2L(1+sum x_i)^2<2L(33b)^2<B/2`.
The target mask `(B/2-1) A_targets` therefore tests exactly whether every
target digit equals B/2. By Section1 this is equivalent to all residuals
vanishing. Doubling both operands and concatenating low and high words
recovers the same carry-free source predicate used by the inherited finalizer.
All estimates before the power-of-two deduction remain valid; the proof does
not assume prematurely that a square b is a power of two.

The zero source vector is not a common zero, because residual5 has constant1.
Thus a genuine source solution can be encoded with arbitrarily large
`b=4^s`, and `g>=B>=b`, as required by the old completeness argument.

## 4. Explicit certified instance

The fixed instance in `code_v1.json` uses the parent variable order

`J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta`.

The corresponding weights, including the initial padding0, are

`0,9,25,23,139,35,151,168,21,91,181,94,52,150,180,7,135,38,88,183,106,178,136,20,138,8,64,105,154,37,137,120`.

Residual order:

`16,2,9,14,21,7,15,22,13,3,19,20,1,10,17,8,4,6,11,18,12,5`.

Corresponding targets:

`70,86,451,685,1050,1296,1530,1874,2212,2358,2696,2780,2792,3157,3290,3634,3929,4238,4384,4527,4865,5190`.

Hence `M=183`, `Q=5190`, `H=5556`, and `N=4 B^5741` in the original source
wrapper. The old package43 values were `M=799`, `Q=35177`, `H=36775`, and
`N=4 B^37576`. Package45 shifts every uniform target by1 and has `Q=35178`.
These are exponent-span comparisons, not final polynomial degree or circuit
operation counts; those must be recomputed after compilation.

`verify_selective.py` independently derives the shifted source supports,
compares every weighted coefficient with the pinned package45 data after the
precise transport adjustment, checks all528 padded pairs, and enumerates all
71808 possible source-term/padded-pair products. Exactly136 contributions
land at marked targets, one per source term, and each is the intended one.
It also verifies injectivity of the136 reversed exponents and the leading
coefficient2. The checker uses only Python's standard library and does not
execute any upstream program. The randomized search is not part of the
mathematical proof or trusted verification path.

## 5. Limits and attribution

The selective condition was suggested as an open finite-search direction in
package43's `proof-notes/FURTHER_REDUCTIONS.md`. This iteration supplies a
successful explicit certificate and a sharper observation that isolation
already prevents D-coefficient collisions. The present work does not claim
that the weights, target span, final degree, operation count, or number of
variables are globally minimal. It gives no new proof of ZFC consistency.
The fixed-machine compiler, transport completeness where applicable, and
Sun/Jones arithmetic finalizers remain separately stated inherited theorems.
