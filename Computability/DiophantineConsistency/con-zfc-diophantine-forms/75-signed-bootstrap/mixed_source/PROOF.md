# Degree-separated monic projection

This is a verified source transformation and a general packing lemma, not a claimed improvement to the current nine-variable endpoint.

## Frozen source and projection

The input is the 31-positive-coordinate source copied in wave9/encoding/parent_source.json. Its exact SHA-256 is recorded in source24.json. Constants beta,K0,MC,MF are the inherited coherent positive compiler tuple; beta is positive. No coefficient ports are spliced.

Delete the defining rows 1,2,3,9,10,11,16 and their seven coordinates L,N,X,D,Delta,C2,F2. Reconstruct, in this order, with q=beta J+1:

L=q²−1, N=q³, X=qw, Delta=a²+4a+3, C2=c², F2=f²,
D=(4a+3)gamma+ac+X.

All seven quantities are strictly positive for every assignment of positive values to the remaining 24 coordinates. Each defining row is monic in the deleted coordinate. Substitution therefore gives a bijection between positive common zero sets of the original system and the 15 residuals in source24.json. build.py checks the symbolic identities, not merely numerical instances. The reduced residuals have maximum total degree four and 89 nonzero monomials, where the four compiler constants are coefficient parameters, not variables.

Consequently the explicit single equation sum(r_j²)=0 has 24 positive unknowns and degree eight, and is equivalent to the inherited source zero condition. Its lack of positive solutions is equivalent in ZFC to Con(ZFC), conditional on exactly the inherited source/compiler theorem already used by the 31-coordinate endpoint. This does not establish any global or repository minimum. The direct polynomial is specified unambiguously by the JSON residual list and sum-of-squares operation; its expansion is unnecessary.

## Mixed-degree kernel lemma

Let r_j(x)=sum_alpha c_(j,alpha) x^alpha be integer polynomials in n variables of degree at most d. Put m=d!, choose positive integer weights w_i and targets q_j, and write W_alpha=sum alpha_i w_i. Define

D_e(Z)=sum_(j,|alpha|=e) [m/e! * product(alpha_i!) * c_(j,alpha)] Z^(q_j−W_alpha),
U(Z)=sum_i x_i Z^w_i.

All kernel exponents must be nonnegative. Require, for every source monomial alpha in row j and every degree-e monomial gamma (including absent monomials),
q_k−q_j+W_alpha=W_gamma only when k=j and gamma=alpha.

Then coefficient q_j in sum_e D_e U^e is m r_j. Proof: the multinomial coefficient of x^alpha in U^e is e!/product(alpha_i!), cancelling the kernel factor. The isolation condition excludes all other contributions. Different homogeneous degrees may use identical weights and exponents; they are separated by the kernel index. There are no dummy homogenizing coordinates.

For existence, choose weights w_i=(d+1)^(i−1), whose degree-at-most-d sums encode exponent vectors uniquely. Let W=max_i w_i and choose q_j=dW+j(2dW+1). Distinct targets differ by more than any possible difference of degree-e weights, proving cross-row isolation. This is explicit but deliberately not offered as a competitive compact code.

## Carry caveat

If decoded coordinates satisfy 0<x_i<=b, coefficient height for a degree-d residual grows as O(b^d), not O(b²). Reusing a quadratic carry lemma with unchanged base B proportional to b² is unsound. With coefficient mass C, B>2 m C (b+1)^d suffices for the elementary signed-digit bound. A low-degree projection must reduce the target/convolution height enough to compensate for this larger base exponent. No such improvement has yet been validated for this projection. Kernel coefficient positivity, finalizer thresholds and gate counts also require fresh proofs before using this source in a compressed endpoint.

## A direct octic in 21 positive variables

Extend the preceding projection by deleting rows 7,13,20 and coordinates P,V,Baux. Reconstruct Baux=I², P=E(c−eta)+eta+zeta, and V=jc+hE−eta−zeta+1. The retained row4 forces a−E=sN>0. The retained row6 forces c=(eta+zeta)sN+eta>eta+zeta. Consequently P and V are positive, and the inverse reconstruction is unique. These conclusions use common-zero equations, not positivity of the formulas on every ambient tuple. Build.py checks all substituted original rows exactly. The resulting source21.json has 21 variables, 12 residuals, maximum degree4, and100 support terms. Its sum of squares is an explicit octic endpoint over positive integers with precisely the same consistency equivalence. No auxiliary variables are introduced in taking the sum of squares.

## A direct sextic in 26 positive variables

Instead delete only C2,F2,L,X,Baux and their defining rows. Reconstruct by c²,f²,q²−1,qw,I², all unconditionally positive. source26.json has26 variables,17 residuals, maximum degree3 and85 support terms. Its sum of squares is a sextic. These domain-qualified low-degree tradeoffs must be compared with positive-domain endpoints, not advertised as improvements to unrestricted-integer endpoints.

## Comparison correction

The repository already contains a 20-positive octic and a 25-positive sextic. Thus the 21-positive octic and 26-positive sextic here are dominated in unknown count at their respective degrees. They demonstrate the exact source projection and positive reconstruction, not new low-degree records.

## Explicit fixed instance

COEFFICIENT_BINDING.json selects the entire old31 tuple from the previous Oriented Guards package, nine/coefficients/old_tuple, with beta=2^1064921−1. Its nine/PROOF.md §1 identifies exactly the same frozen source SHA-256 1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287. The separate low_degree compact44 tuple is not substituted here. This manifest supersedes only the historical default-selection prose inside parent_source.json, not any source equation or byte.
