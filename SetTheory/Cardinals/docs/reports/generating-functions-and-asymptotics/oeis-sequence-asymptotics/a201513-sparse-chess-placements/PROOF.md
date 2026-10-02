# Sparse nonattacking chess placements: every fixed asymptotic order

## 1. Scope, sequences, and attribution

Let K_n be the number of placements of n indistinguishable nonattacking kings on an ordinary n by n square board (OEIS A201513), and N_n the corresponding number for knights (A201540). Rotations and reflections are distinct placements. There is no requirement of one piece per row or column.

Kotěšovec's leading equivalent, dated 29 November 2011 and reproduced in his book, is

K_n ~ N_n ~ exp(-9/2) n^(2n)/n!.

This leading law is not new. The book also contains fixed-piece polynomial formulas, notably pp. 65, 77, and 283–293, and a general bounded-move leading argument at pp. 685–686. This report supplies explicit specialized corrections, a finite exact algorithm for each further order, an elementary uniform remainder argument, and growth-index inversion. It does not claim a new general cluster-expansion method: canonical independent-set cluster expansions and convergent tails already occur, for example, in Davies, Jenssen, and Perkins, *A proof of the Upper Matching Conjecture for large graphs*, arXiv:2004.06695. The derivation below is self-contained.

The actual OEIS entries and cited book pages were inspected on 2 October 2026. No claim of exhaustive historical priority is made for every individual coefficient. No fit to sequence values enters any result.

## 2. Explicit results

For every fixed M, both sequences admit expansions with remainder O(n^(-M-1)) relative to their common factorial carrier. In particular,

K_n = exp(-9/2) n^(2n)/n! [1 + 7/(3n) + 119/(9n^2) + 11327/(810n^3) + 90475/(1944n^4) + O(n^-5)],

N_n = exp(-9/2) n^(2n)/n! [1 + 37/(3n) + 914/(9n^2) + 330917/(810n^3) + 966583/(1944n^4) + O(n^-5)].

Consequently,

N_n/K_n = 1 + 10/n + 65/n^2 + 332/(3n^3) - 4841/(6n^4) + O(n^-5).

The corresponding logarithmic corrections, relative to the factorial carrier, are

log(K_n n! / (exp(-9/2)n^(2n))) = 7/(3n) + 21/(2n^2) - 379/(30n^3) - 357/(40n^4) + O(n^-5),

log(N_n n! / (exp(-9/2)n^(2n))) = 37/(3n) + 51/(2n^2) - 6559/(30n^3) - 1397/(40n^4) + O(n^-5).

If the carrier is instead exp(-9/2)(en)^n/sqrt(2*pi*n), the first relative corrections are 9/(4n) and 49/(4n), respectively. Keeping track of the carrier matters.

Two useful neighbors are the grid graph (wazirs, A201511) and diagonal-neighbor graph (ferses, A201861). Their carrier is exp(-5/2)n^(2n)/n!, and their first four corrections are respectively

(7/3, 32/9, -1003/810, 68291/9720),

(13/3, 128/9, 8267/810, -388861/9720).

## 3. General finite-range theorem

Fix a finite nonempty symmetric move set S contained in Z^2 minus {(0,0)}. Write d=|S|. On V_n={0,...,n-1}^2 join x and y when y-x belongs to S; call the resulting graph G_n. Its maximum degree is at most d. Let I_n(z)=sum_k a(n,k)z^k be its independence polynomial and write

log I_n(z)=sum_(j>=1) b_j(n)z^j.

For each fixed j there are rational alpha_j, beta_j, gamma_j such that

b_j(n)=alpha_j n^2 + beta_j n + gamma_j

for every sufficiently large integer n. In particular alpha_1=1, beta_1=gamma_1=0, and alpha_2=-(d+1)/2. Put a=alpha_2.

For every fixed M>=0,

a(n,n)=n^(2n)/n! exp(a) [sum_(r=0)^M c_r n^-r + O_(M,S)(n^(-M-1))],

where c_0=1 and every c_r is rational. Section 6 gives a finite formula requiring only b_2,...,b_(M+2).

More generally, let theta=k/n and restrict theta to any fixed compact interval in (0,infinity). Uniformly for all integers k with k/n in this interval,

a(n,k)=n^(2k)/k! exp(a theta^2) [sum_(r=0)^M c_r(theta)n^-r + O_(M,S,interval)(n^(-M-1))].

Each c_r(theta) is given by the explicit finite operator formula below; in particular it is a Laurent polynomial over the rationals. The theorem uses the actual theta=k/n and therefore retains any floor phase if k=floor(lambda n). It does not assert uniformity for theta tending to zero or infinity.

## 4. Exact connected-support coefficients

For a finite graph H, write L_j(H)=[z^j]log I_H(z). For a nonempty vertex set T of G_n, define

w_j(T)=sum_(U subset T) (-1)^(|T|-|U|) L_j(G_n[U]).

The empty graph contributes zero. Multivariate formal logarithms show:

1. w_j(T)=0 if |T|>j;
2. w_j(T)=0 if the induced graph on T is disconnected;
3. b_j(n)=sum_(nonempty T subset V_n) w_j(T).

For completeness, replace z at each vertex v by its own variable z_v. A degree-j monomial of log I has support of size at most j. Mobius inversion above collects precisely the monomials whose support is all of T, after all variables are set equal. If the induced graph on T splits into two nonempty components, its independence polynomial factors, so its logarithm is a sum and contains no monomial using both components. This proves all three assertions.

Enumerate every finite nonempty S-connected lattice subset T of size at most j modulo translations, choosing the unique representative with minimum x and minimum y both zero. Let w(T)=max x and h(T)=max y. Its number of translates contained in V_n is exactly

(n-w(T))_+ (n-h(T))_+.

Thus, for all n,

b_j(n)=sum_T w_j(T) (n-w(T))_+ (n-h(T))_+.

There are finitely many such T because the moves are fixed and T is connected. If R=max_(u in S) max(|u_1|,|u_2|), then w(T),h(T)<=R(j-1). Consequently n>=R(j-1)+1 permits removal of both positive-part signs and gives the quadratic polynomial exactly:

alpha_j=sum_T w_j(T),
beta_j=-sum_T w_j(T)(w(T)+h(T)),
gamma_j=sum_T w_j(T)w(T)h(T).

This is a finite formula, not an asymptotic approximation or interpolation. The accompanying `compute_clusters.py` implements it with integer arithmetic for j L_j and rational arithmetic for alpha,beta,gamma.

## 5. A uniform analytic bound

The connected-support identity alone does not justify inserting k=n into a fixed-k polynomial expansion. We now supply a uniform analytic bound.

### Lemma (bounded-degree zero-free disk)

For every graph G of maximum degree at most d, I_G(z) is nonzero when |z|<=r=1/[4(d+1)]. Its logarithm with value zero at z=0 satisfies

|log I_G(z)|<=4 |V(G)| |z|,

and hence

|[z^j]log I_G(z)|<=4 |V(G)| r^(1-j).

### Proof

Put delta=1/[2(d+1)]. Induct on |V(G)|, proving simultaneously that every ratio I_G(z)/I_(G-v)(z) exists and differs from 1 in modulus by at most delta. The deletion identity gives

I_G/I_(G-v)=1+z I_(G-N[v])/I_(G-v).

Delete the at most d neighbors of v one at a time in G-v. The induction hypothesis bounds the second quotient by (1-delta)^(-d)<2, since d[-log(1-delta)]<=d*delta/(1-delta)<1/2. Therefore the displayed ratio differs from 1 by at most 2|z|<=delta. It is nonzero, closing the induction. Each ratio has an analytic logarithm, and

|log(ratio)|<=|ratio-1|/(1-delta)<=4|z|.

Telescope along any vertex deletion order to obtain the logarithm bound. Cauchy's coefficient estimate on |z|=r gives the last inequality. This proof uses no root location conjecture or thermodynamic-limit assumption.

### Consequence

For a fixed radius R_0>1 and any fixed J, the tail in log I_n(theta t/n), uniformly on |t|<=R_0 and theta in a fixed compact positive interval, is bounded by

sum_(j>J) 4n^2 r^(1-j) (theta R_0/n)^j=O(n^(1-J)).

For the finitely many retained j, use the exact quadratic polynomials of Section 4. With J=M+2 this gives

I_n(theta t/n) exp(-theta n t)
 = exp(a theta^2 t^2) [sum_(r=0)^M H_r(t;theta)n^-r + O(n^(-M-1))]

uniformly on that closed complex disk. Exponentiation preserves the bound since all retained functions are uniformly bounded there.

## 6. Exact coefficient extraction and the all-order formula

Define h_l(t;theta) for l>=1 by

h_l(t;theta)=alpha_(l+2)(theta t)^(l+2) + beta_(l+1)(theta t)^(l+1) + gamma_l(theta t)^l,

where missing indices below 2 are interpreted as zero. Let H_0=1 and define polynomials H_r by

sum_(r>=0) H_r(t;theta) epsilon^r = exp(sum_(l>=1) h_l(t;theta) epsilon^l).

Only l<=r is needed for H_r, and the exact recursion is

r H_r = sum_(l=1)^r l h_l H_(r-l).

Define polynomials P_q(m) by

sum_(q>=0) P_q(m) epsilon^q
 = exp[-sum_(l>=1) (epsilon^l/l) sum_(i=0)^(m-1) i^l].

Faulhaber's formula makes every P_q a rational polynomial of degree at most 2q. In particular

P_0=1,
P_1=-m(m-1)/2,
P_2=m(m-1)(m-2)(3m-1)/24.

Let D=t d/dt. Then

c_r(theta)=exp(-a theta^2) sum_(q=0)^r theta^(-q)
 [P_q(D){exp(a theta^2t^2) H_(r-q)(t;theta)}]_(t=1).

This is a finite exact algorithm. Its apparent exponential factors cancel. For the diagonal theta=1 all coefficients are rational.

### Proof of the extraction and error estimate

Put H_(n,k)(t)=I_n(theta t/n)exp(-kt), where k=theta n. The exact identity is

a(n,k)/(n^(2k)/k!) = sum_(m=0)^k [t^m]H_(n,k)(t) (k)_m/k^m.

Indeed, expand exp(kt) and extract [t^k]; the scale factor in I_n(theta t/n) is (k/n^2)^k. This identity is valid for every positive integer k.

On analytic functions on |t|<=R_0>1, this linear functional has bounded norm independent of k: coefficient estimates and 0<=(k)_m/k^m<=1 bound the sum by (1-1/R_0)^(-1) times the supremum. The analytic remainder in Section 5 therefore remains O(n^(-M-1)) after extraction.

For the remaining finitely many analytic coefficient functions expand

(k)_m/k^m = sum_(q=0)^M P_q(m)k^-q + error.

For 0<=m<=sqrt(k), expand the finite product prod_(i=0)^(m-1)(1-i/k) in elementary symmetric functions. With A=m(m-1)/2, the absolute remainder is at most

k^(-M-1) A^(M+1)/(M+1)! exp(A/k)
 <= C_M k^(-M-1) m^(2M+2).

The geometrically decaying coefficients make the sum of this bound O(k^(-M-1)). For m>sqrt(k), both the exact functional and each polynomial P_q(m) have an exponentially small coefficient tail, O(poly(k) R_0^(-sqrt(k))). Extending the polynomial sums to all m introduces the same harmless error. Finally sum m^j[t^m]f(t)=D^j f(1). As k and n are uniformly comparable, the stated formula and uniform error follow.

## 7. First correction in geometric form

Let B=(1/2)sum_(u in S)(|u_1|+|u_2|). Let tau be the number of lattice triangles per bulk vertex: equivalently, tau=(1/6) times the number of ordered pairs (u,v) in S^2 with v-u in S. This convention gives tau=4 for kings and tau=0 for knights.

The elementary graph identities

b_2=-|V|/2-|E|,

b_3=|V|/3+2|E|+sum_v binom(deg(v),2)-#triangles

give

alpha_2=-(d+1)/2,
beta_2=B,
alpha_3=1/3+d(d+1)/2-tau.

The first operator yields

c_1(theta)=(d+1)theta/2+B theta^2-[ (d+1)/2+tau-1/3]theta^3.

In particular c_1(1)=B+1/3-tau. For kings (d,B,tau)=(8,6,4), and for knights (8,12,0). Their equal leading term sees only the degree; the first correction sees the boundary and triangles.

For kings,
c_1(theta)=-theta(49theta^2-36theta-27)/6,
c_2(theta)=theta(2401theta^5-3528theta^4-2628theta^3+4248theta^2+891theta-432)/72.

For knights,
c_1(theta)=-theta(25theta^2-72theta-27)/6,
c_2(theta)=theta(625theta^5-3600theta^4+3924theta^3+7632theta^2-405theta-864)/72.

## 8. Cluster data and exact checks

Rows below are (alpha_j,beta_j,gamma_j), j=2,...,6.

Kings:
(-9/2,6,-2),
(97/3,-76,44),
(-1133/4,907,-715),
(13856/5,-10936,10632),
(-58193/2,134242,-458096/3).

Knights:
(-9/2,12,-8),
(109/3,-164,180),
(-1489/4,2226,-3248),
(21771/5,-31468,55684),
(-110719/2,460910,-2826242/3).

The connected support counts of sizes 1,...,6 modulo translations are
kings: 1,4,20,110,638,3832;
knights: 1,4,28,234,2162,20972.

The generator exhaustively grows every connected shape from the singleton; every connected finite graph has a vertex deletion order preserving connectedness, so no shape is omitted. Translation normalization, not rotation or reflection normalization, avoids accidental symmetry division. Graph-log coefficients use the exact recurrence j b_j = j i_j - sum_(k=1)^(j-1) k b_k i_(j-k). Support Mobius inversion is exact.

An independent finite-board program enumerates independent subsets directly on 3x3, 4x4 and 5x5 boards for each of kings, knights, wazirs and ferses. It compares every log coefficient through order 6 with the clipped-support formula. The detailed results are in `finite_verification.txt`. These finite checks validate the implementation; the preceding analytic proof supplies the asymptotic theorem and its remainder.

## 9. Growth-index inverse and rounding caveat

Let A_n denote either K_n or N_n. Stirling's expansion and Section 2 give

log A_n = n(log n+1) - (1/2)log(2*pi*n) + a + d_1/n + d_2/n^2 + ...,

where a=-9/2, d_1=9/4 for kings and 49/4 for knights. Every fixed order is valid with a controlled remainder. For any fixed truncation, replace n by a positive real variable; this defines a smooth asymptotic model, not an assertion that the combinatorial count is defined for noninteger boards.

Given y tending to infinity, set L=log y, x=L/W(eL), D=log x+2, and

delta_0=[(1/2)log(2*pi*x)-a]/D.

For any logarithmic model retaining at least the d_1/n term, its inverse has

n=x+delta_0+[delta_0/2-delta_0^2/2-d_1]/(xD)+O(1/(x^2D)).

Proof: x(log x+1)=L. Taylor expansion at x first cancels the logarithmic-and-constant residual with delta_0. The remaining term of order x^-1 is (delta_0^2/2-delta_0/2+d_1)/x; division by the derivative D gives the next correction. All derivatives of the displayed residual have the indicated bounds, and the derivative is D+O(1/x), bounded away from zero. Newton's method or recursive Taylor cancellation produces every further fixed order.

For an integer threshold, A_n is eventually strictly increasing, since the proved leading equivalent implies A_(n+1)/A_n ~ e^2 n. If q_M(y) is the root of the logarithmic model through d_M/n^M, then the actual threshold N(y)=min{n>=n_0:A_n>=y} lies between the ceilings of q_M(y) plus or minus O(q_M^(-M-1)/log q_M). A unique rounded answer follows whenever that small interval avoids an integer. No finite-order asymptotic can guarantee unconditional rounding at thresholds arbitrarily close to A_n.

## 10. References

1. OEIS Foundation, A201513, https://oeis.org/A201513 ; A201540, https://oeis.org/A201540 ; A201511, https://oeis.org/A201511 ; A201861, https://oeis.org/A201861 . Definitions and leading equivalents inspected 2 October 2026.
2. V. Kotěšovec, *Non-attacking Chess Pieces*, sixth edition, 2013 (online file includes subsequent table updates), pp. 77, 293, 382, 423, 683, 685–686. https://www.kotesovec.cz/books/kotesovec_non_attacking_chess_pieces_2013_6ed.pdf . The author's HTTP endpoint supplied the PDF when HTTPS timed out.
3. E. Davies, M. Jenssen, W. Perkins, *A proof of the Upper Matching Conjecture for large graphs*, arXiv:2004.06695, https://arxiv.org/abs/2004.06695 . Prior general canonical cluster-expansion framework; not a claim that the present chess coefficients occur there.
