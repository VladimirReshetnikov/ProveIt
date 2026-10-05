# Fixed-displacement permutations: a recurrence-free complete expansion

Status: direct derivation, awaiting independent review. No conjectured recurrence is used.

## Scope and sources

For fixed positive integers r,s, let a_{r,s}(n) count permutations pi of [n]
such that pi(i+r)-pi(i) is never s. A189281 is a_{2,2}.

The exact paired-tiling identity below is due to Spahn and Zeilberger,
*Counting Permutations Where The Difference Between Entries Located r Places
Apart Can never be s*, ECA 3:2 (2023), S2R10, pages 4--6 of the authors'
version: https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/permsV2.pdf .
We reproduce its short counting proof to make the argument self-contained.
The conjectured order-eight recurrence is unnecessary.

The live author page added on August 14, 2026 a claim of general holonomicity
by Jaideep Sai Padhi. His August 2026 note gives no asymptotic expansion and
does not identify/prove the particular guessed order-eight operator:
https://github.com/jaideepsaipadhi/restricted-permutations-holonomicity .
This updates the older 2023 challenge status and must be acknowledged.

## 1. Exact inclusion--exclusion and its uniform tail

For a permutation pi let X count the n-r forbidden equalities. Select j of
these equalities. Their position graph is a union of c non-singleton directed
paths; a path with i vertices uses i-1 selected equalities. Let alpha_i be the
number of such paths, for i>=2, and write

    c=sum alpha_i, j=sum(i-1)alpha_i, D=j-c=sum(i-2)alpha_i.

There are n-j-c isolated vertices. Let C_r(n;alpha) be the number of ways to
select the position paths with this profile from the r arithmetic-progression
chains in [n]. The value paths have the same profile in the s chains. Matching
paths of equal length gives prod alpha_i! choices, and matching the isolated
vertices gives (n-j-c)! choices. Therefore

    a_{r,s}(n)/n! =
      sum_alpha (-1)^j C_r(n;alpha) C_s(n;alpha)
                 prod alpha_i! / (n)_{j+c}.                       (1)

Here (n)_b is falling factorial; profiles with j+c>n are absent.

For a fixed j-edge selection with c components there are at most n^c
admissible value assignments to its j+c vertices (choose the first value on
each path), and every injective assignment has probability 1/(n)_{j+c}.
Consequently, for 2j<=n/2,

    E binom(X,j) <= binom(n-r,j) max_{c<=j} n^c/(n)_{j+c}
                 <= exp(C j^2/n)/j!,                              (2)

with an absolute C, since n^{j+c}/(n)_{j+c} is bounded by that exponential.
Bonferroni gives an error at most E binom(X,J+1) when (1) is truncated at
j<=J. For any fixed K, choose J asymptotic to
2(K+3) log n/log log n. Then this error is O_K(n^{-K-2}).
No alternating-series convergence assertion is being made.

## 2. The stable long-chain coefficient

Introduce finitely many formal marks x_i, i>=2, of weighted degree i-1.
Let F_N be the tiling polynomial of a chain of N vertices into intervals;
singletons have weight 1 and an interval of i vertices has weight x_i.
Then

    [x^alpha] F_N = (N-j)_c / prod alpha_i!                       (3)

whenever N>=j+c. This follows by ordering the N-j tiles.

Define the formal solution lambda=1+w by

    w=phi(w), phi(w)=sum_{i>=2} x_i (1+w)^{1-i},
    C=1/(1-phi'(w)).

Formal Lagrange inversion, equivalently its residue form, gives

    [x^alpha] C lambda^N = (N-j)_c / prod alpha_i!.                (4)

For clarity, the residue identity is
  H(w)/(1-phi'(w)) = sum_{a>=0} (1/a!) (d/du)^a[H(u)phi(u)^a]_{u=0};
for H(u)=(1+u)^N the coefficient of x^alpha is the right side of (4).
Thus F_N and C lambda^N agree through weighted degree J whenever N>=2J.
If the r chains all have length >=2J, multiplication yields

    C_r(n;alpha)=[x^alpha] C^r lambda^n  (j<=J).                 (5)

In particular this depends only on n and r, not on the individual lengths.
For fixed r, their lengths floor(n/r) or ceil(n/r) satisfy this condition
for the J chosen in Section 1. The analogous assertion holds for s.

The following finite polynomial formula is useful for computation. For
0<=b_i<=alpha_i put h=sum b_i. Expanding C^{r-1} as a geometric-binomial
series and then using (4) gives

 C_r(n;alpha)=
 sum_{b<=alpha} (-1)^h (r-1)^{overline h}
   prod[(i-1)^{b_i}/(b_i! (alpha_i-b_i)!)]
   (n-j-h)_{c-h}.                                               (6)

The rising factorial with base 0 is 1 at h=0 and 0 at positive h.
Formula (6) is used only in its stable range. Its degree in n is c.

## 3. Complete algebraic expansion with an actual remainder

For every fixed r,s,K there are rational polynomials d_l(r,s), symmetric in
r,s, such that

 a_{r,s}(n)/n! = exp(-1) [sum_{l=0}^K d_l(r,s)n^{-l}
                                      +O_{r,s,K}(n^{-K-1})].     (7)

All residue classes of n have the SAME expansion.

Here are details justifying the termwise procedure. There are at most
n^c/prod alpha_i! placements of a given path profile on either side: label
the paths of each size, choose their starts, then forget the labels.
For j<=J, (1) in absolute value is at most

    exp(C J^2/n) n^{-D}/prod alpha_i!.                            (8)

Summing over the dimer count alpha_2 gives a factor e. Summing the remaining
profiles of defect D is encoded by

    exp(sum_{d>=1} u^d)=exp(u/(1-u)).

Its coefficients are nonnegative and its Taylor remainder at u=1/n shows
that the total of profiles D>K in (8) is O_K(n^{-K-1}).

For D<=K set alpha_2=k. All other alpha_i range over a finite set of
partitions of D, and c=k+L, j=c+D, where L=sum_{i>=3}alpha_i is fixed.
In (6), after factoring n^c/prod alpha_i!, the terms with given h have
prefactor

    (-1)^h (r-1)^{overline h} e_h n^{-h},
    e_h=[t^h](1+t)^k prod_{i>=3}(1+(i-1)t)^{alpha_i}.

Since e_h is an elementary symmetric function of weights whose sum is j,
e_h<=j^h/h!. Also (r-1)^{overline h}/h! is polynomially bounded in h
(and is zero for h>0 when r=1). Thus the h>K tail is bounded by a constant
times (j/n)^{K+1}, with a harmless fixed polynomial factor, uniformly for
j<=J and n sufficiently large.

For retained h, expand the normalized falling factorials and reciprocal
falling factorial by

 log[(n-A)_B/n^B] =
       -sum_{p>=1} n^{-p}/p sum_{v=0}^{B-1}(A+v)^p.              (9)

For the reciprocal denominator use the opposite sign with A=0,B=j+c.
Here A,B=O(j), so Taylor's theorem through any fixed order gives a remainder
bounded by n^{-K-1} times a fixed polynomial in j, times exp(C j^2/n).
The last factor is bounded for j<=J. Hence every error, after including
the leading profile factor n^{-D}/prod alpha_i!, is summable uniformly
in k, since sum (k+1)^M/k! is finite for every fixed M.
This proves an O(n^{-K-1}) integrated error without logarithmic losses.

The retained coefficients are polynomials in k divided by k!, multiplied by
(-1)^k and a rational factor. Extending k to infinity has a factorially small
error, by the same J cutoff. Finally

    sum_{k>=0} (-1)^k k^v/k! = exp(-1) T_v(-1),                 (10)

where T_v is the Touchard polynomial, an integer polynomial. This proves (7),
rationality, the finite algorithm, and the absence of parity at every
algebraic order. The coefficient degrees in r,s are finite because h is
bounded at each order.

## 4. Explicit coefficients

The supplied checker implements only (6), (9), and (10). It gives

 d0=1,
 d1=r+s-1,
 d2=(r^2-r+s^2-s)/2,
 d3=(r+s-1)(r^2-4rs+4r+s^2+4s-6)/6.

For A189281:

 exp(1) a_{2,2}(n)/n! ~
 1+3/n+2/n^2+1/n^3+0/n^4+3/n^5+26/n^6+101/n^7
      +124/n^8-1409/n^9-13266/n^10+...

These are asymptotic coefficients, not a claimed convergent series.
The first three are the ones currently stated in OEIS; no guessed recurrence
has entered their derivation.

## 5. A quantitative geometry-independence statement

The argument is not specific to equally spaced chains. Let P,Q be directed
path forests on n labelled vertices, with r and s components respectively,
and count bijections which send no directed edge of P to a directed edge of Q.
The same paired-tiling identity applies. If every component of both forests
has at least delta*n vertices, the expansion (7) holds with the SAME
d_l(r,s), uniformly over those component lengths.

There is a stronger exact comparison. For two such pairs of forests with
the same n,r,s, take J=floor(gamma*n), with
0<gamma<min(delta/2,1/4). Their inclusion--exclusion sums through J agree
term for term by (5). Formula (2), with its elementary product estimate
now bounded by exp(C_gamma*n), gives

  |probability(first pair)-probability(second pair)|
       <= exp(-gamma*n*log n + O_{gamma}(n)).                    (11)

Thus dependence on the component lengths is smaller than every fixed
exponential in n. This does not identify a canonical full flat sector for
the single sequence, but precisely quantifies where the seam geometry can
first matter. In particular there is no parity-dependent algebraic
coefficient for a_{2,2}.

## 6. All-orders inversion and the discrete threshold

For a fixed K define the explicit smooth model

  f_K(x)=Gamma(x+1)*exp(-1)*D_K(x),
  D_K(x)=sum_{l=0}^K d_l(r,s)x^{-l}.

It is positive and strictly increasing on a sufficiently large real tail.
Let x_K(y) be its inverse there. The expansion (7) and the mean-value theorem,
using (log f_K)'(x)~log x, show that the eventual discrete threshold

  N(y)=min{n:a_{r,s}(n)>=y}

satisfies, for a constant C_{r,s,K} and sufficiently large y,

  ceil(x_K(y)-epsilon_K(y)) <= N(y)
                          <= ceil(x_K(y)+epsilon_K(y)),
  epsilon_K(y)=C_{r,s,K} x_K(y)^(-K-1)/log x_K(y).                (12)

The constant can be enlarged to make all endpoint inequalities strict
where necessary. Eventual monotonicity of the original integer counts follows
from (7): a(n+1)/a(n)~n+1. Formula (12) gives an exact rounding rule whenever
the model root stays farther than epsilon_K from the nearest integer.
No arbitrary interpolation of the integer sequence is being selected.

For computation, take the exact gamma core X=X(y) defined by

    log Gamma(X+1)-1=log y,

and write q(X)~log(sum_l d_l X^{-l}), psi(X+1)=(log Gamma(X+1))'.
Formal Lagrange reversion in the logarithmic ordinate gives

 x(y) ~ X + sum_{k>=1} (-1)^k/k!
       [(1/psi(X+1)) d/dX]^{k-1}
       [q(X)^k/psi(X+1)].                                      (13)

At every fixed order, truncating this formula is justified by Taylor's
theorem for the explicit smooth f_K, with the error in (12) made arbitrarily
small by increasing K. The compatible inverse expansion is unique to all
algebraic orders even though different flat interpolations could exist.
The gamma core itself starts at log(e*y)/W(log(e*y)/e), with the usual
Stirling corrections; the repository already develops that inversion tool.

For A189281 one has q(X)=3/X-5/(2X^2)+4/X^3+O(X^-4). Retaining psi exactly,

 x(y)=X-3/(X psi)+5/(2X^2 psi)-4/(X^3 psi)
           -9/(X^3 psi^2)-9 psi'/(2X^2 psi^3)
           +O(X^-4/log X),                                    (14)

where psi=psi(X+1), psi'=psi_1(X+1). This is a finite-order smooth-model
expansion; (12) transfers it to integer-threshold information with the
appropriate error, rather than silently identifying it with an analytic
inverse of the discrete sequence.

## 7. Remaining transseries scope

The result is a complete algebraic factorial expansion, its compatible
inverse expansion, and the quantitative flat geometry bound (11).
It does not yet identify all intrinsic exponentially small sectors of
the sequence or their Stokes constants. No guessed recurrence or
unverified global holonomicity assertion is needed for any stated result.
