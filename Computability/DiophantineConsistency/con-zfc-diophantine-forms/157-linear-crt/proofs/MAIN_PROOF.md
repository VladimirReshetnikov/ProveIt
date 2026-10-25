# Affine beta spacing and arithmetic sign recovery

Independent mathematical audit for the new direct C222 construction.
Prepared 25 October 2026. This is an ordinary proof, not a newly compiled
proof-assistant theorem. The exact source compiler must still bind the
changed rows and retain the full signed Pell-orientation and frame interface.

## 1. Changes and retained interface

Start from the incoming `ConZFC_Factorial_Free_Binomial_CRT_2026-10-25`
arithmetic source. Keep all local C222, beta endpoint, common-remainder,
semantic-anchor and eighteen power-request equations. Set

    t = 16 + 4d^2,
    F = t^t,
    R = F,
    C = 2c,
    H = 2 + 4(C+A_1+...+A_8),
    y = F(2v+1).

Here C and A_j denote ACTUAL representatives; an old stored coordinate can
be their value minus one. The changes to R, C and H must be applied to those
actual values. Remove the dedicated odd-square restriction on q. The
retained equations include

    B h_B = C + F + 1,
    x = F + 1 + (y+1)u_0,
    x = 1 + [1+(t+1)y]u_t,

and requested exact powers

    N = B^x,  q = (BH)^x,  M = q^x,  D_y = q^(y+1),

together with all binomial numerator/denominator powers. These power
displays describe semantics to be recovered, not premises asserted in
place of the polynomial rows.

The full fourteen-pair orientation pool is retained. Its signed-frame and
semantic-anchor proof gives every principal pair its canonical signed-index
Pell interpretation BEFORE any arithmetic sign is known. The source frame
must contain the base t (reused as a requested index), the actual BH wire and every changed base,
index and output atom. Its conclusions are |atom|<W, W>=258 and |A|>W^W.
No sign of x, y, B, q or a representative is required by that proof.

The signed canonical power lemma says that for an integer requested base n
with |n|>=2, its polynomial request forces k>=0 and m=n^k. At n=+/-1 it
forces m=(+/-1)^k for either sign of k. No such assertion is used at n=0.
This is exactly the retained unbounded Pell lemma, valid also for negative
centers and negative bases.

## 2. Acyclic sign bootstrap

The F request has known positive base and index t>=16. Thus

    F=t^t>=16^16=2^64>2^32.

The horizon t=16+4d^2 is divisible by four, so F is even. Since C=2c, the integer C+F+1 is odd, including when C is
negative. The literal equation B h_B=C+F+1 consequently makes B and h_B
odd and nonzero. In particular this does not assume C>=0.

The definition of H gives H=2 modulo 4 for ALL signed representatives.
Therefore |H|>=2 and |BH|>=2, without any sign premise on the columns.
The canonical request at base BH now gives

    x>=0,  q=(BH)^x.

The affine beta definition gives y!=0 and |y|>=F. Put
L=1+(t+1)y. Then

    |L| >= (t+1)|y|-1 >= (t+1)F-1 > 1.

If x=0, the last endpoint would give L u_t=-1, impossible. Hence x>=1
and Q=|q|=|BH|^x>=2.

At this stage the retained request with base q and exponent y+1 is already
usable: its base has absolute value at least two. The signed power lemma
therefore forces y+1>=0. A negative y would satisfy y<=-F<-1, a
contradiction. Thus

    y>=F>0.

This is the essential saving: an existing power request recovers the sign
of the cofinal beta spacing, so its odd multiplier need not be squared.

If u_0<=-1, the first endpoint would give

    x <= F+1-(y+1)=F-y<=0,

contrary to x>=1. Thus u_0>=0 and x>=F+1>=3. In the last endpoint
u_t<=0 would give x<=1, so u_t>=1 and

    x>=2+(t+1)y>=2+(t+1)F.                         (A)

It follows that Q>=2^x and |q+1|>=Q-1>=2. Every actual representative
C,A_1,...,A_8 is an exponent in a request at base q+1. Applying the
signed power lemma now gives all nine representatives nonnegative. The
derived label is also nonnegative by its analogous request; its inherited
anchor excludes zero where required. In particular H>=2 is now positive.

All q-based requested powers are now genuine. The sign of q can still be
negative, because B has not yet been authenticated. No earlier step used
positive q or a positive B.

## 3. First binomial digit in a signed radix

Let n=F+t and C_j=binom(n,j). For 0<=j<=t,

    C_j <= (F+t)^t <= (F^2+F)^t <= 2^[t(F-1)].

The first inequality uses the elementary binomial bound (also valid at
j=0); the second uses F>=t and F>=2. The last uses
F^2+F<=2^(F-1) for F>=7. From (A),

    2^[t(F-1)] / Q <= 2^(-F-t-2),

so C_max/(Q-1)<1/32 and C_t<Q/32.

The binomial theorem is a polynomial identity also when q<0. Its signed
low part

    r_0=sum_{j=0}^{t-1} C_j q^j

satisfies |r_0|<Q^t/32 and is congruent to (q+1)^n modulo q^t.

The common-remainder rows are retained. Write a denominator D=q^k,
ratio a=M/D and normalized remainder rho. Its exact row has the form
a U=M J+rho. Since a divides M and a U, it divides rho. Consequently
r=rho/a is an integer and U=D J+r. The common norm

    M^2=1+4 sum rho_i^2+alpha^2+beta^2+gamma(gamma+1)

gives |rho_i|<|M|/2, hence |r_i|<|D_i|/2, for either sign of D_i or M.
Every ratio is nonzero because q!=0. Congruent remainders r,r_0 with
those bounds must be equal: |r-r_0|<|D| and D divides the difference.

For the exact B digit this gives B=C_t modulo q. Put a=|BH|>=2.
Since x>=3 and H is now positive, |B|<=a<Q/2. Therefore

    |B-C_t| < Q/2+Q/32 < Q,

and the congruence yields the ordinary equality

    B=binom(F+t,t)>0.

In fact B>=2. As H>0, the self-radix equality now gives q=(BH)^x>0.
The B request has positive base at least two, so N=B^x>0. All signs
required by the inherited range compiler are now available.

## 4. Remaining digits and local arithmetic bounds

For every nonnegative ordinary representative a and every requested lower
digit index at most x,

    binom(a,j)<=max(1,a)^x<=H^x.

The new H dominates 2+sum of the nonnegative representatives, so the
inherited derived-label bound h_*<=H^ell, ell=2^22, still holds. Because
F>2^32>ell and x> (t+1)F, all required derived-label coefficients are
also at most H^x. As q=B^x H^x and B>=2,

    H^x/(q-1)<2/2^x<1/32.

Thus all ten other common remainders are recovered exactly by the same
argument. This invokes only LOWER bounds for H; replacing its old affine
definition by the larger positive majorant cannot invalidate the estimates.

The unchanged local C222 ledger has

    0<=L_local < (2+t+x+y+F)^E,  E=2^23.

From y>=F, (A), t>=16 and F>2^32, one has 2+t+x+y+F<2x and x>2^32.
The elementary dyadic estimate E log_2(2x)<x then yields

    0<=L_local<2^x.

For an integer-only verification of this estimate, take k with
2^k<=x<2^(k+1), k>=32. Then log_2(2x)<k+2 and
2^23(k+2)<2^k<=x; the middle inequality holds at k=32 and persists when
k increases because the right side doubles.

The strict local beta quotient ranges and every other inherited range
budget remain valid. The derived label, being a polynomial of the actual
columns, reduces to the same bounded local value at each selected prime.

## 5. Why the smaller binomial radius suffices

Let Lambda_t=lcm(1,...,t). We use Lambda_t<=4^(t-1). A short proof is as
follows. Put m=ceil(t/2). For each prime p, the p-adic exponent in
Lambda_t exceeds that in Lambda_m by at most one. If it exceeds it, the
largest power p^e<=t lies above m; its contribution to the factorial
valuation formula for binom(t,floor(t/2)) is one. All other contributions
are nonnegative. Thus

    Lambda_t divides Lambda_m * binom(t,floor(t/2)).

Strong induction, binom(t,floor(t/2))<=2^t for even t, and the sharper
bound <=2^(t-1) for odd t (two equal middle coefficients) prove the claim.
The base t=1 is immediate.

At t>=16,

    R=F=t^t>=16^t>16^(t-1)>=Lambda_t^2.

The incoming general binomial-CRT theorem therefore applies directly with
R=F. Its two separate conclusions are both needed:

* Each row i in 1,...,t has a prime-power selector p^e||B with p^e>t
  and p^e dividing F+i.
* Every full prime power p^e||B divides F+i for at least one row i.

Together with B|C+F+1, the range binomials modulo N=B^x, and the local
value bound below 2^x, these conclusions recover every genuine local row
and justify the reverse CRT construction at every prime of B.

The label weights remain W_j=1+jF. The old sufficient hypothesis
F>(t+1)^t is no longer true at F=t^t, so it must NOT be reused. The
following sharper proof replaces it.

Suppose the product-balance identity has at most t nonunit factors on its
conclusion side and at most 2t+1 on its premise side (including the target
weight). All labels lie in 1,...,t after unit factors have been omitted.
If the factor counts differ, let r be their minimum; r<=t. The larger side
is at least (F+1)^(r+1) and the smaller side at most
(1+tF)^r<=t^r(F+1)^r. This contradicts F+1=t^t+1>t^r. Therefore the
factor counts agree at some m<=t.

Replace F by an indeterminate z in both products. For 0<=k<=m, every
coefficient is a positive integer, bounded above by

    binom(m,k)t^k <= m^(m-k)t^k <= t^m <= F.

The first coefficient bound counts the products of k labels; the middle
bound uses binom(m,k)=binom(m,m-k)<=m^(m-k). Since BOTH coefficients
are positive, their difference has absolute value at most t^m-1<F,
even in the boundary case m=t. The constant coefficients are both one.
A nonzero difference polynomial with all coefficients of absolute value
less than F cannot vanish at F: divide by F to the power of its lowest
nonzero degree and reduce modulo F. This proves an identity in Z[z].
Distinct labels give distinct irreducible linear factors 1+jz over Q, so
unique factorization recovers every required positive-label multiplicity.
The proof works with F=t^t exactly and needs no factorial authenticity or
pairwise coprimality of the evaluated weights.

If y=F, the initial beta remainder is zero while the terminal remainder is
one. The decoded positive-weight local updates propagate a zero initial
accumulator to zero at every row, contradicting the terminal value. Thus
every actual solution has y>F. Its first endpoint now has intended initial
accumulator F+1, its last endpoint has final accumulator one, and the local
updates give the label-product balance. The retained single-conclusion Horn
flow lemma extracts a finite C222 refutation, and the named C222/ZF/ZFC
calibration extracts a finite syntactic ZFC refutation.

## 6. Constructive completeness with the affine multiplier

Start from a finite calibrated refutation, choose a sufficiently large
horizon t=16+4d^2, and set F=t^t. Build the finite pending-multiset
accumulator path with weights 1+jF, padded by truth to exactly t rows.

Let O be the odd part of t!. Choose an arbitrarily large positive odd
multiple w of O and put

    y=Fw,  v=(w-1)/2.

This is the new affine beta equation. The valuation

    v_2(F)=t v_2(t)>=2t>v_2(t!)

shows t! divides y, and y is even. By taking w large, arrange y>F and
bound every pending accumulator by y. The beta moduli 1+(i+1)y are
pairwise coprime: a common prime would divide a nonzero index difference
at most t, hence would divide y, contradicting its divisibility into
1+(i+1)y. All beta moduli are odd. Choose a sufficiently large positive
beta code x in its CRT class. It can still be chosen even if retaining
that harmless old convention is convenient, but the new proof does not
need its parity. The genuine endpoint and local quotients have the same
strict ranges as before.

Set B=binom(F+t,t), N=B^x and apply the generalized binomial CRT compiler.
It gives independent representative classes modulo N^2. The binomial B is
odd: v_2(F)>floor(log_2 t), so for every 1<=i<=t,

    v_2(F+i)=v_2(i).

Summing these valuations and subtracting v_2(t!) gives v_2(B)=0. Thus N^2
is odd, and adding N^2 to any representative changes its parity while
preserving all required CRT congruences.

Choose C even, which supplies c=C/2. Independently choose the dominant
syntax representative a odd in [2N^2,4N^2), and b even. All the other
ordinary representatives can be positive and at most 2N^2; C is one of
those independently adjustable columns. The inherited constructor has
h_*=1+a+b modulo 2 and h_*>=2a^2. Hence h_* is even and dominates all
other requested indices exactly as in the source proof. Changing the
binomial upper index from F^2+t to F+t only lowers that front index.

Now define H=2+4(C+sum A_j)>0 and q=(BH)^x>0. These choices occur AFTER
the representative CRT, so there is no circular modulus choice. In fact
q is even here, which is permitted: no retained CRT, Pell or digit lemma
requires q to be odd. One still has N|q since q=N H^x, the divisibility
used by the binomial range encoding.

The true low remainders are less than their denominators divided by 32.
Their normalized values rho_i are less than M/32, M=q^x. Thus

    4 sum_{i=1}^{11} rho_i^2 < (44/1024)M^2 < M^2,

and the nonnegative integer gap M^2-1-4 sum rho_i^2 has a representation
alpha^2+beta^2+gamma(gamma+1). This supplies the common norm. The
unchanged constructive simultaneous Pell frame and the even semantic
anchor supply all private power and comparison witnesses. In particular,
there is no new requested exponent. This constructs a zero of the new
raw arithmetic system.

## 7. Exact logical and artifact status

The two directions prove, by ordinary arithmetic formalizable in ZFC,

    exists an integer zero of the new raw system
      iff a finite calibrated C222 refutation exists
      iff a finite syntactic ZFC refutation exists.

The last step uses the identified inherited interfaces
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Exact integral
projection and sum-of-squares compilation preserve this equivalence.
Negating it gives the requested equivalence with Con(ZFC). It proves
neither consistency nor inconsistency and makes no global-minimality claim.

The new change is semantic, not a claim that every old zero survives
unchanged: it changes the binomial radius, the size function H and the beta
spacing. Completeness reconstructs witnesses from a finite refutation.
Finite coefficient and transformation audits are still needed to bind the
selected output polynomial to these exact source edits. They do not replace
the unbounded proof above, and no new end-to-end Lean/Rocq build is asserted.

