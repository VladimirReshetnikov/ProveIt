# A diagonal growth certificate and a residue-class sign bootstrap

This note gives the ordinary unbounded proof for the new arithmetic source.
All variables in the final equations are unrestricted integers. The finite
compiler and coefficient checks do not replace the argument below.

The immediate parent is `ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip`,
read from ProveIt commit `536c08e7913e59bd42e8fca66e89944c920884ad`. Its
complete original package is retained under `baseline/`. We use its finite
C222 calculus, common signed Pell frame, eighteen exact-power requests,
eleven normalized binomial digits, range and local-polynomial ledgers,
prime-power range lemma, and C222/ZF/ZFC refutation calibration. We change
the arithmetic source and prove its soundness and completeness again.

The signed-power lemma and absolute-value remainder argument are also
explicitly used in the concurrent Shared Factorial Error package. The
new ingredients here are the following compatible combination:

* a diagonal growth value F=t^t, which also serves as the binomial shift;
* the affine residue class q=6z+3, ensuring that q and q+1 are both
  nonunit, nonzero integers before signs are known;
* the existing power request at exponent y+1, which recovers the sign of
  a linear odd multiplier y=F(2v+1).

## 1. The literal changed source

Use the semantic values

    t = 16 + 2h0^2,
    F = t^t,
    R = F,
    y = F(2v+1),
    H = 3 + 6(a1+...+a9),
    q = 6z+3,
    B = binom(R+t,t), N=B^x, q=(BH)^x.

Here a1,...,a9 are the nine actual CRT representatives. The last line
states the intended interpretation of the retained graph, not additional
primitive operations in the final polynomial. The Pell graph certifies
all variable powers. The binomial graph certifies B. At the start of
soundness B, q, x and the representatives may be signed.

In the raw compiler coordinates t=t0+16 and ai=stored_ai+1. Thus the new
rows, before final translation, are exactly

    t0 - 2h0^2 = 0,
    growth_base - t0 - 16 = 0,
    q - 6z - 3 = 0,
    self_base - B(57+6*sum(stored_ai)) = 0,
    y - F - 2Fv = 0.

The old beta-square multiplier row is deleted. Its private multiplier
coordinate becomes unused. The old binomial-shift square row R-F^2=0
is deleted and R is replaced globally by F in every residual, including
the exact frame. Every retained power base, exponent and output therefore
remains represented by its actual value in the frame.

`source_delta.json` records all literal row changes and the global alias.
The source remains quadratic. The old F=t! interpretation is never used.

## 2. One diagonal power suffices for both arithmetic jobs

### 2.1 Recovering proof-label multiplicities at F=t^t

Suppose all labels lie in [0,t] and there are t single-conclusion Horn
rows, with at most two premises per row. Put W_j=1+jF, so W_0=1. The
positive accumulator identity is

    product W_conclusions = (1+F) product W_premises.

Delete unit factors. The left nonunit count is at most t. If the two
counts differ, their minimum d is at most t. The larger-count product
is at least (F+1)^(d+1), whereas the smaller is at most

    (1+tF)^d <= t^d(F+1)^d.

This contradicts F+1=t^t+1>t^d. Hence both sides have the same number
m<=t of nonunit factors. For a product of m factors 1+jZ, 1<=j<=t,
every coefficient in degrees 0,...,m is a positive integer and

    coefficient at degree k <= binom(m,k)t^k
                              <= binom(t,k)t^k <= t^t=F.

The last bound follows from binom(t,k)=binom(t,t-k)<=t^(t-k). At each
degree both compared coefficients are positive and at most F. Their
difference therefore has absolute value strictly below F. A nonzero
integer polynomial with all coefficient magnitudes <F cannot vanish at
F: divide by its lowest nonzero power and reduce modulo F. The evaluated
product identity is consequently an identity in Z[Z]. Unique
factorization of the distinct rational linear factors 1+jZ recovers
the exact label multiplicities. The equality cases at k=t-1 and k=t
cause no gap; positivity on both sides supplies the strict difference
bound. This improves the parent's sufficient choice [2(t+1)]^t.

The inherited one-conclusion flow argument now gives derivability of
falsity. It applies to cyclic supplied multisets and repeated premises:
sum the multiplicity balance over the labels outside the finite closure
of truth. Each rule contributes at most zero, whereas the desired
falsity balance would contribute one.

### 2.2 The binomial shift may be F itself

Let Lambda_t=lcm(1,...,t). Since t is even, there are at most t/2 primes
not exceeding t: prime 2 and the t/2-1 odd numbers 3,...,t-1. Writing
Lambda_t as the product of the maximal power <=t of each such prime gives

    Lambda_t^2 <= t^(2*pi(t)) <= t^t=F.

Thus the parent's sharpened binomial selector condition R>=Lambda_t^2
holds with R=F; no square of F is needed. This elementary estimate is
uniform and uses neither prime distribution nor a growth asymptotic.

For clarity, the required selector theorem is proved next. Let t>=1,
R>=Lambda_t^2 and B=binom(R+t,t). For every i in [1,t], there is a prime
p such that the full p-primary factor p^e of B divides R+i and p^e>t.
If every v_p(R+i) were <=2 floor(log_p t), then R+i would divide
Lambda_t^2, contradicting R+i>Lambda_t^2. Choose p with v=v_p(R+i)>2a,
where a=floor(log_p t). Since p^v>t, every other factor R+j has
v_p(R+j)=v_p(j-i). Therefore

    e=v_p(B)=v-v_p(t*binom(t-1,i-1)).

For every prime power p^j<=t, the Legendre-sum contribution to
v_p(t*binom(t-1,i-1)) is zero or one; above t it is zero. Hence this
valuation is between zero and a. Consequently v-a<=e<=v, so e>a,
p^e>t and p^e divides R+i.

Conversely, every full prime power p^e of B divides at least one R+i.
Indeed put v=max_i v_p(R+i). Legendre's formula for e is a sum of
zero-or-one interval-carry terms. Terms above level v vanish, giving
e<=v. This converse is essential when constructing CRT representatives
at all primes of B, including primes not selected for an individual row.

These two facts are exactly the soundness/completeness interface of the
inherited binomial CRT compiler. They do not require coprimality among
the consecutive R+i, nor factorial authenticity.

## 3. Signed power and remainder interfaces

The unchanged square frame and semantic anchor give W>=258,
|A|>W^W, and absolute bounds below W on every actual power base n,
index k and output m. The fourteen-pair orientation pool is retained in
full. Its ordinary proof authenticates the canonical signed-index Pell
pairs before front signs, factoriality or binomial meanings are used.

For a nonzero integer n with |n|>=2, set T=2An-n^2-1. The retained power
row is

    X_k(A)+(n-A)Y_k(A) = m mod T.

The frame implies |T|>W^W+W. At k>=0 the left side is congruent to n^k
and its bounded difference from m forces m=n^k. At k=-j<0 it gives
mn^j=1 mod T. The absolute error is <|T|, forcing the impossible integer
identity mn^j=1. Thus k>=0 and m=n^k. This statement treats negative
bases as well as positive bases.

The common remainder norm has the form

    M^2 = 1+4 sum(R_i^2)+a^2+b^2+c(c+1).

For all integer c, c(c+1)>=0. Hence M!=0 and |R_i|<|M|/2. If L_i v_i=M
and v_i U_i=M Q_i+R_i, then L_i,v_i are nonzero, v_i divides R_i, and
r_i=R_i/v_i is an integer with

    U_i=L_i Q_i+r_i, |r_i|<|L_i|/2.

A prescribed congruent signed remainder of absolute value <|L_i|/2
is unique. No positivity of L_i, M or r_i is required.

## 4. Acyclic sign recovery

1. The positive index t>=16 and base t>=16 give F=t^t>=2^64. This
   is the first authenticated power and uses no later signs.

2. The literal residue class q=6z+3 gives |q|>=3 and |q+1|>=2 for
   every integer z. Both bases are nonzero nonunits. Requests at base
   q+1 therefore make all nine actual representatives nonnegative.
   The requests at base q make x>=0 and y+1>=0, and authenticate all
   denominator powers. Thus H=3+6 sum(ai)>=3.

3. Since y=F(2v+1), y is a nonzero multiple of F. The preceding
   y>=-1 and F>=2 force y>=F. The sign of the odd multiplier is a
   consequence of an existing power request; no square multiplier or
   separate nonnegativity graph is needed.

4. The raw index row is B*index_quotient=C0+F+1. Its right side is
   positive, so B!=0. Consequently |BH|>=3. The self-radix request
   gives q=(BH)^x. Since q!=1, x>=1. In the first beta endpoint

       x=F+1+(y+1)u0,

   u0<=-1 would imply x<=F-y<=0. Hence u0>=0 and x>=F+1. The last
   endpoint x=1+(1+(t+1)y)ut then gives ut>=1 and

       x>=2+(t+1)y>=2+(t+1)F.

5. Write Q=|q| and b=|B|. Now

       Q=(bH)^x >= 2^x,   Q>=9b^2,   b<=Q/9.

   No positivity of B or q has yet been assumed. All four low-digit
   denominators are nonzero signed powers and their exponents t,t+1,
   y+1,x are nonnegative and at most x. Their exact ratios to M=q^x
   are therefore valid integer normalizations.

This order avoids every q=0, q=1, q=-1 and q=-2 issue by the original
affine class itself. It also avoids appealing to a positive factorial
error, which the new source does not contain.

## 5. The first binomial digit and the sign of q

Put C_j=binom(F+t,j). For 0<=j<=t,

    C_j<=(F+1)^t=:Vstar.

This standard elementary bound follows by Pascal induction, with the
last coefficient bounded by product_(i=1)^t(1+F/i)<=(F+1)^t. Vstar is
proof notation, not an extra register. For F>=3 one has F+1<=2^(F-1).
Together with x>=2+(t+1)F and Q>=2^x, this gives

    Vstar/Q <= 2^(-F-t-2),    Vstar/(Q-1)<1/32.

The exact numerator is U=(q+1)^(F+t). Its normalized digit row becomes

    U=q^t(B+q*eta)+r,     |r|<Q^t/2.

For either sign of q, the binomial theorem supplies

    r0=sum_(j=0)^(t-1) C_j q^j,
    |r0|<Vstar*Q^t/(Q-1)<Q^t/32.

Signed remainder uniqueness gives r=r0. Subtraction and division by
q^t yield B=C_t mod q. Since b<=Q/9 and C_t<=Vstar<Q/32,
|B-C_t|<Q; the congruence is therefore equality. Thus

    B=binom(F+t,t)>0,    q=(BH)^x>0,    N=B^x>0.

Since t>=2, B>F+1. The retained divisibility B|(C0+F+1) therefore
excludes C0=0, and the already nonnegative actual index representative
satisfies C0>=1, as required by the original row-index extraction.

Every remaining power now has its ordinary positive-base interpretation.
The negative-radix branch was fully considered before being excluded.

## 6. Remaining ranges, row extraction, and the endpoint y=F

The inherited local polynomial ledger uses exponent E=2^23. For
Rmaj=2+t+x+y+F, the established endpoint and y>=F give Rmaj<2x, since

    x-(2+t+y+F) >= t(y-1)-F >= (t-1)F-t>0.

Also x>=F+1>=2^64+1. The parent's uniform estimate
(2x)^E<2^x, valid already for x>=2^32, applies with ample room. The
derived-label degree ledger ell=2^22 satisfies ell(t+1)<x.
The new H is at least the parent's positive representative majorant,
so the ten remaining genuine low binomial remainders have exactly the
same <1/32 relative margin. Their normalized congruences therefore
restore the required range divisibilities by N.

Apply Section 2.2 to R=F. For each row i, a prime power p^e in B with
p^e>t identifies its index uniquely. The inherited binomial range
lemma at precision x and the bound 0<=L<2^x<=p^(ex) turn the local
congruence into L=0. Thus all local Horn/accumulator rows are genuine.
Conversely every prime of B has a compatible row, closing the reverse
CRT construction at all primes.

The standalone arithmetic permits y=F. It must still be excluded before
asserting a positive initial accumulator. If y=F, the first endpoint
forces the initial proper beta remainder to be zero, while the final
endpoint gives final remainder one because its modulus exceeds one.
The recovered local equations are

    S_(i+1) W_(conclusion_i) = S_i W_(premise1_i) W_(premise2_i).

All W_j are positive. A zero initial state therefore forces every state
to be zero, contradicting the final state one. Hence y>F at every zero.
The first proper remainder is now F+1, the last is one, and induction
makes the accumulator path positive. Section 2.1 recovers exact label
balance and the calibrated C222 refutation. This proves soundness.

## 7. Constructive completeness

Start with a finite C222 refutation and expand it to a finite proof
tree. Choose h0 sufficiently large so that the even horizon
t=16+2h0^2 exceeds the finite tree, every parameter and every label
needed by the inherited padding. Pad with truth to exactly t rows.
Let F=t^t and form the finite positive pending-multiset accumulator path
using weights 1+jF.

Let O be the odd part of t!. Choose an arbitrarily large odd multiple
u=O(2m+1), and put y=Fu and v=(u-1)/2. Because t is even,
v_2(F)=t*v_2(t)>=t>v_2(t!). Thus t! divides y. Choose m large enough
that y>F and y exceeds every accumulator. The moduli 1+(i+1)y are
pairwise coprime and odd; CRT gives a positive beta code x, which can
be increased arbitrarily in its progression. No parity condition on x
is imposed by this construction.

Set B=binom(F+t,t), N=B^x. The selector theorem of Section 2.2 assigns
a compatible genuine row to every prime power in B. The inherited
precision-N^2 CRT construction gives the nine representatives and all
range certificates. Its cofinal lifts preserve nonnegativity and the
required dominant semantic anchor.

Moreover B is odd: for i<=t, v_2(i)<t<=v_2(F), so
v_2(F+i)=v_2(i). The product formula for B then has total 2-adic
valuation zero. Hence N^2 is odd. As in the parent, shifting a
representative by N^2 permits the parity choices making the dominant
semantic anchor even. The parent needs only these existing lifts; no
new congruence on their total sum is necessary.

Now H=3+6 sum(ai) is automatically positive, odd and divisible by three.
Thus q=(BH)^x is positive, odd and divisible by three. Set z=(q-3)/6.
This is an integer, as required. The standard retained construction
supplies all genuine powers, Pell pairs, the common frame and anchor,
normalized remainders and ternary completion of the common norm. Their
same strict margins hold because H is larger than the former majorant.
The source has a zero. This proves completeness.

## 8. Calibration and exact finite polynomials

The construction uses the numerical C222 calculus directly. Its inherited
ordinary logical interfaces are

    KEndpoint.c222_iff_zf_refutation
    ConstructibleChoice.zf_refutation_iff_zfc_refutation.

Together with the soundness and completeness just proved, they give
in ZFC an equivalence between a zero of the new source and a finite
syntactic ZFC refutation. The finite compiler first factors Horn rows,
then applies recorded integral monic eliminations, translations and
reversible affine coordinate/row operations. Each elimination has an
explicit integer-polynomial restoration; private unused coordinates may
be restored to zero. These transformations preserve zero existence.

The emitted equations are P=sum_j R_j^2, with every residual R_j literally
specified and quadratic. Over the integers P=0 is equivalent to all
R_j=0. Therefore ZFC proves

    (no integer zero of P) <-> Con(ZFC).

`diagonal239/` has 239 variables and 175 residuals; `diagonal238/` has
238 variables and 174 residuals before any optional residual basis
improvement. Neither involves K215, Jones's universal polynomial, an
uncomputed coefficient tuple or a variable-exponent primitive in the
final polynomial. The argument proves an equivalence, not consistency
or inconsistency. It is ordinary mathematics formalizable in ZFC,
not a newly compiled end-to-end proof-assistant proof object.

