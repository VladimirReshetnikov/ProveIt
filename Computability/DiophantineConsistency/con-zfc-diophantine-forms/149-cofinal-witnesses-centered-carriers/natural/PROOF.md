# Positive centers, pooled digits, and cofinal descending beta bounds

## The theorem and exact domains

Every coordinate of every endpoint ranges independently over N={0,1,2,...}.
Each equation is the sum of the squares of all literal quadratic residuals in
its equation.json. The adjacent expanded_polynomial.json gives every collected
coefficient. No power, factorial, binomial, Pell sequence, floor or bounded
quantifier is a primitive of these finite quartics.

The first source change combines the retained shift-free descending factorial
certificate with the incoming positive deterministic Pell comparison center,
four equal-denominator low-digit budgets, and removal of a redundant factorial
output bound. Its source has325 variables and276 quadratic rows. A second NEW
change takes the even horizon t=2t0+4 and fixes the beta bound at y=V-1, where
V=(F²-1)^t is an existing power output. Its source has324 variables and276 rows.
The independently checked dimension endpoint has219 variables and171 rows.
The complete cofinal proof is also isolated in COFINAL_PROOF.md.

Relative to the explicitly retained ordinary C222/ZF/ZFC calibration, every
selected equation has a natural zero iff there is a finite syntactic ZFC
refutation. Thus ZFC proves each no-natural-zero sentence equivalent to Con(ZFC).
This is not a proof of consistency, an optimality claim, or a newly kernel-
checked end-to-end logical endpoint. The finite checkers prove literal algebra
and artifact binding; the unbounded arguments below and in retained proofs
establish arithmetic and logical equivalence.

## 1. The retained shift-free descending source

The source has t=t0+12 initially and natural F,n,B,r,s with

    n+1=F²,       V=BF+r,       B=r+s+1.

Its exact-power modulus row T_n+n²+1=2An rules out n=0 before interpreting any
power. Hence F>=2,n>=3. The shared frame and semantic Pell anchor recover

    V=n^t, N=B^x, q=(NS)^x,
    D_t=q^t, D_y=q^(y+1), D_x=q^x,
    S=1+C+Aa+Ab+Ac+Ad+AS+ASp+Au+Av.

There are13 nonanchor seeds and11 modular requests. The frame W contains all
base, exponent and output atoms and all modular tops, with offset15. The anchor
index J is the actual derived syntax-label sum; it is not replaced by a free
Pell norm. Its full principal, auxiliary and comparison norms are retained.
The two endpoint equations x=F+1+(y+1)u0 and
x=1+(1+(t+1)y)ut remain in every version.

The floor rows give V<B(F+1). Since n>=3,F>=2,t>=3,
V=n^t>=n²>F(F+1), and therefore B>F. Consequently

    V<B(F+1)<=B²<=N<=q.

Every binom(n,j),0<=j<=t, is at most n^t=V<q. Exact modular decoding gives
B=binom(n,t)>0, so n>=t and F=floor(n^t/binom(n,t)). For T=t! and
U=t(t-1)/2, this floor implies F>=T. Since T-1>U for t>=3,
n=F²-1>=(T+1)(T-1)>(T+1)U. The product inequality gives

    T <= n^t/binom(n,t)
      <= T*n/(n-U) = T+T*U/(n-U) < T+1.

Thus F=T. Conversely the same estimate at F=T constructs the floor witnesses.
All positivity and carry bounds precede the factorial identification.

For1<=i<=t put d_i=F²/i-1. These are integral, congruent to-1 modulo F,
and have no prime divisor<=t. A common prime divisor of d_i,d_j would divide
id_i-jd_j=j-i, which is impossible. They are pairwise coprime and their product
is B=binom(F²-1,t). The retained index row C+1=F²+Bq_C gives C≡i-1 modulo d_i.
Its quotient is natural: B>n=F²-1, so every positive representative of this
congruence class is at least n. This descending sign is explicitly retained.

## 2. Positive deterministic Pell comparison center

Write the cap principal pair (X,Y), auxiliary pair (U,Vc), comparison pair
(S_c,R_c), base A, and desired index H=J. The raw frame forces A>=2.
The unchanged merged cap row has

    Y=H+sum_i(Y_i-k_i)²+(A-1)Q,

so Y>=H>=2 BEFORE interpreting indices or powers. The last lower bound follows
from the literal nonnegative Cantor label polynomial, whose constant is at
least7. Replace the old free center congruence parameters by

    Vc=2Y²(e+1),   T=U²,
    Cc=A+(4Y+1-A)T,

with natural Cc-1; keep all three norms, S_c=X+Ug and R_c=H+4Yh.
Only the new square gate T is added; the old q4minus1,Bquotient and its product
gate disappear. This is the positive-center construction credited in
inherited/POSITIVE_CENTER_PROOF.md, applied to the descending source.

For soundness the auxiliary norm gives

    T-1=(A²-1)Vc²=4(A²-1)Y⁴(e+1)²,

and T>A. Set L=4Y+1-A. If L<0, then Cc=A+LT<=A-T<0, contrary to Cc>=1.
Thus L>=0,Cc>=A>=2. Also

    Cc-1=4YT-(A-1)(T-1),

which is divisible by4Y. Since positive, its quotient is at least1. Restore
the old parameters by d=(Cc-1)/(4Y)-1>=0, f=LU>=0 and e_old=2e+1>=0.
Restore the old product gate U f and double the old V-multiple product gate.
Every original full-index row is recovered before its index theorem is used.
These restorations are nonnegative ON the retained equations; they are not
misrepresented as unconditional orthant-positive monic substitutions.

For completeness the canonical pair has Y=Y_H(A),H>=2, so Y>=2A. The Pell
recurrence matrix is invertible modulo2Y². Its action on the finite state set
has a positive period returning(1,0), so choose a positive auxiliary Pell
index with Vc divisible by2Y² and let e=Vc/(2Y²)-1. Then L>0, Cc>A,
Cc≡A modulo U and Cc≡1 modulo4Y. Take comparison pair
S_c=X_H(Cc),R_c=Y_H(Cc). Polynomial base transfer gives S_c≡X modulo U;
Y_H(1)=H gives R_c≡H modulo4Y. Monotonicity gives S_c>=X,R_c>=H, so the
comparison quotients g,h are natural. These are fresh auxiliary choices, not
a claim that every old auxiliary tuple is preserved pointwise.

## 3. Four pooled low-digit bounds and a redundant output bound

The exact denominators form four groups:

- q^t: factorial binomial and encoded row index;
- q^(t+1): a,b,c,d and the derived label J;
- q^(y+1): the two pending-state columns;
- q^x: the two beta quotient columns.

Replace D=r_i+s_i+1 for every member of a group by one row

    D=sum_i r_i+s+1.

Soundness restores every old private slack by the polynomial
s_i=s+sum_(j!=i)r_j>=0. This restoration uses no powers, binomials or factorials.
The numerator/output equations, whose natural signs orient the Pell seeds,
are unchanged. Removing the old output row q=B+o+1 is separately justified:
after exact powers are recovered, Section1 already proves q>=N>=B²>B.
Thus o=q-B-1 is naturally restored BEFORE decoding the factorial binomial.
No factorial assumption is used to establish its own output bound.

For completeness use the source's canonical finite-refutation witnesses.
Every independent representative is<S; for j below a requested range digit
k<=x, its coefficient is<=S^x. The constructor ledger gives J<=S^ell with
ell=2^22 and ell(t+1)<x, so all needed coefficients for J are also<=S^x.
Factorial low coefficients are<=n^t=V<B²<=N. At most five members share a
level. Hence every coefficient sum is at most5S^x+N, which is<q=N^x S^x:
N>=4,x>=2 imply N^x-5>=N, and S^x>1. The coefficient sum is therefore at
most q-1. Its geometric low-digit expansion gives sum_i r_i<=q^k-1=D-1,
so the pooled slack is natural. This is a canonical-witness completeness
argument, not an assertion that all old arbitrary remainder tuples pool.

## 4. New even-horizon cofinal beta specialization

Make the exact finite substitution old_t0=2new_t0-8 in the preceding raw
source, so its semantic horizon is now t=2new_t0+4. Replace

    y=F+endpoint.r0+1

by y+1=V and delete endpoint.r0. The translation is NOT a natural bijection;
this section proves its new domain theorem. No nominal index, power request,
frame atom or source polynomial is omitted.

Before factoriality the unchanged power-modulus row gives F>=2,n>=3, while
x>=F+1 and natural y ensure all requested exponents t,x,y+1 are positive.
The cap and natural output incidences authenticate indices and recover the
six powers exactly as before, without needing y>=F+1 at that stage.
Now y=V-1=(F²-1)^t-1>=F+1. The final endpoint has ut>=1, hence
x>=2+(t+1)y>max(t+1,y+1). The common-root modulus Nq^x has every required
factor before the first binomial is decoded. Section1 then recovers F=t!.

At t>=4, F>=24,n>=575, so y>=575^4-1>2^36 and x>2^38.
Since t,F<y, the source radius R=2+t+x+y+F<2x. The literal ledger has E=2^23;
(2x)^E<2^x for x>=2^38: the base case is39E<2^38, and induction uses
(1+1/x)^E<2 for x>=2E. The latter follows by majorizing the finite binomial
expansion by the geometric series in E/x, with strictness. Also y>ell=2^22
implies ell(t+1)<x. These replace precisely the former horizon12 majorant
and label-budget estimates. All local source values are below2^x; all needed
label coefficients fit below q. Range, CRT and Horn-flow soundness follows.

For completeness expand a finite refutation to a proof tree and choose an EVEN
t>=4 at least its rule occurrences, parameters, full derived label sums and
truth-padding label sum, all before F. Every pending nontruth vertex is the
root of a distinct not-yet-expanded subtree, so there are at most t such
vertices. Its label j<=t has weight1+jF<=1+tF<F²-1=n. Truth weights are1.
Thus every pending product is at most(1+tF)^t<V and, being integral, at most
y=V-1. Also y>=F+1. Because n≡-1 mod F and t is EVEN, F divides y.
The moduli1+(i+1)y,0<=i<=t, are pairwise coprime by the inherited difference
argument. CRT supplies x with precisely those state residues, including
F+1 initially and1 finally, and all endpoint/local quotients are natural.
The remaining construction proceeds with N=B^x, precision-N² representatives,
one representative lifted by N², the self-sized S,q, the denominator/frame
values, common-root-compatible A, and fresh Pell witnesses. This order is
acyclic and satisfies the same cofinal semantic-anchor dominance hypothesis.
The pooled completeness argument of Section3 remains valid.

COFINAL_PROOF.md spells out the same specialization independently for review.
The retained authoritative pending-state and beta-CRT construction appears in
inherited/descending18/proofs/inherited/direct_arithmetic.tex, under
"Constructive completeness" in the factorial-weight Horn-flow section.

## 5. Local range decoding and the logical boundary

After factoriality and the preceding bounds, all eleven modular requests are
carry-free. The root modulus Nq^x is divisible by qD_t for the exact digit and
by N times every range denominator because x>max(t+1,y+1). The unchanged
common-root row 2A(q+1)=(q+1)²+1+Nq^x h supplies the required congruences.
For each prime p|d_i and m=v_p(d_i), the one-direction prime-power range lemma
recovers every residue in its specified interval modulo p^(xm). The index
congruence is C≡i-1. The nonnegative local source is strictly below2^x<=p^(xm);
its zero residue forces its actual value to be zero. The derived-label range
bounds all rule labels. Beta overlap and factorial-weight Horn-flow then yield
a finite C222 refutation. No false converse of the prime-power range lemma is
used. The retained C222/ZF/ZFC calibration gives a finite syntactic ZFC
refutation, and the complete reverse construction starts from one.

## 6. Exact artifacts, restoration certificates, and negative result

check_source.py independently checks every name-level raw source mutation and
the cofinal translation/replacement. check_natural.py checks all exact rational
sum-of-affine-squares plus nonnegative-monomial restoration certificates, then
replays every substitution and complete SOS expansion. Rendered TeX rows are
parsed back. A polynomial restoration never changes the domain to integers.
Optional residual-basis shears are invertible integer ROW operations, not
coordinate transformations; they preserve the common zero set on the same
natural orthant. Source pins bind the complete retained offline compiler and
ordinary proof closure. Rebuilds compare every selected coefficient file.

The suggested common-denominator linear budget was also tested. Its raw source
has323 variables rather than325, but contraction yields231 rather than221.
In this six-power natural compiler the modular numerator is a direct Pell
expression Y(q+1)-Z, not a separate authenticated power coordinate. Multiplying
its existing wires by three denominator ratios blocks previously available
quadratic monic eliminations. The normalized construction is therefore not
selected. This is a measured architectural limitation of this implementation,
not an impossibility theorem for all common-denominator natural encodings.
