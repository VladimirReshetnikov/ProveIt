# One binomial for the factorial and the CRT carrier

## 1. Result, domain, and the actual finite object

The principal new equation is the sum of the squares of the 254 quadratic
integer polynomials in `merged_cantor/natural/equation.json`.
Its 319 variables range over N={0,1,2,...}. The fully collected polynomial
has exactly 10,283 monomials, degree four, and coefficient height 86,842,335.
`expanded_polynomial.json` is a second, literal coefficient definition of
the same equation. The raw graph has 465 natural coordinates and 400
quadratic rows. A checked certificate eliminates 146 coordinates with
natural-valued polynomial restorations. Its equation-to-equation equivalence
is independent of the number-theoretic argument below.

The baseline is the final `derived16_cantor` equation in the supplied
`ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip`:
349 naturals, 268 rows, 12,768 terms, height 86,915,503. The present result
improves all four of these measures, at the same exact degree. It does not
improve the smallest-variable equations in other coefficient architectures.

With the inherited ordinary C222-to-ZFC refutation calibration, ZFC proves
that existence of a natural zero of this fixed polynomial is equivalent to
existence of a finite ZFC refutation. Its no-zero sentence is therefore
equivalent in ZFC to Con(ZFC). The argument is ordinary finite arithmetic and
formalizable in ZFC; no new Lean proof term or literal object-language ZFC
derivation is asserted. No assumption that ZFC is consistent is used.

The completed contribution is the identification of the squared-radius
factorial binomial with the reciprocal CRT product, the independently
bounded radix in Section 3, and their integration with common modular
Pell residues. The factorial fixed-point theorem was already proved,
more generally for every nonnegative input, in package 105,
`105-bootstrap-certificates/direct/proofs/NEW_RESULTS.md`, Section 2;
Section 2 below gives an independent elementary proof on the domain used
here, with credit to that predecessor. The residue idea is credited to
package 108, `108-pell-residues`, especially its Sections 5-6. The
factorial-carrier source, reciprocal prime-power CRT, derived label range,
and arithmetic contraction are credited to Round 14. A new combination
and a new fully materialized polynomial are claimed, not discovery of
these inherited lemmas.

## 2. A squared-radius factorial with no additional size guard

**Lemma.** If t>=6 and F is a positive integer, then

    F = ceiling((F^2+1)^t / binom(F^2+t,t))

if and only if F=t!.

Write

    H_t(F) = (F^2+1)^t/binom(F^2+t,t)
           = t! product_{i=1}^t (F^2+1)/(F^2+i).

Every factor is at most one, so H_t(F)<=t!. The asserted ceiling implies
H_t(F)<=F and F<=t!.

First suppose F<t. Each factor (r+1)/(r+i) is nondecreasing in r>=1.
Since F^2>=1,

    H_t(F) >= 2^t/(t+1) > t > F.

The strict inequality 2^t>t(t+1) holds at t=6, and induction follows from
2t>=t+2 for t>=2. This contradicts H_t(F)<=F. Hence F>=t.

For F>=t, the elementary product inequality gives

    product_i (1-(i-1)/(F^2+i))
      >= 1 - sum_i (i-1)/(F^2+i)
       > 1 - t(t-1)/(2F^2) > 1/2.

If F<t^2, it follows that H_t(F)>t!/2>t^2>F, again impossible.
Here t!>2t^2 holds at t=6 and persists by induction. Thus F>=t^2.

Consequently

    sum_i (i-1)/(F^2+i) < t(t-1)/(2F^2) < 1/(2F),
    H_t(F) > t! (1-1/(2F)).

If t!>=F+1, this lower bound is strictly greater than or equal to
(F+1)(1-1/(2F))=F+1/2-1/(2F)>=F, contradicting H_t(F)<=F.
Together with F<=t!, this proves F=t!.

Conversely set F=t!. For t>=6, F>=t^2. The same estimate gives
F-1/2<H_t(F)<=F, so its ceiling is F. This proves both directions.

The only ceiling relation used in the equation is the pair of natural rows

    V+B = BF+r+1,             B=r+s+1.                     (2.1)

When B>0 these imply V+s=BF and 0<=s<B. Therefore they assert exactly
F=ceiling(V/B). They also force F>=1 once V>=1. Conversely the ceiling
identity determines s=BF-V in [0,B-1] and r=B-s-1>=0.

The key match is literal, not asymptotic: the binomial in the lemma is

    B = binom(F^2+t,t),

which is exactly the reciprocal CRT product used by the preceding
construction. One exact binomial therefore serves both purposes. The old
radius F*t^2 needed the different binomial binom(F*t^2+t,t).

## 3. A radix certified before any binomial has been interpreted

Take natural t0,x,y,F and put

    t=t0+16,                 R=2+t+x+y+F,       K=2R,
    B=b0+2,                  N=B^K,            q=N^K,
    V=(F^2+1)^t.

Only the three displayed powers and the later digit denominators are
represented as exact powers. The condition B>=2 is a coordinate shift,
not an assertion depending on the binomial interpretation. Thus, once
the simultaneous power graph is decoded,

    N>=2^K,                 q=B^(K^2)>=2^(4R^2).           (3.1)

This already bounds every lower digit needed to recognize B. For
0<=j<=t and n=F^2+t,

    binom(n,j) <= n^t <= (R^2+R)^t
                         <= 2^(2Rt) < 2^(2R^2) < q.       (3.2)

Use binom(n,j)=0 when j>n. The inequality r^2+r<=4^r for r>=1 follows
at r=1 and by the ratio (r+2)/r<=3<4. Also t<R. These bounds do not use
F=t!, B's meaning, any CRT range, or any local proof label.

The single exact digit therefore gives B=binom(F^2+t,t). The ceiling rows
give F>=1 and then Section 2 gives F=t!. At this point, and only now,
the reciprocal CRT interpretation becomes available.

This is the needed change from the preceding radix N(N+V+1)^K: the new
q=N^K no longer needs V in its arithmetic recipe, because the explicit
B>=2 condition supplies a much stronger independent lower bound.

## 4. Exact-power frame and freely chosen common Pell base

For a>=2 let

    X_0(a)=1, Y_0(a)=0,
    X_{n+1}=a X_n+(a^2-1)Y_n,   Y_{n+1}=X_n+aY_n.

The inherited indexed-Pell graph exactly certifies the pair
(X_n(a),Y_n(a)) for each positive requested index. It shares an auxiliary
Pell pair and a CRT base across all indices; its ordinary proof is retained.

Let W be two plus the sum of the distinct bases, exponents, and outputs
of the six retained exact-power requests. Choose Z>=1, L,A>=0 with

    L^2-((W+1)^2-1)(WZ)^2=1,             A=L+sigma.        (4.1)

Pell classification writes L=X_e(W+1), WZ=Y_e(W+1). Modulo W,
Y_e(W+1)=e, so W divides e. Since WZ>0, e>=W; hence L>W^W and A>W^W.
Conversely e=W supplies L,Z, and then any A>=L is allowed.

For each retained exact request m=n^k, the graph has T_n>=0 and

    T_n=2An-n^2-1,
    X_k(A)+nY_k(A)=A Y_k(A)+m+T_n h,       h>=0.          (4.2)

The modulus row excludes n=0; all requested exponents are positive by
their literal definitions. Since n,k,m<=W and A>W^W, both m and n^k
lie in [0,T_n). The Pell recurrence modulo T_n gives

    X_k(A)+(n-A)Y_k(A) = n^k mod T_n.

Thus (4.2) gives m=n^k. Its completeness quotient is nonnegative:
the left expression is positive and congruent to the least residue m,
and T_n>m. This is the same positive-power argument used by the parents.
Separating L from A makes the later common-root congruence compatible
with completeness.

The six exact requests in the final system are

    V=(F^2+1)^t,       N=B^K,          q=N^K,
    D_t=q^t,          D_y=q^(y+1),    D_x=q^(x+1).

The additional denominator D_{t+1}=q D_t is an ordinary multiplication;
it needs no seventh exact power and no Pell pair at index t+1.

## 5. One common modular root replaces eleven power numerators

Put b=q+1 and

    M=q D_{t+1} D_x D_y = q^(t+x+y+4).

All the digit denominators are among D_t,D_{t+1},D_x,D_y. For each of
them d, qd divides M. Because N divides q, Nd also divides M.

Add the single polynomial equation with natural h0

    2A(q+1)=(q+1)^2+1+Mh0.                              (5.1)

For every integer n>=0 it implies

    R_n = X_n(A)+(q+1-A)Y_n(A) = (q+1)^n mod M.           (5.2)

Indeed the substitution s=q+1-A respects the quadratic relation
s^2=A^2-1 modulo M, so the identity
(A+s)^n=X_n(A)+Y_n(A)s yields (5.2). Furthermore R_n>0: for n>0,
X_n(A)>(A-1)Y_n(A), hence R_n>qY_n(A)>0; for n=0 it is 1.

For the one exact binomial, with n=F^2+t, k=t, d=q^k and output B,
the graph asserts

    X_n+(q+1)Y_n = A Y_n+r+dB+qd h,
    d=r+s+1,              q=B+o+1.                       (5.3)

For a divisibility request N|binom(n,k), it asserts

    X_n+(q+1)Y_n = A Y_n+r+Nd h,
    d=r+s+1.                                             (5.4)

All new variables are natural. Formula (5.2), together with qd|M or
Nd|M, identifies these as exact low-digit conditions for (q+1)^n.
If binom(n,j)<q for j<=k, the binomial theorem shows that (5.3) forces
B=binom(n,k), and (5.4) forces N|binom(n,k). Conversely the true low
digits supply the remainders; all quotients are nonnegative because
R_n>0 and the chosen residue is the least nonnegative residue.

Completeness of (5.1) is essential. Since M is a power of q,
gcd(q+1,M)=1; hence gcd(2(q+1),M) is 1 or 2. In the second case q+1 is
odd and (q+1)^2+1 is even. Thus the linear congruence for A is soluble.
Its solution class contains arbitrarily large positive A. Choose one
above L and sufficiently large to make h0 nonnegative, then supply the
standard common-index Pell witnesses at this A. No semantic variable
has to depend on A before A is chosen.

The eleven modular requests are one exact binomial and ten range
divisibilities. Their upper indices are positive: the eight encoded
columns and encoded index are shifted positive, the binomial upper
index F^2+t>=16, and the derived label expression contains a constant 1.
Their upper indices need not be included in W. They are certified as
indices by the inherited indexed-Pell graph, rather than by a growth
estimate intended only for exact powers.

## 6. The inherited bounded source, made explicit

The numerical C222 calculus has truth label 0 and false target 1. Its
Cantor constructors are

    I(a,b)=2(a+b)(a+b+1)+4b,
    M(a,b)=I(a,b)+1,  A(a,b)=I(a,b)+2,  E(a,b)=I(a,b)+3,
    N(a)=I(a,1),      X(a,b)=N(A(a,N(b))).

The nine axiom conclusion polynomials c1,...,c9 are the eight fixed
C222 rows and its guarded bundle, supplied literally by the frozen
`direct_calculus.py`. Each nonaxiom branch has premise labels and conclusion

    truth: (0,0,0),        modus ponens: (a,I(a,b),b),
    generalization: (b,0,A(a,b));   axiom j: (0,0,cj).

The bundle additionally requires (c-a)^2(c-b)^2=(d+1)^2, exactly
expressing c!=a and c!=b over naturals. The eight local columns are
(a,b,c,d,S,S',u,v). Their bounds are (t,t,t,t,y,y,x,x).
The full local polynomial L(i,local) is the product of the nonnegative
branch residuals plus the squares of

    x-S-(1+(i+1)y)u,
    x-S'-(1+(i+2)y)v.

The selected branch residual expresses

    S'(1+F*conclusion)=S(1+F*premise1)(1+F*premise2),

plus the guarded bundle equation when appropriate. The source includes
the endpoint equations

    x=F+1+(y+1)u0,       y=F+1+r0,
    x=1+(1+(t+1)y)ut.

Let J be the sum of the nine conclusion polynomials, a,b,I(a,b),A(a,b),1.
The extra derived range J(local)<=t bounds every possible rule label.

Because F=t!, the positive weights 1+jF, 1<=j<=t, are pairwise coprime.
Indeed a prime dividing weights j!=k divides j-k and hence is <=t, yet
it would then divide F, contrary to 1+jF=1 modulo that prime. Weight 0
is the unit 1. The beta remainder equations identify S' at one row with
S at the next, as their remainders are <=y. The positive initial
accumulator and positive branch weights inductively make all S,S'
positive. Multiplying all local equalities and cancelling gives

    product(weight(conclusions)) = weight(1)*product(weight(premises)).

Valuations at a prime of each positive label's weight give exact
multiplicity balance: conclusions minus premises is one for label 1
and zero for every other positive label. If 1 were not derivable under
the finite selected rules, every rule concluding outside the derivable
closure would have a premise outside it. Counting such premises and
conclusions contradicts the balance. Truth 0 is already derivable and
does not need a nonunit weight. Thus this certificate implies a finite
C222 refutation, even if the selected rule multiset contains cycles.

Conversely expand a finite proof DAG to a proof tree, choose t>=16 above
its size, all its parameters, and all its finite J-values, and pad with
truth rules. Define F=t! after t is chosen. Expanding a pending proof
multiset backwards supplies positive accumulator products satisfying the
branch equations. Choose y large enough for all products and divisible
by t!, then choose x by CRT for the pairwise coprime beta moduli.
This gives every bounded local witness without circularly bounding
the horizon by the later, much larger accumulator values.

The source calibration is the existing ordinary argument accompanying
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Our construction
uses the numerical calculus endpoint before the machine-specific endpoint.
It neither reads nor simulates the K215 transition table and does not
instantiate Jones's universal polynomial.

## 7. Prime-power CRT and all remaining digit bounds

Set T=F^2 and d_i=1+T/i for 1<=i<=t. Since i divides t!=F, each d_i is
integral and congruent to 1 modulo F. Any prime divisor of d_i exceeds t.
Distinct d_i are coprime, since a common prime would divide i-j. Also

    product_i d_i = binom(F^2+t,t)=B.

The nine independently chosen positive encoded representatives are the
eight local columns A_j and index C. Retain

    C+sum_j A_j+g=9N^2,           B | C+F^2+1,
    N | binom(C,t),              N | binom(A_j,b_j+1),
    N | L(C,A),                  N | binom(J(A),t+1).     (7.1)

Here b_j are the local bounds from Section 6. The last condition replaces
an extra local slack coordinate; J(A) is not included in the aggregate
bound.

The elementary range lemma says that p^e|binom(a,k) implies
a mod p^e<k. For a>=k, the valuation is the sum, over j>=1, of the
0-or-1 quantities floor(a/p^j)-floor((a-k)/p^j)-floor(k/p^j).
If [a-k+1,a] contained no multiple of p^e, all terms with j>=e would
vanish and the valuation would be at most e-1. This proves the lemma.
The case a<k is immediate. Its false converse is never used.

Choose a prime p of d_i and let m=v_p(d_i), e=Km. The index congruence
in (7.1) and p>t identify the small residue of C modulo p^e as i-1.
The other ranges identify bounded residues w_j. The literal majorant
certificate gives L(i-1,w),J(w)<R^E with E=2^23. Since t>=16 and F=t!,
R>=16!>2^44 and the elementary inequality R^E<2^R<2^K holds. It follows
that L(i-1,w)=0. The derived range also forces J(w)<=t, since J(w)
and its small range residue are both below p^e. This establishes all
bounded source hypotheses of Section 6.

For completeness choose C,A_j by CRT modulo d_i^(2K), obtaining positive
representatives at most B^(2K)=N^2. A falling factorial numerator has a
factor divisible by p^(2Km), while division by k! loses at most k-1<=K-1
in p-valuation. Thus every range binomial is divisible by p^(Km), even
though the converse of the range lemma fails at precision K. This also
works for the derived J(A), by polynomial congruence. The evaluation
condition and index congruence hold automatically. The aggregate has a
natural slack because each of its nine terms is <=N^2.

All digit interpretations needed for (7.1) are carry-free. For an ordinary
upper representative n<=9N^2 and 1<=k<=R-1,

    binom(n,j) <= n^k <= 9^k N^(2k)
                      < 2^(4R)N^(2k) <= N^(2k+2) <= N^K=q

for every j<=k; coefficients with j>n are zero. Here N>=2^(2R).

For the derived expression the retained literal positive-DAG certificate
gives ell=2^22 and J(a,b,c,d)<=(n+1)^ell whenever all four inputs are <=n.
As n<=9N^2 and N>=10, n+1<=N^3, so J(A)<=N^(3ell). The finite check
2*16!>=3ell*17 persists by induction, giving 3ell(t+1)<=2F<K. Thus

    binom(J(A),j) <= J(A)^(t+1) <= N^(3ell(t+1)) < N^K=q.

No part of this derived bound incorrectly inserts J(A) in the aggregate.

## 8. Complete order of witnesses and soundness

Soundness proceeds in this exact order:

1. Decode the common indexed-Pell constraints and frame, recovering the
   six exact powers. All their bases/exponents are positive from raw
   polynomial definitions or the modulus rows. In particular B>=2 is
   an explicit shift and independent of factorial/product semantics.
2. Use the independent bound q>=2^(4R^2) and (3.2) to decode the single
   exact binomial. The natural ceiling rows then give F=t! by Section 2.
3. Interpret B as the reciprocal product, establish the factorial growth
   and the carry bounds for all ten range requests, and decode their
   modular Pell residue graphs.
4. Apply the prime-power CRT theorem and the derived label range. Obtain
   every bounded source row and its label bound.
5. Apply Horn-flow soundness and the inherited refutation calibration.

Completeness starts with the finite refutation, chooses the horizon and
source/beta data, then F,B,R,K,N,q and the CRT representatives. It computes
the six powers and eleven genuine binomial residues. With these semantic
data fixed, choose the lower Pell frame L and then a sufficiently large A
in the common-root congruence class. Supply all finite indexed-Pell
witnesses, digit quotients, and natural arithmetic gates. Finally project
the raw solution with the checked elimination certificate. The reverse
restoration of every deleted coordinate is also certified, so the
contracted 319-variable equation has exactly the same existence status.

## 9. Reproduction and evidence boundaries

The new builder is `build_modular_factorial.py`. For the principal result:

    python3 -B build_modular_factorial.py --radix power --merge-factorial --output NEW_DIRECTORY

It imports the frozen, inspected Round 14 compiler, retains the ordinary
source theorem, and writes only to the explicit new output path. Its
independent contraction checker reconstructs the complete quartic, not
samples of its values. The new semantic regression checker uses explicit
exceptions rather than `assert`, so optimization mode preserves checks.

The tests verify finite arithmetic and reproducibility. The unbounded
lemmas and consistency equivalence are established by the ordinary proofs,
not inferred from tested instances. The current equation is not claimed
globally minimal, and no assertion about worldwide priority is made.
