# Pooled low digits and a semantic Pell cap

## Result and exact scope

The principal polynomial is the sum of the squares of all 175 literal
quadratic residuals in `equations/natural226/equation.json`. It has 226
independent nonnegative integer variables, exact degree 4, 10,314 collected
monomials and maximum absolute coefficient 87,839,583. The sparse companion
has 227 variables, 176 residuals and 7,905 monomials at the same height.

The following is an ordinary mathematical proof, formalizable in ZFC:

    a zero of either polynomial exists in its stated natural domain
        if and only if a finite C222 derivation exists
        if and only if a finite ZFC refutation exists.

Negating yields the requested equivalence with Con(ZFC). The last two
calculus/refutation interfaces and the unmodified arithmetic compiler are
inherited explicitly from ProveIt package 129, pinned at commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`. They are mathematical dependencies;
this packet does not assert a new end-to-end Lean/Rocq proof, a reconstructed
object-language ZFC proof object, a proof of consistency, or global minimality.

The finite transformation is made on package 129's **344-variable normalized
quadratic graph**, not on an unspecified Diophantine predicate. Its complete
literal source and full semantic graph are retained. The independent affine
checker binds that literal source to every row of the semantic graph. The
new finite checker binds each changed row, every projection substitution,
and every final quartic coefficient. Finite checks do not prove the unbounded
arithmetic claims below by enumeration.

## 1. Inherited source, stated before the changes

Write N={0,1,2,...}. All source coordinates and auxiliary quotients in this
section range over N. The source uses the C222 Cantor constructor

    I(a,b)=2(a+b)(a+b+1)+4b.

Its semantic data include t>=16, F, x, y, B>=2 and

    R=2+t+x+y+F,  K=2R,  N=B^K,  q=N^K,
    V0=(F^2+1)^t,
    Dt=q^t,  Dt1=q*Dt,  Dy=q^(y+1),  Dx=q^(x+1).

The six displayed variable powers are represented by the retained quadratic
Pell power graphs. They are conclusions of the source's exact-power lemma;
their meanings are not assumed prematurely in soundness. The source's
factorial fixed-point binomial is B=binom(F^2+t,t), and its exact semantics
eventually imply F=t!. The nine independent CRT representatives are

    a,b,c,d,S,Sp,u,v,C.

The derived label upper index J is the sum of nine nonnegative axiom
conclusion polynomials, a, b, I(a,b), another nonnegative constructor and 1.
In particular J>=I(a,b)>=2a^2 and J>=2 in the actual source.

There are eleven modular numerator requests. Each has a remainder r_i and
an old private slack s_i giving D_i=r_i+s_i+1:

| Requests | Common denominator |
| --- | --- |
| factorial binomial and C | Dt |
| a,b,c,d,J | Dt1 |
| S,Sp | Dy |
| u,v | Dx |

The exact factorial binomial separately retains its digit-output bound
q=B+o+1. Its row is not removed in the selected equations.

The source has one complete indexed Pell certificate at H=J, with
(Xcap,Ycap)=(X_H(A),Y_H(A)). Fourteen other requested positive indices have
principal Pell pairs. They are

    t,K,y+1,x+1,F^2+t,a,b,c,d,S,Sp,u,v,C.

In the actual normalized graph the independent pairs use consecutive
ordinates (Y_i,Z_i):

    Y_i^2+Z_i^2-2*A*Y_i*Z_i=1.

Each occurrence of the cubic-looking product has its retained product gate,
so every emitted residual is quadratic. Output rows force Z_i<A*Y_i and
identify the positive orientation. The full anchor retains ordinary Pell
coordinates. Package 129 proves this orientation before its index conclusion.

The frame W is a positive constant plus the distinct exact-power base,
exponent and output atoms and all modular upper indices. In particular,
before any power or binomial semantics,

    W>=3,  2<=H<W,  1<=k_i<W,  r=14<=W-2.

Its independent lower Pell witness L and the free slack A-L force

    A >= (W+1)^W,  A-1>W^3.

The modulus-congruence class for A remains cofinal because the lower witness
is L and A=L+sigma; A itself is not forced to be that witness's Pell abscissa.

The old two cap rows were

    Ycap = H+1+s+sum_i Y_i,
    sum_i (Y_i-k_i)^2 = (A-1)*Qold.

The source already proves that its entire graph has a natural zero exactly
when C222 has a finite derivation. The changes below replace only these cap
rows and the eleven private remainder bounds.

## 2. A general pooled digit-budget lemma

Let q>=2 and k>=1. Suppose n_1,...,n_m are nonnegative integers and every
coefficient below position k satisfies

    sum_i binom(n_i,j) <= q-1  (0<=j<k).

Define the canonical low residues

    r_i = sum_(j=0)^(k-1) binom(n_i,j)*q^j.

Then

    sum_i r_i <= (q-1)*sum_(j=0)^(k-1)q^j = q^k-1.

Thus the **single** row

    q^k = sum_i r_i + s + 1,   s>=0,

has a witness. Conversely, for arbitrary nonnegative r_i and s, this row
implies r_i<q^k for every i. Every old private slack can be restored by

    s_i = s + sum_(h!=i) r_h.

This restoration is an integer polynomial with nonnegative coefficients.
Consequently pooling strengthens the raw constraints, with a direct
soundness map. Its completeness requires a bound on the *sum* of the low
digits, not merely the old separate bounds r_i<q^k. That required bound is
proved next for the actual construction.

## 3. The actual radix has enough spare digits

This section is a **constructive completeness argument**. Start with an
arbitrary finite C222 refutation and choose the inherited true witnesses.
Thus F=t!, N=B^(2R), q=N^(2R), and all six powers already have their intended
values. No attempt is made to use F=t! in the soundness bootstrap.

The package-129 CRT construction first chooses all nine positive
representatives at most N^2 and then replaces only a by a+N^2. Hence every
representative is at most 2N^2, their sum is at most 10N^2, and all original
local congruences survive. We will use the weaker bound n<=10N^2 for
ordinary representative indices. As B>=2,

    N>=4^R,   q/N^2=N^(2R-2),   N^2>=6.

Every lower index k in {t,t+1,y+1,x+1} is at most R-1. For an ordinary
representative and 0<=j<k,

    binom(n,j) <= max(1,n^j)
              <= (10*N^2)^(R-2)
              < N^(2R-2) = q/N^2.

The strict estimate follows from 10^(R-2)<N^2, since N^2>=16^R.

For the factorial upper index n0=F^2+t, use n0<R^2+R and
R^2+R<=2^(2R) for integers R>=1. Since t<=R,

    binom(n0,j) <= n0^t <= 2^(2R^2)
                  <= 2^(4R^2-4R) <= N^(2R-2)=q/N^2

for 0<=j<t. Here R>=2; in the actual construction R is much larger.

For J, the retained literal positive-DAG majorant gives

    J <= N^(3*ell),   ell=2^22.

This follows from J<=(10N^2+1)^ell and 10N^2+1<=N^3 for the actual N.
The retained factorial budget at t>=16 is

    3*ell*(t+1) <= 2*t! = 2F.

For 0<=j<t+1 we therefore have

    binom(J,j) <= max(1,J^j) <= N^(3*ell*t)
                <= N^(2F) <= N^(2R-2)=q/N^2.

Every group has at most five members. Since q/N^2 is an integer and N^2>=6,

    5*(q/N^2) <= q-1.

Thus every group's sum of low digit coefficients is at most q-1. The pooled
digit-budget lemma supplies four nonnegative slacks, one for each common
denominator. This proves completeness of all four new bounds with the
unchanged radix q. It does not rely on a further free enlargement of q.

The exact low residues used here are valid Pell output residues: after
choosing the common-root-compatible A, the unchanged Pell identities give
the same (q+1)^n modulo every relevant digit modulus. The ordinary binomial
theorem and the coefficient bounds above identify the low digits. All
private output quotients remain those of the inherited construction; the
new inequalities only replace their remainder slacks.

## 4. One natural row replaces both cap rows

For A>=2 define the standard Pell sequence by

    X_0=1, Y_0=0,
    X_(n+1)=A*X_n+(A^2-1)*Y_n,
    Y_(n+1)=X_n+A*Y_n.

We use the elementary identities and inequalities

    Y_n=n mod(A-1),   Y_n>=n,
    X_n>(A-1)*Y_n for n>=1,
    Y_(n+1)>(2A-1)*Y_n for n>=1,
    Y_(2n)=2*X_n*Y_n.

They follow from the recurrence, norm identity and multiplication of Pell
units. Natural norm-one solutions have canonical ordinates Y_j. The same
is true for the consecutive-ordinate conic after restoring |A*Y-Z|.

**Fused cap theorem.** Suppose W>=3, A-1>W^3, 2<=H<W, r<=W-2,
1<=k_i<W, and a complete retained certificate fixes V=Y_H(A). If every
nonnegative Y_i is a canonical Pell ordinate and Q>=0 satisfies

    V = H + sum_i (Y_i-k_i)^2 + (A-1)*Q,                 (FC)

then Y_i=Y_(k_i)(A) for every i.

**Soundness proof.** Write Y_i=Y_(j_i)(A), j_i>=0. The row implies
|Y_i-k_i|<=sqrt(V). Because H>=2,

    V>=Y_2(A)=2A>2W,   V>4.

Hence W<V/2 and sqrt(V)<V/2. Therefore

    Y_i <= k_i+sqrt(V) < W+sqrt(V) < V.

Strict monotonicity gives j_i<H<W. Reduce (FC) modulo A-1. Since
V=H and Y_i=j_i modulo A-1, that modulus divides

    E = sum_i (j_i-k_i)^2.

But 0<=E<=r(W-1)^2<W^3<A-1. Thus E=0 and j_i=k_i for all i. The full
anchor criterion's required bound H<=V is supplied directly by (FC).

**Constructive converse.** It is enough that H>=2m+1, where m=max_i k_i,
in addition to the preceding frame bounds. Take the true canonical pairs.
As Y_(k_i)>=k_i,

    Ebig=sum_i(Y_(k_i)-k_i)^2 <= r*Y_m^2.

Using doubling and growth,

    V=Y_H >= Y_(2m+1)
       > (2A-1)*Y_(2m)
       = 2*(2A-1)*X_m*Y_m
       > 2*(2A-1)*(A-1)*Y_m^2.

The frame implies A>W. Thus 2*(2A-1)*(A-1)>r+H and Y_m>=1, so
V>r*Y_m^2+H>=Ebig+H. Moreover V-H and every Y_(k_i)-k_i are divisible
by A-1. Consequently

    Q=(V-H-Ebig)/(A-1)

is a nonnegative integer satisfying (FC).

This natural-domain specialization removes the abscissa-sign squares needed
by a signed-domain cap. A one-row cap is already present in package 128;
we claim the new composition with package 129's semantic anchor and pooled
digits, not the first discovery of the general one-row mechanism.

## 5. The semantic anchor supplies the doubled gap for free

The unchanged CRT lift has N^2<a<=2N^2. Package 129's explicit label
polynomial satisfies

    H=J >=2a^2 >2N^4.

Every other CRT representative is at most N^2 and the lifted a is at most
2N^2. The five non-CRT seed indices t,K,y+1,x+1,F^2+t are at most N by
N>=4^R and the elementary bounds in the retained source proof. Thus

    m=max_i k_i <=2N^2.

Since N>=2, 2N^4>=4N^2+1; hence H>=2m+1. The stronger gap required by
the fused cap is already supplied by the existing CRT choice. No new
nominal-index inequalities, CRT variable, exponentiation, or budget doubling
is inserted into the equation.

In soundness the gap H>=2m+1 is unnecessary. Soundness uses only the raw
frame bounds and the fused row. This distinction is essential: the equation
does not assert that its arbitrary a-coordinate exceeds N^2.

## 6. Complete soundness and completeness order

From a zero of the new raw graph:

1. The unchanged raw frame gives A-1>W^3, H and all k_i below W.
2. The full indexed anchor is applicable because (FC) gives H<=V.
3. The fused-cap theorem identifies all fourteen seed ordinates. Their
   retained output rows select the positive consecutive orientation exactly
   as in package 129, without interpreting any binomial first.
4. Restore the old cap rows using

       Qold=sum_i(Y_i-k_i)^2/(A-1),
       s=Y_H-H-1-sum_iY_i.

   Both are natural. For the second, k_i<H and the Pell growth bound give
   Y_H-sum_iY_i >=Y_H-rY_(H-1) >H, exactly as in the retained cap proof.
5. Restore each old private remainder slack by the nonnegative sum in
   Section 2. All other rows are unchanged. This gives a zero of the entire
   inherited graph, whose ordinary source theorem yields a C222 derivation
   and then a ZFC refutation.

For completeness start with a finite C222 derivation. Use the retained
padding/CRT construction and the same a-to-a+N^2 lift. Compute the true
factorial, binomial, all six powers, representative values, label J and
frame W. The bounds of Section 3 supply the four new digit slacks before
any Pell witnesses are chosen. Choose the independent lower-frame L and
then a sufficiently large A in the unchanged soluble common-root congruence
class. Supply the true seed pairs and the complete indexed anchor at J.
Sections 4 and 5 give Q>=0 for (FC). Keep all original output witnesses and
quadratic gates. This constructs a zero of the new raw graph.

The source modification is therefore an equivalence of **existence of
zeros**. It is not a claimed bijection on all arbitrary old witnesses: an
old witness need not have the doubled semantic-index gap or the stronger
pooled digit bounds. Completeness deliberately reconstructs witnesses from
the derivation using the proven CRT choice.

## 7. Literal finite construction and projection

The pinned normalized source has 344 natural coordinates and 293 rows.
Removing the four private aggregate-cap sum gates and their slack, fusing
the cap row, and pooling eleven remainder bounds into four leaves 332
coordinates and 281 rows. The raw fused row uses exactly the original
quadratic squared errors, the linear H and Ycap terms and the bilinear
(A-1)*Q term. No residual has degree greater than two.

The principal contraction removes 106 further coordinates by monic
substitution, with every restored coordinate certified as an integer
polynomial nonnegative on the natural domain. The resulting 226-variable
system has 175 rows. The independent checker verifies each rational
sum-of-squares or nonnegative-monomial certificate and replays all exact
substitutions. Squaring and summing gives the stated literal quartic.

The sparse projection removes 105 coordinates and has 227 variables and
176 rows. It uses exactly the same unbounded source proof. Its coefficient
height equals the principal one's and its support has 7,905 monomials.

The final coefficient lists contain no variable exponent, factorial,
binomial, machine code, free coefficient port or bounded universal
quantifier. The indexed JSON monomials are ordinary products of their
listed variables. All coefficients are explicit integers.

## 8. Unrestricted-integer companion

For each natural coordinate substitute

    g(a,b,c)=a^2+b^2+c(c+1).

This is nonnegative at every integer triple and is surjective onto N.
Indeed, 4n+1 is not of the forbidden three-square form 4^e(8h+7); a
three-square representation of 4n+1 has exactly one odd entry. Move it to
the third position and divide the two even entries by two to obtain g.

Thus P226(g(z_0,z_1,z_2),...,g(z_675,z_676,z_677)) is a completely specified
ordinary degree-eight polynomial in 678 unrestricted integer variables with
the same consistency equivalence. The packet supplies this finite
substitution recipe alongside the full P226 coefficients. This companion
does not claim to improve the repository's specialized signed quartics.

## 9. Attribution and limits

Package 129 supplies the semantic J anchor, its CRT lift, consecutive
ordinates, six-power modular compiler and ordinary calibration. Package128
supplies the preceding one-row cap idea. Package100 supplies the retained
exact nonnegative projection code. Those contributions are not claimed as
new here. The new work is the pooled low-digit theorem instantiated with
an explicit radix-margin proof, its simultaneous use with the unaltered
semantic anchor and fused cap, and the fully materialized smaller equations.

The two named logical interfaces retained from package129 are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. This packet retains
their exact inspected identities and the source proof boundaries, without
claiming a fresh audit of their complete formal dependency closure. Neither
K215 nor Jones's universal polynomial is instantiated by this construction.
