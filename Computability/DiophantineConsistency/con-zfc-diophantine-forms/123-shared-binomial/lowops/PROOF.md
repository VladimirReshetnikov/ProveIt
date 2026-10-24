# A single product equation in eleven unrestricted integers

## Result and scope

This component gives two complete ordinary integer polynomials, each with
eleven unrestricted integer unknowns and the six unchanged, fixed source34
coefficient ports. The native-index form has **111 binary operations and
exact degree 966**. Replacing its first-index modulus by `4q^4` gives
**112 operations and exact degree 882**. These are operation/degree tradeoffs
against the independently developed lower-degree three-root forms.

The arithmetic mechanism is a product of three pairwise coprime integers.
A congruence modulo four recovers their signs after square extraction.
There is no radical norm in the displayed equation. The strong Pell
ordinate is saturated with the square root of an already coprime product;
the auxiliary coordinate is rescaled compatibly. A weak scalar carrier and
the supported-modulus interpolation theorem supply the reverse direction.

The claimed consistency equivalence uses the same explicitly retained
ordinary source34/native/compiler/refutation calibration as the predecessor.
The new result is the complete ordinary arithmetic reduction below. It is
not a new Lean/Rocq endpoint, a machine-checked object-ZFC derivation, a
proof of consistency, or a global simplicity minimum.

## 1. Complete polynomial

All eleven independent variables

    j, C, z, h, r, v, w, T, c, n, s

range over **all integers**. The fixed ports are

    beta, K0, MC, MF, cone_A, cone_B.

They are the entire coherent source34 tuple, including the already-shifted
MF, with `beta=2^1064921-1`, `cone_A=2^1113`, and
`cone_B=2^666104`. The supplied compressed bytes and reconstruction recipe
specify all six numerals. They are not quantified parameters.

Every following symbol is a polynomial abbreviation:

    J=6j+1, q=beta J+1, W=12w+4,
    X=qW, Y=(2v+1)q^3, E=XY,
    a=(X+1)Y, A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    F=(K0+W)C-z(q-1),
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J.

Choose one of two explicit moduli:

    M_index=XY              (111-operation form),
    M_index=4q^4            (112-operation form).

Continue with

    k=R+1+h M_index, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2,
    D=3Budget-4,
    ell=XY^2, Dt=1+ell(ell+1)k^2,
    Dg=1+4D Dt s^2, P=Dt Dg,
    Dm=1+Delta c^2,
    U=r c^2 A Dm,
    Df=1+Delta U^2 P,
    Q=Delta^2 U^2 P, delta=Q-1,
    b=c-R+4UPT, V=Df b-c, Cy=QV^2-1,
    K=X(3c-2X)+2,
    S=srH, zc=HT+K,
    Ac=(zc^2+3H^2)(zc^3-19H^3), Z=Sn-Ac.

The single equation is

    delta Z^2 - S^2 P Df Cy = 0.                         (1)

This is a division-free ordinary polynomial with integer coefficients.
In the literal graph Dg is not materialized; the identical identity

    P=Dt+D(2Dt s)^2

saves one multiplication. In the short-index form, the existing register `4q^2`
from the budget is also used to compute `(4q^2)q^2=4q^4`, saving
one more multiplication without changing the polynomial. The shared product `UP=U*P` is reused in
`strong=(Delta U)*UP` and `b=c-R+4UPT`.

## 2. Unconditional nonzero facts

The actual affine restrictions and fixed tuple give, for every integer
assignment,

    q even, q=2 mod3, |q|>=beta-1,
    X=0 mod8, X=2 mod3, |X|>=4|q|,
    Y=0 mod8, |Y|>=|q|^3,
    |a|>2, A!=0, H odd and nonzero, Delta>1.

In particular A is even and Dm is a positive integer. For every integer
ell, ell(ell+1)>=0, so Dt>=1. Moreover ell is a multiple of eight,
hence Dt=1 modulo eight. Since Dg=1 modulo four, it is nonzero and

    P=1 mod4, P!=0.                                    (2)

Because Delta>1, neither `Df=1+Delta U^2 P` nor `delta=Delta^2 U^2 P-1`
can vanish. Also `Cy=QV^2-1` cannot vanish: an integer identity QV^2=1
would force Q=1, already excluded. Thus

    Da=(Q-1)(QV^2-1)=delta Cy

is nonzero on every integer assignment. No sign or Pell interpretation
has been used for these assertions.

If S=0, equation (1) reduces to `delta Ac^2=0`. This is impossible.
Indeed H!=0 and

    Ac=H^5 pi(T+K/H), pi(x)=(x^2+3)(x^3-19).

The first factor has no real zero; the second has no rational zero.
Therefore every zero of (1) has S!=0, and hence s,r are nonzero.
The value c has not yet been shown nonzero.

## 3. Coprimality and sign recovery, including c=0

All gcds here mean gcds of absolute integer values. Directly,

    gcd(P,Df)=1,
    Q=0, delta=-1, Cy=-1, Da=1 modulo P,

so gcd(P,Da)=1. Modulo Df,

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm,
    Da=A^2 Dm.

Since `A Dm | U`, the integer Df is 1 modulo both A and Dm.
Consequently

    gcd(Df,Da)=1.                                      (3)

These identities remain valid for negative P or Df and for U=0.

Multiplying (1) by delta and dividing by the nonzero rational square S^2
gives

    (delta Z/S)^2 = P Df Da.                           (4)

The right side is a nonzero integer. A rational number whose square is an
integer is an integer, so it is an integer square. By (3), the absolute
value of each of P,Df,Da is separately an integer square. By (2), P cannot
be the negative of an odd square, which would be 3 modulo four. Thus P>0.
Now Df=1+Delta U^2 P>0, and (4) forces Da>0. We obtain positive integers

    p0^2=P, f^2=Df, e0^2=Da.                           (5)

There is a second coprime split:

    gcd(Dt,Dg)=gcd(Dt,1+4D Dt s^2)=1.

Dt is positive and P=DtDg>0, so Dg>0. Therefore

    Dt=tau^2, Dg=g^2, p0=tau g

for positive integers tau,g. Since s!=0, Budget<=1 would imply D<=-1
and `Dg<=1-4Dt<0`, a contradiction. Hence Budget>=2.

The centered-budget argument is now valid. It supplies k!=0,
Derr<q^2, the common nonzero sign of q,F,C,q-F-C, and

    |c/k-Y|<1/2, sign(c)=sign(kY).

It also excludes c=0 directly: at c=0,

    Budget=k^2[q^2-Derr-4q^2Y^2]<=0,

since |Y|>=1. Thus c!=0 and U!=0. We have now recovered positivity
before invoking any Pell classification or dividing by c.

## 4. Restore the complete strong and auxiliary source

Define only in the proof

    I=U p0, T_old=p0 T.

They are integers, `I!=0`, `c^2|I`, and `|I|>=c^2`. The exact restored
identities are

    f^2=1+Delta I^2,
    Q=(Delta I)^2>1,
    b=c-R+4I T_old,
    V=f^2(c-R+4I T_old)-c.

The rational number `y=e0/delta` satisfies

    QV^2-(Q-1)y^2=1.                                   (6)

It is integral. Here is the adjacent-coefficient descent in the form
needed here. If y=u/d is in lowest terms, d^2 divides Q-1. The map

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserves (6), keeps V' integral, and preserves the reduced denominator
d. After reflecting signs, V>1 and y>0 give V<y<QV/(Q-1), hence
-V<V'<V. The norm prevents V'=0. Descent reaches |V|=1, where |y|=1.
Thus d=1. This proves the assertion without assuming divisibility by
delta from the fact that Da is a square.

Canceling nonzero delta in (1) after (5)--(6) gives

    Z^2=S^2 p0^2 f^2 y^2.

Thus Z/S is an integer, and S|Ac. Because H|S and Ac=K^5 modulo H,

    H | K^5.                                          (7)

The congruences needed for signed rank recovery hold exactly:

    V=-c modulo f,
    V+R=Delta I^2(c-R)+4I Df T_old=0 modulo c.

No assumption that I/c^2 is odd has been introduced. The retained
signed-folding theorem explicitly permits an arbitrary nonzero integer
strong multiplier.

## 5. Smaller first-index modulus

For the native-index variant the retained centered-rank proof applies
without any change to its first-index congruence. For the short variant
we verify the only changed input to that argument.

The packing bounds supplied by Budget>=2 give

    0<R<|q|^4-2.

Set M=4q^4. Then M>3R+1. The identity

    2XY^2=2(12w+4)(2v+1)^2 q^7

shows `M | 2XY^2`. Write xi=sign(X), sigma=sign(k), and
`PellBase=|2XY^2+1|`. The latter is congruent to xi modulo M.
The first Pell classification therefore yields an index n1>=1 and

    |k|=2 psi_PellBase(n1),
    sigma xi^(n1-1) 2n1 = R+1 modulo M.                (8)

The unaltered strip and growth estimates give the main index p>=1 with
`|c|=psi_|A|(p)` and p>n1. If the sign in (8) is positive then
n1>=(R+1)/2. If negative, n1>R because M>3R+1. Thus all initial growth
bounds in the retained proof hold. Strong and auxiliary folding then
give p=R, without using the projection (7). Since n1<p=R, the negative
case is impossible. Both 2n1 and R+1 lie strictly between zero and M,
so (8) gives `2n1=R+1` exactly.

All subsequent ratio, projection and sign arguments are unchanged.
After their orientation conclusions, the exact first-Pell formula is

    k=2 psi_(2XY^2+1)((R+1)/2).

Reduction of this recurrence modulo XY gives `XY | k-R-1`. Hence
`h_old=(k-R-1)/(XY)` is an integer and restores the original source's
literal h coordinate. A new h is allowed because it occurs in that
source only in the definition of k.

For completeness, the canonical first-Pell value satisfies the same
recurrence. Since M|2XY^2, it has `M | k-R-1`; choose the new h as the
corresponding integer quotient. Thus both directions are proved. The
change does not assume that XY and 4q^4 are equal or divide one another.

## 6. Fifth-power projection and the finite-refutation endpoint

The retained signed folding and rank proof, with Section 5 for the short
index, now gives `R=2t+1`, `t>=24`, and

    c=sigma psi_A(R), x=|X|>=4(beta-1)>=2^64,
    |Y|>(x-3)^t/2-1,
    |H|>x(x-3)^t>x^(t+1)/2^t.

Let `Kquad=X(X+2ac)-1`. The identity

    K=HXc-2Kquad

and odd H show that (7) implies H|Kquad^5. The exact signed-Pell
projector congruence is

    2^R Kquad = Pi modulo H,
    Pi=(sigma X-2^R)(2^R sigma X+1).

Thus H|Pi^5. Each factor has absolute value less than `2^(R+1)x`, so

    |Pi|^5<2^(20t+20)x^10<|H|.

For the last inequality use x>=2^64 and

    64(t-9)-(21t+20)=43t-596>=436>0.

It follows that Pi=0. Its second factor is odd and nonzero, so
sigma X=2^R. The retained centered orientation and half-binomial proof
then restores X,c,k,Y>0, `0<eta/k<1/4`, the exact main-Pell projection,
and every literal old signed source row after fresh private witnesses
are regenerated. Section 5 restores h_old when required.

This is the full hypothesis set of the inherited source34/native finite-
refutation endpoint. Therefore a zero of either new polynomial yields a
finite syntactic ZFC refutation, under that same named ordinary calibration.

## 7. Completeness, with a fixed strong pair

Start with the canonical outer witness supplied by a finite refutation.
Keep j,C,z,v,w,c and the canonical first-Pell value k; choose h using the
appropriate modulus. The source gives A>1 even, R=3 modulo four,
`c=psi_A(R)>0`, `c=R modulo four`, and `Dt=tau^2` with tau>0.
It also gives the stronger centered Budget>=64.

The positive integer `D Dt=(3Budget-4)Dt` is 2 modulo three, hence
nonsquare. Ordinary Pell existence and squaring a positive unit give
positive integers s,g with

    g^2=1+4D Dt s^2.

Fix these and set `p0=tau g`. Now A,Dm,p0,s,c are fixed positive
integers. Choose ONE positive strong Pell pair I,f with

    4s A Dm p0 c^2 | I,
    f^2-Delta I^2=1.

The retained finite-period construction and supported-modulus
interpolation theorem supply such a pair. Define

    r=I/(A Dm p0 c^2), U=I/p0.

These are positive integers; r is a multiple of 4s. Keep this pair
I,f fixed from now on. Every prime factor of `M=p0 s r` divides I.

The canonical projector gives H|K; put kappa=K/H. The classical
intersective quintic pi(x)=(x^2+3)(x^3-19) has a root modulo every positive
integer. Choose a residue a0 modulo sr with

    pi(a0+kappa)=0 modulo sr.

The supported-modulus interpolation theorem, applied to this same fixed
I,f and modulus M, supplies an auxiliary T_old in the prescribed class

    T_old=p0 a0 modulo p0 s r,

with its full integral auxiliary Pell witness y. Consequently p0|T_old;
set T=T_old/p0. Then T=a0 modulo sr and

    Ac/S=H^4 pi(T+kappa)/(sr)

is an integer. The auxiliary equality is precisely the new equality,
since `4I T_old=4UPT`. Finally choose

    n=Ac/S+p0 f y.

This unrestricted integer makes (1) vanish. The order is outer witness,
guard s/g, one strong I/f/r, intersective residue, T_old and T/y, then n.
No strong pair is changed after the residue is requested; no coprimality
between H, s, r, p0, or I is assumed.

Therefore each polynomial has an integer zero exactly when the calibrated
source has a finite syntactic ZFC refutation. Composing the retained
ordinary calibration gives in ZFC the equivalence between the polynomial's
universal nonvanishing over Z^11 and Con(ZFC).

## 8. Exact degrees and coefficients

With q0=6 beta j, X0=12q0 w, Y0=2v q0^3, a0=X0Y0, let k0 denote the
top homogeneous part of k. It is

    k0=h a0                          (native modulus),
    k0=4h q0^4-q0^3 F0,
    F0=12w C-q0 z                    (short modulus).

The prefix degrees are as follows; each indicated leading part is nonzero.

| register | k | P | U | Df | Q | b | V | Cy | S | Ac |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| native | 7 | 94 | 23 | 152 | 164 | 118 | 270 | 704 | 8 | 35 |
| short | 5 | 82 | 23 | 140 | 152 | 106 | 246 | 644 | 8 | 35 |

In both variants Z has degree 35. The first summand delta Z^2 has
degree 234 or 222. The second summand has degree 966 or 882 and
therefore uniquely determines the top homogeneous part.

Direct multiplication, with

    P0=-48 q0^2 X0^4 Y0^10 k0^6 s^2,
    U0=r a0^3 c^4, S0=4sr a0,

gives the complete leading form

    2^36 * 3^7 * q0^14 X0^70 Y0^112 k0^42 s^16 r^12 c^40 T^2.

For the native form it is a single monomial. Its coefficient at

    j^588 w^112 v^154 h^42 s^16 r^12 c^40 T^2

is exactly `2^1002 * 3^707 * beta^588>0`. For the short form the coefficient
at

    j^588 w^70 v^112 h^42 s^16 r^12 c^40 T^2

is exactly `2^960 * 3^665 * beta^588>0`. It is selected by the maximum
h exponent in k0^42. The exponent sums are respectively 966 and 882.
These are polynomial degree proofs at the actual fixed beta, not degree
guesses from numerical evaluation along lines.

The independent checker does not import the producer. It verifies all
literal local polynomial formulas, every live gate, the complete coefficients,
the exact leading monomial at every gate, the coprimality remainder identities,
the auxiliary rescaling identities, and the smaller-modulus divisibility.
Finite checks support the artifact and algebra; they do not replace the
unbounded Pell, interpolation, or inherited consistency arguments.

## 9. Read dependencies

* Incoming `ZFC_Diophantine_Coprime_Projection_2026-10-24.zip`, component
  `integer/PROOF.md`, especially Sections 2--4; the original complete
  source34 coefficient tuple and its reconstruction recipe.
* Its `integer/source/centered11-proof.md`, Sections 3, 5.2--5.4 and 6:
  centered signs, signed rank recovery, exact half-binomial interval,
  restoration to the native endpoint, and the original full-residue theorem.
* Its `integer/source/signed-quadratic-proof.md`, Sections 2 and 5:
  absolute main-root folding and the signed quadratic projector congruence.
* Incoming `ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip`,
  `radicals/PROOF.md`, Sections 4--6: fifth-power saturation and supported-
  modulus interpolation with its explicit Pell valuation proof.

The new square-root saturation has a separately checked completeness
rescaling. It is not a pointwise polynomial substitution of the old
all-fused equation and does not assert a bijection of arbitrary zeros.
