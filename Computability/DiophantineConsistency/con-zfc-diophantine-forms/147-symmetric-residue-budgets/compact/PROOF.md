# Removing the auxiliary positivity shift

## Result and exact scope

The two literal equations in this component use ten strictly positive integer
unknowns and the complete fixed indexed BFS943 coefficient tuple of the
incoming `ConZFC_Certificate_Reductions_2026-10-25.zip` at ProveIt commit
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`.

| Polynomial | Binary arithmetic operations | Exact total degree |
|---|---:|---:|
| `equation77_degree630.json` | 77 | 630 |
| `equation78_degree468.json` | 78 | 468 |
| Matched incoming parent, V-squared weight | 78 | 630 |
| Matched incoming parent, bV weight | 79 | 468 |

The change removes one addition from each matched parent at unchanged
degree and unchanged domain. It is a small arithmetic reduction. No global
minimum or literature-wide novelty claim is made. Its mathematical content
is a low-index exclusion and a signed transport argument that shows why a
previous positivity shift is redundant.

The ordinary proof below establishes an explicit bijection between each
parent's positive zero set and its corresponding new positive zero set.
Therefore the inherited theorem gives, provably in ZFC,

    no positive-integer zero of the new polynomial iff Con(ZFC).

No assertion of consistency or of nonsolvability separately is made. This is
an ordinary proof formalizable in ZFC, not a newly emitted end-to-end
proof-assistant certificate.

## 1. Complete formulas

The only independent unknowns are

    J,F,alpha,i,T,w,s,n,eta,zeta in Z_{>0}.

The four fixed integers are `beta,K0,MC,MF`, with the inherited verified box

    beta >= 31, K0 > 0, 0 < MC < beta < MF < 2 beta.

Their complete literal payloads and finite reconstruction recipe are retained
in `upstream/`. No coefficient port is an extra unknown. Define

    q=beta*J+1, h=q-1, C=q-F-alpha, X=w*q, Y=q^3*s,
    k=eta+zeta, c=k*Y+eta, A=Y*(X+1)+1,
    Delta=A^2-1, H=4*A-5, D=Y^2, V0=X*D,
    E=1+V0*(V0+1)*k^2,
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, B=(K0+w)*C-F,
    U=i*c^2, a=Delta*U^2*E, F0=1+a, G=E*F0,
    Fsqr=1+4*a*F0, Q=Delta*(Fsqr-1),
    b=c*T-R, V=Fsqr*b-c,
    Kpos=X*(3*c-2*X)+2.

For the 77-operation equation put `L=V^2`; for the 78-operation equation
put `L=b*V`. In either case set

    M=h*D*H,
    Z=h*D*[H*(n-L*B)+Kpos]-H*[D*B+h*e],
    RG=M^2*G,
    P=Q*(Z^2-RG*V^2)+(RG-Z^2).

The requested single equation is `P=0`. Every name other than the ten
independent coordinates is a polynomial abbreviation. The data circuits
evaluate these formulas using only addition, subtraction, and multiplication.

The sole difference from the corresponding incoming parent is

    old b = c*(T+alpha)-R;   new b = c*T-R.

Thus, as a free polynomial identity over the integers,

    P_new(T)=P_parent(T-alpha).                         (1)

This identity alone is insufficient to establish equivalence over positive
integers: `T-alpha` might initially be nonpositive. The proof below shows
that every positive zero of `P_new` forces `T>alpha`.

## 2. Root extraction and folding allow either sign of V

Throughout Sections 2-5 assume a positive input with `P=0`, but assume no
sign for `B`, `C`, `b`, `V`, `R`, or `e` until it is proved.

The unchanged initial estimates give `q>=32`, `X>=q`, `Y>=q^3`, `k>=2`,
`c>=3`, `A>=3`, `Delta>=8`, `U>=c^2`, `Fsqr>c+1`, `Q>1`, and `M>0`.
For every integer b, `V=Fsqr*b-c` is nonzero because `0<c<Fsqr`.
Consequently `Q*V^2-1>0`.

Write, in the proof only,

    delta=Q-1, z=Z/M, kappa=Kpos/H,
    rho=e/D, t=B/h, W=1+h*L.

The output equation and the carrier give the exact rational identities

    delta*z^2=G*(Q*V^2-1),
    z=n+kappa-W*t-rho.                                 (2)

The identities

    Fsqr=(1+2a)^2, Q=4*Delta^2*U^2*G

make G coprime to both `Q-1` and `Q*V^2-1`. Prime valuations in (2) force
G to be a positive integer square `g^2`. Since `F0=1 mod E`, its coprime
positive factors are separately squares:

    E=tau^2, F0=f0^2, g=tau*f0.

The rational adjacent-Pell descent from the parent, which uses `|V|` and
does not require `V>0`, gives a positive integer y such that

    Q*V^2-(Q-1)*y^2=1, z=epsilon*g*y,
    epsilon in {-1,1}.                                 (3)

Set `f=1+2a` and `I=2U*g`. Then

    f^2=Fsqr, f^2-Delta*I^2=1,
    Q=(Delta*I)^2, c^2 divides I, c<=I.                 (4)

The all-index folding lemma applies to the strong Pell equation, (3), and
`V=-c mod f`; its statement explicitly permits V to be a signed integer.
It yields `c=psi_A(p)` for an odd integer `p>=1`. For completeness, oddness
comes from classifying `(Delta*I*|V|,y)` at an odd auxiliary Pell index and
folding that index modulo twice the strong Pell index: both reduction and
reflection preserve its parity. The precise original signed folding proof
is retained in `folding_source.md`, Section 2.

The first norm has the standard classification

    k=2*psi_P0(n0), P0=2*X*Y^2+1, n0>=1.              (5)

Here `psi_D(j)` is the Pell ordinate defined by
`chi_D(j)+psi_D(j)*sqrt(D^2-1)=(D+sqrt(D^2-1))^j`.
If `n0=1`, then k=2 and the positive inputs force eta=zeta=1, so
`c=2Y+1` lies strictly between `psi_A(1)=1` and `psi_A(2)=2A`. This is
impossible. Therefore

    n0>=2, k>=8*X*Y^2+4, c>kY>8*X*Y^3.               (6)

In particular c>X and `Kpos>0`, hence `kappa>0`. Also `p=1` is impossible
because c>=3.

## 3. A low-index exclusion from shared divisibility

We show `p!=3` before knowing the sign of B. Suppose `p=3`. Then

    c=4*A^2-1.

If `n0>=3`, (5) implies

    k>=8*P0^2-2>32*X^2*Y^4.

Since `A=Y(X+1)+1<2XY`, we have `c<16X^2Y^2`. This contradicts
`c>kY>32X^2Y^5`. Thus `n0=2`, and `k=4P0=8XY^2+4`.

Two exact identities now give a strict interval:

    2c-(X+2)k = 8Y^2+16Y(X+1)-4X-2 > 0,
    (X+3)k-2c = 8Y[(X-1)Y-2(X+1)]+4X+6 > 0.

The first inequality holds for X,Y>=1; the second holds for X>=3,Y>=4,
as it does here. Hence

    (X+2)/2 < c/k < (X+3)/2.

On the other hand, `c=kY+eta` and `0<eta<k` imply `Y<c/k<Y+1`.
Combining the intervals yields

    0 < 2Y-X < 3.

But q divides both X and Y, and q>=32, a contradiction. Thus the folded
odd main index obeys

    p>=5, c>psi_A(3)=4Delta+3.                         (7)

This argument is independent of the native machine constants beyond the
simple inequalities already stated. More generally, it excludes main index
three whenever X>=3, Y>=4, and X,Y share a divisor at least three in this
Pell quotient strip.

## 4. Both signs of b satisfy a strong transport bound

Set `S=Delta*I`, so `Q=S^2`. Classify the positive Pell pair in (3):

    S*|V|=chi_S(j), y=psi_S(j), j>=1.

An even j would give `chi_S(j)=+1 or -1 mod S`, impossible since S divides
the left side and S>=2. Thus j is odd. The case j=0 has already been
excluded by `y>0`, and would also fail the same divisibility condition.

We have

    f^2=1+Delta*I^2>c+4Delta+3.                       (8)

Indeed `I>=c^2`, `Delta>=8`, and c>=3 imply
`Delta(c^4-4)>c+2`. If `j=1`, then `V=epsilon_v` for a sign
`epsilon_v`, so `f^2*b=c+epsilon_v`, whose right side lies strictly
between zero and `f^2`, impossible for an integer b.

If `j=3`, then `V=epsilon_v*(4Q-3)`. The exact equality becomes

    f^2*(b-4*epsilon_v*Delta)=c-epsilon_v*(4Delta+3).

For `epsilon_v=1`, (7) makes the right side strictly between zero and
`f^2`. For `epsilon_v=-1`, the same conclusion follows from (8). Both
cases are impossible. Therefore j>=5 and

    v:=|V|>=16Q^2-20Q+5>8Q^2.                         (9)

Since `c<f^2<Q` and `f^2>=3`, we obtain

    |b|=|V+c|/f^2 >= (v-c)/f^2
        > (8Q^2-Q)/f^2
        = Delta*(1-1/f^2)*(8Q-1)
        >= (2Delta/3)*(8Q-1)
        > 4Delta*Q = 4Delta^3*I^2 > 4g.               (10)

The last inequality uses `I=2U*g`, with U,g positive. In particular b is
nonzero. Since `0<c<f^2-1`, the equation `V=f^2*b-c` shows that V has the
same sign as b and `v>|b|`.

Also (3) implies `y<3v/2` because `Q>=4`. It follows that both allowed
weights are positive and obey

    L=V^2 or L=bV=|b|v,       g*y < L/2.              (11)

For bV use `|b|>4g` in (10); for V-squared use `v>|b|>4g`.
No prior positive orientation of b or V has been used.

## 5. Recover the signs and then recover the deleted shift

The identity

    b-e=cT-k+1>0

uses only T>=1 and `c>k`, so `rho<b/D`, including when b is negative.
If `B<=-1`, then `Wt=(1+hL)B/h<=-L-1/h`. Combining (2), (3), (11), and
`kappa>0`,

    n=epsilon*g*y-kappa+Wt+rho < -L/2+b/D < 0.

For the final inequality, if b<0 it is immediate. If b>0, then D>2 and
L>b give `b/D<L/2`. This contradicts the positive input n. Consequently

    B>=0, C>0, F+alpha<q, alpha<q.                    (12)

The fixed mask box gives `0<R<q^4`. This can also be checked directly:
put `r=q-F`; then `1<=alpha<=r-1`, `r<=q-1`, and

    h*r+alpha <= q*r-1 <= q^2-q-1,
    0<(MC+q*MF)J<(q-1)(2q+1).

Thus `R<q^4-q^3<q^4`. By (6), `c>8XY^3>=8q^10>2q^4`.
Hence, with the new positive input T,

    b=cT-R>=c-R>c/2>0.                               (13)

The strong product square further gives

    g^2=E+Delta*U^2*E^2 > (A-1)^2*U^2*E^2,
    g/c > (A-1)c >= q.

Now (10), (12), (13), and R>0 imply

    T=(b+R)/c > b/c >4g/c >q>alpha.                  (14)

All statements needed for positive orientation have now been established
without assuming them earlier. The integer `T_parent=T-alpha` is strictly
positive. Every other input is unchanged, and (1) says that these inputs
form a zero of the matched parent equation. Its retained soundness theorem
therefore gives a finite syntactic ZFC refutation.

## 6. Completeness and an actual bijection

For any positive zero of the parent, set

    T_new=T_parent+alpha,

and retain all other coordinates. This is positive, and (1) makes the new
polynomial vanish. Conversely (14) permits the positive inverse
`T_parent=T_new-alpha` at every new positive zero. The two triangular maps
are inverse. Thus each pair has a bijection between its entire positive zero
sets; no assumption of consistency or inconsistency is used to prove this.

The parent's complete positive-witness construction and its identified
native/compiler/refutation calibration now transfer without alteration.
The ordinary arguments are elementary number theory and finite syntactic
reasoning formalizable in ZFC. This proves the claimed ZFC-provable
equivalence, with the same inherited calibration boundary as the parent.

## 7. Exact degrees and finite verification

Deleting the single register `Tp=T+alpha` and using T directly removes
exactly one live addition. Every other live operation is retained. The two
new operation breakdowns are `(46 multiplications,17 additions,14
subtractions)` and `(47,17,14)`.

Let `q0=beta*J` and `k0=eta+zeta`. The entire leading homogeneous forms are

    2^14*q0^382*w^46*s^112*i^20*k0^64*T^4*(q0-F-alpha)^2,
    -2^10*q0^288*w^34*s^84*i^14*k0^46*T^2,

of total degrees 630 and 468. They have respectively 390 and 47 collected
terms. These are counts for the leading forms only, not for the fully
expanded polynomials. The coefficients of

    J^382*w^46*s^112*i^20*eta^64*T^4*F^2,
    J^288*w^34*s^84*i^14*eta^46*T^2

are `2^14*beta^382` and `-2^10*beta^288`, so neither leading form vanishes
at the actual fixed positive beta.

`verify.py` checks 28 exact free-polynomial cut identities per equation,
covering every actual register; propagates the full leading forms; checks
liveness, costs, and coefficients; reconstructs all four fixed numerals;
checks the new low-index identities; and rejects ten actual algebraic
mutations per equation. `build.py --check` independently reproduces the
literal changed data from the retained parent data. These finite checks do
not replace the unbounded Pell and sign proofs above. The symbolic checker
is adapted, with attribution, from the retained parent checker, and does not
import the producer.

## 8. Source and proof boundary

`upstream/` retains the incoming compact component byte for byte, including
its coefficient payloads, finite reconstruction code, proofs, licenses and
source seals. `folding_source.md` additionally contains the explicit signed
folding lemma used in Section 2. `UPSTREAM_PINS.json` binds the incoming
archive, repository commit and every retained file.

The inherited endpoint is the parent's ordinary theorem for the whole
indexed BFS943 tuple, ultimately using the native compiler and K215
refutation calibration. This component does not change that encoding. Its
new contribution is the signed proof permitting shift deletion and the two
resulting smaller circuits. All new work was prepared with AI assistance.
