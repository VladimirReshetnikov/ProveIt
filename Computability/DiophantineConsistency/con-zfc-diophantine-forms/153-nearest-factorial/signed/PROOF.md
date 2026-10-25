# Rebase the first index at its full available modulus

Prepared with AI assistance, 25 October 2026. Comparison snapshot:
`3ecd6a6cf53d47519228328567f45fb7ee9781d9` of VladimirReshetnikov/ProveIt.

## Results and exact scope

The following ordinary polynomials have unrestricted integer unknowns. The
files are finite arithmetic DAGs whose leaves are precisely the listed
unknowns, fixed integer literals and the six completely supplied coefficient
integers. Intermediate registers introduce no unknowns.

| Literal equation | Unknowns | Exact total degree | Live binary operations |
|---|---:|---:|---:|
| `integer14_degree82.json` | 14 | 82 | 113 |
| `integer14_degree90.json` | 14 | 90 | 111 |
| `integer13_degree152.json` | 13 | 152 | 126 |
| `integer11_degree298.json` | 11 | 298 | 150 |

The matched incoming degrees/costs are 86/112, 94/110, 156/125 and 300/148,
respectively. The new points trade a small evaluator-cost increase for lower
degree. These are not global minimality results or a claim that their
coefficients are small. All six coefficients, their full bytes, finite recipe,
and retained source proofs are included. The ordinary proofs compose with the
identified inherited native/compiler/syntactic-refutation calibration to prove
in ZFC that absence of integer zeros is equivalent to Con(ZFC). This is not a
new end-to-end Lean/Rocq certificate and asserts neither consistency nor actual
unsolvability.

The principal mathematical change is to use a larger first-index modulus
already supplied by the same Pell recurrence. It permits a weaker magnitude
guard. The eleven-variable endpoint also adds one more integral polynomial
term to the earlier whole-expression center.

## 1. Common front and the changed fifteen-integer kernel

Let `beta,K0,MC,MF,cone_A,cone_B` be the fixed source34 tuple in
`coefficients/BINDING.json`. In particular

    beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104.

MF is the already shifted source value. No tuple is mixed with any other
native encoding. Use fifteen unrestricted integer inputs

    j,C,z,h,r,v,w,T,c,n,f,y,p1,p2,p3.

Define polynomial abbreviations

    J=6j+1, qm=beta*J, q=qm+1, W=12w+4, X=qW, Y=v,
    F=(K0+W)C-z qm,
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    ell=XY^2, k=R+1+h ell, eta=c-Yk, L=ell k,
    I=(2r+1)c^2, Q=Delta(f^2-1), V=f^2(cT-R)-c,
    M=2q^3, U=MH, Klo=X(2X-3c)-2,
    Z=Un+M Klo+H(Y-q^3),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    B0=k^2(q^2-Derr)-4q^2 eta^2,
    Budget6=Y^2 B0-k^2 q^6.

The four residuals are

    Acar=(Z+Uk)^2+4U(LZ-U),
    Bstrong=f^2-Delta I^2-1,
    Caux=V^2-(Q-1)y(2V+y)-1,
    Gguard=Budget6-1-p1^2-p2^2-p3(p3+1).

The comparison source used `k=R+1+hE` and `Budget8=Y^2 B0-k^2 q^8`.
Everything else is unchanged; `E(Yk)=ell k` is an exact identity.

The changed kernel is the simultaneous vanishing of the four displayed
residuals, equivalently the zero of their sum of squares. The three
fourteen/thirteen-variable reductions below are pointwise exact reductions
of this changed kernel. Its semantic calibration is proved next.

## 2. What the weaker guard proves before any Pell interpretation

The affine restrictions and authentic coefficients give q even,
q=2 modulo3, q nonzero, |q|>=16, X=0 modulo8, X=2 modulo3, and
|X|>=4|q|. H is odd and nonzero, so U is nonzero. Also Delta>=3.
These statements are unconditional, as in the retained source proofs.

At a kernel zero, the positive ternary representation gives Budget6>0.
Thus k and Y are nonzero and

    Y^2 B0 > k^2 q^6 > 0,    B0>0.

Since B0<=k^2 q^2, it follows that

    |Y|>|q|^2.                                           (2.1)

The ordinary centered-disk argument from B0>0 gives

    Derr<q^2, |eta/k|<1/2,
    F,C,q-F-C have q's common strict sign,
    |k|(|Y|-1/2)<|c|<|k|(|Y|+1/2),
    sign(c)=sign(kY).

Consequently c is nonzero. The same authentic mask lemma then gives,
writing q0=|q|,

    q0(q0^2-1)<R<q0^4-2.                                 (2.2)

Unlike the old proof, we do not need |XY|>3R+1. Put x=|X|, m=|Y|. The
larger available modulus satisfies

    |ell|=x m^2 >4q0^5 >3R+1.                            (2.3)

The middle inequality uses (2.1) and x>=4q0; the last follows at once
from (2.2) and q0>=16. No cubic-scale divisibility or main power-of-two
projection has been used.

## 3. First-index congruence and the signed bootstrap

The carrier residual has the same monic rational-root interpretation as
before. Dividing Acar=0 by U^2 gives

    (Z/U)^2+2(2L+k)(Z/U)+k^2-4=0.

Thus Z/U is integral. Its parity implies an integral square root of
`1+L(L+k)=1+ell(ell+1)k^2`. It also gives

    M | H(Y-q^3),  H | M Klo.

Since H is odd, the first relation implies Y is even. No cancellation
through a nonunit modulo H or M has occurred.

Let B=|A| and P=|2ell+1|. The unchanged strong and auxiliary equations
and absolute folding give integers p,n0>=1 with

    |c|=psi_B(p),   |k|=2 psi_P(n0),

where psi_b is the Pell ordinate sequence psi_b(0)=0, psi_b(1)=1,
psi_b(t+2)=2b psi_b(t+1)-psi_b(t). These are exactly the classification
and folding lemmas retained in `inherited/roots_baseline/source/02_PROOF.md`
and `06_PROOF.md`. Their preconditions are Delta=B^2-1, c!=0,
I=(2r+1)c^2, f^2-Delta I^2=1, c^2|I, and the two literal residues of V.
Neither lemma requires the old magnitude |Y|>|q|^3.

Here P>B because x>=64 and m>q0^2>=256. For example
P>=2xm^2-1 whereas B<=m(x+1)+2. Since |c|>|k|, monotonicity gives p>n0:
if n0>=p then |k|/2=psi_P(n0)>=psi_B(p)=|c|, a contradiction.

The recurrence supplies the stronger congruence we now use. For every
integer ell and every natural n,

    psi_(2ell+1)(n)=n modulo 2ell.                       (3.1)

This follows by induction from the recurrence, reducing its parameter to
1 modulo 2ell. The signed version at P=|2ell+1|, with ell's sign equal
to X's, gives

    epsilon*2n0=R+1 modulo |ell|,
    epsilon=sign(k)*sign(X)^(n0-1).                     (3.2)

Indeed k=R+1+h ell is literal. If epsilon=+1, (2.3) and (3.2) force
n0>=(R+1)/2. If epsilon=-1, the positive integer 2n0+R+1 is a nonzero
multiple of |ell|, hence greater than 3R+1, so n0>R. This is the exact
index lower bound required by the old signed proof, now obtained from
|ell| rather than |E|.

Thus p>n0>=24, and ordinary Pell growth yields |c|>2p, |c|>2R and the
other old large-ordinate bound. The normalized strong-rank lemma and the
signed auxiliary step-down now apply without changes; they give p=R.
Their elementary mechanisms are recorded in `06_PROOF.md`, Sections 2 and
4: c^2|I implies c divides the strong index, and the two auxiliary
congruences imply p=plus or minus R modulo c; the strict bounds eliminate
wrapping. The negative branch in (3.2) is now impossible because p=R>n0.
The positive branch has both indices below |ell| and therefore gives

    2n0=R+1,   R=2t+1,   t>=24.                        (3.3)

Only the first-index modulus has changed. The signed ratio proof uses
x>=64, m>=6, (3.3), the same main/first Pell parameters, and
|c/k|<m+1. It yields

    m>(x-3)^t/2-1,   |H|>x(x-3)^t.

All these hypotheses have been established in the new order.

## 4. Source restoration and completeness

The original whole-product proof is now applicable verbatim. The early
divisibility H|M Klo implies H|q^3 Kq for

    Kq=X(X+2ac)-1,
    2Kq-Klo=HXc.

The Pell projector and the just-proved ratio bound force
`sign(c) X=2^R`. Congruences modulo3 give c>0 and X=2^R; the surviving
first-index branch and centered strip then give k,Y>0. Exact projection
gives H|Klo. Returning to M|H(Y-q^3) and cancelling the integer H after
substituting Klo/H into Z/U recovers

    Y=(2v_scale+1)q^3,

with v_scale integral. The uniform centered half-binomial argument gives
0<eta/k<1/4. These statements precede the handoff to the native compiler.

**Precise predecessor map.** A new zero need not have Budget8>0. We do
not map it to the old free-scale degree44 kernel with that stronger guard.
Instead restore the earlier B0-only degree48 kernel described in
`inherited/roots_baseline/source/FREE_SCALE15_PROOF.md`, Section 6.
Keep the other arithmetic coordinates and set

    h_old=Y*h_new,   v_old=Y/q,
    g=Klo/H,  t_carrier=Z/U,
    n_old=t_carrier-g-v_scale.

These are integers, and

    R+1+h_old XY=R+1+h_new XY^2=k.

The old scale is q*v_old=Y and its centered carrier ratio is t_carrier.
Its strong and auxiliary residuals are unchanged. Its B0-only guard is
restored using a fresh positive ternary representation of the already
proved integer B0>0. This is a literal zero of that earlier calibrated
source, to which the retained native/refutation theorem applies.

Conversely, a finite refutation supplies the same canonical outer source
data. Let ell=XY^2>0 and n0=(R+1)/2. The canonical first Pell value is

    k=2 psi_(2ell+1)(n0).

By (3.1), 4ell divides k-2n0=k-R-1. Therefore the new

    h=(k-R-1)/ell

is an integer. This choice preserves the entire canonical k, c, Y, first
norm, strong pair and auxiliary pair. The old canonical family already
has Budget8>0. Since q>=16,

    Budget6=Budget8+k^2(q^8-q^6)>Budget8>0.

Choose a fresh ternary representation of Budget6. All changed-kernel
residuals vanish. This proves both directions of zero existence; no
identity between the old and new full zero sets is asserted.

## 5. The fourteen- and thirteen-variable final equations

### 5.1 Fourteen variables, degree82

Take inputs

    j,C,z,h,r,v,w,T,c,n,f,p2,p1,s.

Use the common front but remove y and p3. Put

    Bg=Budget6-p1^2-p2^2, G=4Bg-3,
    delta=Q-1, Cy=QV^2-1,
    K=delta[s(s+1)-Bg+1]-Cy,
    N=K^2-G delta Cy, Sunit=f^2-Delta I^2,
    P82=(Acar+1) Sunit (N+1)-1.

At an integer zero all three factors are units. Since Acar is a square
modulo4, Acar+1 cannot be -1. Since Delta is 0 or3 modulo4, Sunit
cannot be -1. Hence Acar=0, Sunit=1 and N=0.

The exact primitive odd-carrier identity is the retained lemma

    [d(s(s+1)-b)-e]^2-(4b+1)de=0
    iff there exist integers g,u with
    g^2=4b+1, d u^2=e, 2s+1=g+2u,                    (5.1)

for d!=0. Its proof comes from

    16N=[d((2s+1)^2+4b+1)-4e]^2
          -4d^2(2s+1)^2(4b+1).

The forced rational square root of 4b+1 is integral and odd; division
by2 then restores u. Here d=delta is nonzero because Sunit=1 makes
Q=Delta^2 I^2, which is either0 or at least9. Apply (5.1) with
b=Bg-1, e=Cy. Restore p3=(g-1)/2 and y=u-V. The four changed-kernel
residuals vanish. Conversely any changed-kernel zero gives a P82 zero
by s=p3+V+y. Thus this is a pointwise algebraic equivalence with the
changed kernel proved above.

### 5.2 Fourteen variables, degree90

Use inputs `j,C,z,h,r,v,w,T,c,n,y,p1,p2,s`. Eliminate f by

    Ds=Delta I^2, Fs=1+Ds, Q=Delta Ds, V=Fs(cT-R)-c.

Define Bg,G as above and

    K=s(s+1)-Bg-Ds, N=K^2-G Fs,
    Aunit=V^2-(Q-1)y(2V+y),
    P90=(Acar+1)(N+1)Aunit-1.

Fs is positive and is0 or1 modulo4. Since G=1 modulo4, N cannot be
-2. The unit-product argument gives Acar=N=0, Aunit=1. Apply (5.1)
with b=Bg-1,d=1,e=Fs to restore integer f with f^2=Fs and p3 from the
odd root. Conversely set s=p3+f at any changed-kernel zero. The
pointwise equivalence follows exactly as in the retained primitive proof.

### 5.3 Thirteen variables, degree152

Use `j,C,z,h,r,v,w,T,c,n,y,p1,p2` and the same Fs,Q,V. Put

    G=4(Budget6-p1^2-p2^2)-3,
    Dt=1+L(L+k), U2=U^2,
    ga=U2 G, db=4U2 Dt, fc=16U2 Fs, gc=ga+fc,
    K=(Acar-gc)^2-4(ga fc+db gc),
    N=K^2-64 ga db fc(Acar+db),
    Aunit=V^2-(Q-1)y(2V+y), P152=(N+1)Aunit-1.

The unchanged parity-separated three-root lemma in
`inherited/roots_baseline/thirteen/PROOF.md` applies for every value of
the new k and Budget6. Its unconditional prerequisites are U!=0,
Dt>=1 odd, Fs>=1, and G=1 modulo4. These hold here. It extracts
integer roots of G, Dt and Fs with weights1,2,4; restores f,p3 and an
integral translate of n; and proves exact zero-existence equivalence
with the changed fifteen-variable kernel. No old magnitude guard is
used by that purely algebraic merger.

## 6. Eleven variables and a further center correction

Use inputs `j,C,z,h,r,v,w,T,c,n,s`, the same front through Budget6, and
the complete linear-cofactor construction of
`inherited/scalar_source/LINEAR_COFACTOR_ROUND17_PROOF.md`. In explicit
polynomial abbreviations its additional quantities are

    D=Budget6-4, Dt=1+ell(ell+1)k^2,
    Dg=1+D Dt s^2, Pg=Dt Dg,
    Dm=1+Delta c^2, B=r A Dm, Us=r c^2 Dm,
    I2=c^4 B=A c^2 Us,
    Df=1+Delta I2, Q=Delta^2 I2, delta=Q-1,
    V=Df(c-R+4A Us T)-c, Cy=QV^2-1,
    Kpos=X(3c-2X)+2, M=2q^3, Dc=HM,
    S=srH M^5, zc=Dc T+M Kpos+H(v-q^3),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3).

Here Us is called U in the actual JSON. The new center is

    Psi=[(32Delta+16)Us-4r c^4]V
       +Us^2 T[8Us(c^2-2)+64A^3+r c^4(3c^2-16)].

Compared with the incoming degree300 center, this is the additional
polynomial term `-16r c^4 Us^2 T`. Finally define

    Z=S(n+Psi)-Ac,
    pa=delta Z^2, pb=delta S^2 Pg, pc=1024 S^2 B Df Cy,
    P298=(pa+pb-pc)^2-4pa pb.

The even-weight norm proof, squareclass separation, coprime extraction,
adjacent-coefficient integrality descent, and carrier valuation arguments
are unchanged. In particular the old modulo16 calculation still gives

    D=8 or12 modulo16,

because both q^8 and q^6 are divisible by16 and the new ell is still
a multiple of8. No sign or zero-case assertion is lost. From a zero
the old algebra recovers Pg as a positive square, B=u^2, Df=f^2 and
the integral auxiliary root, then Budget6>=12 and the centered signs.
Sections2--3 of this note replace the old magnitude/index paragraph.
The same fifth-power carrier and whole-product argument recover the
native endpoint. Its stronger bound uses the already authentic enormous
|X| and the same p=R and n0=(R+1)/2, and therefore remains valid.
At the final scalar Q41/native handoff, explicitly set
`h_old=Y*h_new`, as in Section4, so that the retained source computes
`R+1+h_old*XY=R+1+h_new*XY^2=k`; the other restored outer coordinates
and fresh strong witnesses follow the retained scalar construction.

For completeness the canonical outer source has integral new h as above
and Budget6>Budget8>64. Choose a Pell guard pair for D Dt; then choose
one fixed strong pair divisible by the retained required modulus, form
u,r, choose the intersective-quintic residue, and interpolate the same
fixed strong pair. The source's choice order and supported-modulus
theorem are unchanged. Its last coordinate is now

    n=Ac/S+32u f y+tau g-Psi,

which is integral. Thus one factor of the new norm vanishes. In particular
there is no demand that old guard coordinates survive unchanged or that a
strong pair be reselected after interpolation.

## 7. Exact degrees

The new budget has degree16. Let the following denote highest homogeneous
forms in the actual variables, with all coefficient ports degree zero:

    q0=6 beta j, X0=12q0 w, Y0=v,
    F0=12wC-q0 z, R0=-q0^3 F0,
    ell0=X0Y0^2, k0=R0+h ell0, a0=X0Y0,
    T0=cone_A^2 Y0^2 F0^2+4q0^2Y0^4+q0^6.

Then `[Budget6]_16=-k0^2 T0`, a nonzero polynomial. This explicitly
accounts for the new top-degree contribution from h; the old assertion
that k's entire leading form is R0 is no longer used.

For P82 the degrees of Acar,Sunit,N are22,12,48, giving82. A nonzero
actual coefficient is

    [j^47 w^9 v^10 z^5 f^4 r^2 c^4 n] P82
        =-2^75 3^56 beta^47.

For P90 the norm N has degree32 and Aunit degree36, giving22+32+36=90.
For P152 the three scaled radicands ga,db,fc have degrees28,30,24.
Thus K has degree58, N has degree116, and Aunit degree36, giving152.
The independent checker propagates an attained actual coefficient through
every gate of these three circuits and records all of them.

For P298 give independent variables (A,c,r,T,R) weights (3,1,1,1,5).
Set Delta=A^2-1 and use the exact definitions of B,Us,Df,Q,V and Psi.
The two exact remainders are

    Dcenter=Psi^2-1024 B Df V^2,
    Ecenter=(Q-1)Dcenter-1024 B Df(V^2-1).

Their respective exact weighted degrees are80 and108. Their complete
highest weighted forms are

    [Dcenter]_80 = 512 A^15 c^24 r^5 T R
                 +8192 A^17 c^22 r^5 T^2
                 -4096 A^16 c^24 r^6 T^2,
    [Ecenter]_108 = 512 A^22 c^30 r^6 T R
                  -8192 A^24 c^28 r^6 T^2
                  -4096 A^23 c^30 r^7 T^2.

Every coefficient of both remainders is supplied in center_remainder.json
and independently re-expanded in check.py. With W0=Sn-Ac, the exact cut is

    pa+pb-pc=delta W0^2+2delta S Psi W0+delta S^2 Pg
                +S^2 Ecenter.

The first three terms have degrees at most98,137,122. The last has degree
148. Thus its square has degree296. In contrast, pa has degree176 and
pb degree122, so the correction `-4pa pb` has exact degree298 and cannot
cancel. An explicit actual coefficient is

    [j^136 w^46 v^50 z^6 s^6 r^12 c^40 T^2] P298
        =2^272 3^182 beta^136.

Each displayed exponent sum equals the corresponding degree. Both
coefficients are nonzero for the supplied fixed positive beta. The final
circuits, not numerical samples on a line, are checked at these cuts.

## 8. Verification and remaining boundary

Run `python3 -B build.py` to reproduce the four DAGs and `python3 -B check.py`
or `python3 -B -O check.py` to verify. The checker does not import the
producer. It authenticates retained source bytes, reconstructs all fixed
coefficients from their finite recipe, proves the changed guard identity
in a free polynomial ring, checks every circuit register against its
definition, recounts all live operations, proves attained actual degrees,
and rejects targeted corruptions of the new index, budget and center.

These finite checks verify transcription and algebra. The unbounded proof
is Sections2--6 with the explicitly retained signed-Pell, interpolation
and native/refutation inputs. They do not solve the equations or replace
those inputs with finite evidence. The new contribution is this proved
composition and its literal lower-degree polynomials, not priority for
Pell congruences, the primitive norm identity, or polynomial shears in
general.
