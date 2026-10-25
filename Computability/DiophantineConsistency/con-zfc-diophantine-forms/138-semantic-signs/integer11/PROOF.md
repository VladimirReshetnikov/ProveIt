# Parity and main-root saturation in eleven integer variables

This component composes two independently supplied reductions that were not
combined in the inspected snapshot. Package 132 saturates by the main
radicand; package 131 removes unnecessary scalar factors from the sign
guard by a modulo-sixteen argument. Their hypotheses are compatible.
The product-square evaluator from package 133 then saves one more operation.
The resulting equations use eleven unrestricted integer variables and have
degree/operation pairs **924/107** and **840/108**. The matched package-132
parents have 924/109 and 840/110. These are two-operation improvements at
unchanged variable count, degree, and complete fixed-coefficient tuple.

The result is a new composition of identified existing ideas, not a claim
of priority for the parity argument or the elementary finalizer identity.

## Literal definition

The unknowns j,C,z,h,r,v,w,T,c,n,s range independently over Z. The six fixed
integers beta,K0,MC,MF,cone_A,cone_B are exactly the source34 tuple supplied
in coefficients/. They are constants, not existential variables.
In particular beta=2^1064921-1, cone_A=2^1113 and cone_B=2^666104.
The complete finite coefficient recipe and compressed integer bytes are
included, with their original binding and hashes.

Define the following polynomial abbreviations:

    J=6j+1, q=beta J+1, W=12w+4,
    X=qW, Y=(2v+1)q^3, E=XY,
    a=E+Y, A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    M_index=E                  [native],
    M_index=4q^4               [short],
    k=R+1+h M_index, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2,
    L=XY^2 k, Dt=1+L(L+k), D=Budget-4,
    P=Dt+D(Dt s)^2,
    Dm=1+Delta c^2, BP=Dm P, U=A r c^2,
    Df=1+Delta U^2 BP, Q=Delta^2 U^2 BP,
    V=Df(c-R+4U BP T)-c,
    K=X(3c-2X)+2,
    S=srH, zc=HT+K,
    Ac=(zc^2+3H^2)(zc^3-19H^3), Z=Sn-Ac,
    RG=S^2 BP Df.

The final equation is

    Q(Z^2-RG V^2)+(RG-Z^2)=0.                         (1)

All abbreviations are polynomial expressions and all exponents are fixed.
The canonical DAGs give every binary arithmetic operation. Their order is
topological and all nodes are live. There is no implicit division,
square-root operation, extra coefficient port, or unspecified witness.

## The new compatibility argument

Write Uc=cone_A F and Vc=cone_B C. The actual coefficient tuple and affine
front imply q even and Uc,Vc divisible by sixteen. Thus

    Budget+(qk)^2
       =k^2[2q(Uc+Vc)-Uc^2-Vc^2]-4q^2 eta^2
       =0 modulo 16.

An even square is zero or four modulo sixteen. Hence Budget is zero or
twelve modulo sixteen and

    D=Budget-4 is 12 or 8 modulo 16.                  (2)

Consequently D is divisible by four and is never a square. Let ell=XY^2.
Since X is a multiple of eight, ell is a multiple of eight and
Dt=1+ell(ell+1)k^2 is positive and one modulo eight. Therefore

    Dg=1+D Dt s^2 is 1 modulo 4,
    P=Dt Dg is nonzero and 1 modulo 4.                (3)

This replaces package 132's D_old=3Budget-4 and its forced factor four in
the guard. The new guard remains positive and nonsquare when the
completeness proof needs a Pell equation. It also has all the nonzero
properties required before sign recovery.

## Soundness, without circular sign assumptions

For proof notation put delta=Q-1, Cy=QV^2-1 and Da=delta Cy. The identity

    Q(Z^2-RG V^2)+(RG-Z^2)
      =(Q-1)Z^2-RG(QV^2-1)                           (4)

shows that (1) is the same product-square final relation as package 132,
with the new P. The affine front gives Delta>1, A nonzero even, H odd
and nonzero, and Dm>0. By (3), BP is nonzero. Df cannot vanish: if U=0 it
equals one, and otherwise its nonconstant summand has absolute value
greater than one. Similarly delta and Cy are nonzero.

The polynomial pi(t)=(t^2+3)(t^3-19) has no rational root. Since
Ac=H^5 pi(T+K/H), Ac is nonzero. If S=0, equation (4) would reduce to
delta Ac^2=0, a contradiction. Thus s and r are nonzero at every zero.

The three integers BP,Df,Da are pairwise coprime. Indeed Df is one modulo
BP and Da is one modulo BP. Modulo Df, direct reduction gives

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm,
    Da=A^2 Dm.

Since A divides U and Dm divides BP, Df is one modulo A and modulo Dm.
This proves the last coprimality assertion without using any signs.
Multiplying (4) by delta gives

    (delta Z/S)^2=BP Df Da.                           (5)

A rational number with integral square is integral. Prime factorization
and pairwise coprimality show that the absolute values of all three
factors are squares. Because A is even, Delta U^2 is divisible by four;
Df is one modulo four, so it cannot be a negative square. Thus Df>0.
If c is nonzero, U is nonzero and BP<0 would make Df<0. If c=0, then
Dm=Df=1 and Da=1, so (5) itself gives BP=P>0. Hence BP>0 in all cases,
P>0, and Da>0. We have positive integers p0,f,e with

    p0^2=BP, f^2=Df, e^2=Da.                         (6)

Since Dt>0 and P=Dt Dg>0, Dg>0. If Budget<=3, then D<=-1 and s!=0 would
give Dg<=1-Dt<=0. Therefore Budget>=4; by (2), in fact Budget>=12.
The centered budget now yields k!=0, Derr<q^2, common strict signs of
q,F,C,q-F-C, and |c/k-Y|<1/2. At c=0 its defining expression is
k^2(q^2-Derr-4q^2Y^2)<=0, so c is nonzero. These arguments recover all
necessary signs before Pell classification.

Define I=U p0 and T_old=p0 T. Then c^2 divides I, |I|>=|c|, and

    f^2-Delta I^2=1,
    Q=(Delta I)^2,
    V=f^2(c-R+4I T_old)-c.

The adjacent-Pell descent from the retained parent proof makes
y=e/delta integral. The early folding theorem uses only these strong
and auxiliary norms and the bound |c|<=|I|; it supplies Dm=d^2 before
the first Pell norm is used. Then P=(p0/d)^2 is an integer square.
Because gcd(Dt,Dg)=1 and both factors are positive, Dt and Dg are each
squares. The complete first/strong/auxiliary system of the calibrated
signed source has now been restored.

The remaining rank, projector and orientation arguments are identical
to package 132: the actual congruences V=-c modulo f and V=-R modulo c
hold; c^2 divides I; the main index is R; the native or short first-index
modulus gives the same first index; and the signed projector restores
X=2^R. Fresh original source witnesses are then reconstructed. None of
these later interfaces depends on the removed factors three or four in
the guard. The retained PARENT132_PROOF.md records their precise order
and full transitive dependencies are supplied under source/.

## Completeness with the new guard

Start with a finite refutation and take the parent's canonical outer
data. They have Dt=tau^2, Dm=d^2 and Budget>64. Now D>0 and, by (2), D
is nonsquare. The positive integer D Dt=D tau^2 is also nonsquare.
The classical Pell existence theorem supplies s,g>0 with

    g^2-D Dt s^2=1.

Thus P=(tau g)^2 and p0=d tau g is fixed. Choose the one strong Pell
pair with the parent's prescribed divisibility 4s A p0 c^2|I, set
r=I/(A p0 c^2), and keep that strong pair fixed. Supported-modulus
interpolation selects T_old divisible by p0 and in the required
intersective class modulo p0 s r. Put T=T_old/p0 and choose
n=Ac/S+p0 f y. This is exactly the parent's integral reverse map.
It relies on the support of p0 s r in I, not on a particular formula
for D. Thus every refutation yields a zero of (1).

Combining the two directions with the retained native calibration gives

    ZFC proves: (for all z in Z^11, (1) is nonzero) iff Con(ZFC).

This is an ordinary proof formalizable in ZFC, not a new proof-assistant
kernel object and not a proof of Con(ZFC).

## Counts, degree and verification

Replacing 12Budget-16 by Budget-4 saves one multiplication. The identical
finalizer (4) saves one additional operation. All multiplications by
fixed constants and all squares count as binary operations. The native
DAG has 66 multiplications, 24 additions and 17 subtractions, totaling
107; the short DAG has one additional multiplication, totaling 108.

The guard substitution multiplies the old leading part of P by 1/12;
it does not change its degree. The finalizer is an identity. The exact
degree therefore remains 924 or 840. The verifier independently tracks
every actual gate's leading monomial over the coefficient polynomial
ring and obtains a nonzero signed power of two and three times a power
of the authentic beta. It records the full leading monomial and
coefficient in CHECK.json. This proves attainment, rather than only
an upper bound or an evaluation on a sample point.

Run python3 -B verify.py and python3 -O -B verify.py. The checker uses
only the standard library. It verifies local free-polynomial identities,
all live gates and counts, exact leading forms, all six constant payloads
and their full finite reconstruction, the inherited dependency hashes,
and explicit corruption controls. Finite residue tests supplement the
unbounded argument (2); they are not its proof.
