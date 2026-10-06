# Integral quotient cores need not admit a unit pivot or cyclic basis

The quotient condition T in SL2(Z), with trace T=(trace P)^2-2, does
not guarantee a unit entry after a common integral basis change, a
unimodular companion basis, or even a rational triangularization. The
explicit family below disproves all three shortcuts while remaining
arbitrarily close to the identity in congruence subgroups.

This is a scoped obstruction to particular reductions of the fixed
two-input quotient core. It is not an arithmetic-circuit lower bound,
an obstruction to independent left/right basis changes, or a statement
that these matrices occur in the unmaterialized universal relator list.
An exact three-product schedule for this equal-diagonal family is also
given; it trades one multiplication for one addition and saves no total
operations in the present model. Root requested this bounded continuation
after the frozen10M+10A quotient-pair append.

## 1. An explicit family and the inherited quotient recipe

Let g>=3 and put

    p=g^2+1, h=g^2+2,
    P_g=[p,g;g*h,p].                                      (1)

Since p^2-g^2*h=1, P_g lies in SL2(Z). More explicitly, with

    U(g)=[1,g;0,1], L(g)=[1,0;g,1],

one has P_g=L(g)U(g)L(g). Also P_g=I2 modulo g. Thus taking g a multiple
of any chosen fixed congruence level retains that congruence. None of
this asserts membership in the particular frozen universal relator list.

Use exactly the representation S and integral right-quotient construction
of the preceding quotient-pair note. The primitive right invariant and
its row basis are, without any coordinate permutation,

    w=(1,0,-h)^T,
    V=[0,-1,0;h,0,1].                                    (2)

Indeed w0=(2g,0,-2gh), and the prescribed gcd/Bezout choice uses1 as
its first primitive coordinate. Take c=(1,0,0); then c*w=1 and the
integral section is

    J0=[0,0;-1,0;0,1], V*J0=I2.                          (3)

For verification directly from the fixed scalar formula,

    S(P_g^-1)=[p^2,2pg,g^2;
               pgh,p^2+g^2*h,pg;
               g^2*h^2,2pgh,p^2].                       (4)

Therefore the inherited quotient T_g=V*S(P_g^-1)*J0 is exactly

    a=2p^2-1, L=pg,
    T_g=[a,-L;-4hL,a].                                   (5)

Its determinant is a^2-4hL^2=1, and its trace is2a=(2p)^2-2, as
required. All displays are handwritten identities in the integer g;
no stored coefficient array or source program has been evaluated.

## 2. No unit entry in any common integral quotient basis

The matrix(5) is scalar modulo L:

    T_g=a I2 modulo L.                                   (6)

Every common quotient-basis change C in GL2(Z) preserves this identity,
since C and its inverse are integral:

    C T_g C^-1=a I2 modulo L.                            (7)

Now gcd(p,g)=1, and

    a=-1 modulo p, a=1 modulo g.                         (8)

Because p>=10 and g>=3, a cannot equal1 modulo L (reduce modulo p),
and cannot equal-1 modulo L (reduce modulo g). In every conjugate(7),
the off-diagonal entries are0 modulo L and the diagonal entries are a
modulo L. Thus no entry of any such conjugate equals+1 or-1.

For the small explicit case g=3,

    P_3=[10,3;33,10],
    T_3=[199,-30;-1320,199]=19 I2 modulo30.                (9)

Here199^2-30*1320=1 and trace T_3=398=20^2-2. The residue19 modulo30
is neither+1 nor-1. Equation(9) is therefore a counterexample to a
unit-pivot assertion even after an arbitrary common unimodular basis
change, not merely in the initially displayed basis.

**Remark 1 (refuted unit-pivot shortcut).** The tempting claim that the
integral SL2 quotient and its special trace always allow a unit entry
by a common integral basis change is false by(6)--(9). A Gaussian or
shear schedule relying on that premise is not a valid uniform schedule.
This does not forbid some other algorithm with fewer products, and does
not address independently changing the input and output bases: those
are different operations whose effects on the identity-side input and
all consumers must be charged. Smith reduction of one isolated matrix
does not prove a cheap substitution in t_+-T t_-.

## 3. The nonunit cyclic index and triangular obstruction

For any integer column v=(x,y)^T, direct expansion gives

    det[v,T_g v]=L*(y^2-4h*x^2).                         (10)

Every nonzero such determinant is divisible by L. Its minimum nonzero
absolute value is exactly L, achieved at v=e2; equivalently the gcd of
all these determinant values is L. Since L>=30, no pair(v,T_g v) is a
unimodular basis. The ordinary companion-basis conversion consequently
cannot be performed by a common GL2(Z) change for this family.

The characteristic discriminant is

    (trace T_g)^2-4=16 L^2 h.                            (11)

Here g^2<h=g^2+2<(g+1)^2, so h is not a square and(11) is not a rational
square. The characteristic polynomial is therefore irreducible over Q.
A rational upper- or lower-triangular matrix would have rational diagonal
eigenvalues, so T_g cannot be triangularized by a common rational basis
change either. This is stronger than an obstruction to a particular
integral triangularization algorithm.

**Remark 2 (refuted free companion conversion).** The fact that a rational
cyclic basis exists does not make its conversion an integer operation.
For v=e2 the basis matrix is

    Ccyc=[v,T_g v]=[0,-L;1,a], det Ccyc=L.

Converting the integer input(1,0)^T to these coordinates requires the
second coordinate-1/L, not an integer. Fixed nonunit division cannot
be relabeled multiplication by an allowed fixed integer numeral. This
input is already attained by the signed form map on positive raw history
coordinates: using the unchanged four-coordinate decoder C0,

    V*C0=[-1,-1,0,2;h+2,0,1,-h-4],
    (H4,H5,H6,H7)=(1,2,h+6,2)

gives V*C0*H=(1,0)^T. These are local positive raw coordinates, not a
claim that they extend to a genuine ordinary-input history or a complete
native zero. The counterexample concerns the exact arbitrary-integer
action cut proved by the quotient-pair theorem. No supplied divisibility
guard at that cut justifies the nonunit conversion.

## 4. A genuine three-product schedule, with its actual cost

For an equal-diagonal matrix[a,b;c,a] and arbitrary integer input(x,y),
compute

    s=x+y;
    u=a*s; v=(b-a)*y; w=(c-a)*x;
    out1=u+v; out2=u+w.                                  (12)

The output is exactly(ax+by,cx+ay). Every displayed coefficient is a
fixed integer, so this is a valid3M+3A schedule. For(9) the three product
coefficients are199,-229,-1519. It applies uniformly to(5), where
b=-L and c=-4hL.

The literal dense2-by-2 product costs4M+2A. Both schedules have six
operations under the current equal-cost M/A ledger. Including the two
subtractions t_+-T t_- changes the quotient core from4M+4A to3M+5A.
The unchanged final3-by-2 append costs6M+6A, so the full pair append
becomes9M+11A, still20 operations, instead of10M+10A. No additional
total-operation saving follows from this legitimate three-product rule.

The identity does not prove that an arbitrary quotient T can be made
equal-diagonal by an integral basis change. A basis conversion on already
formed runtime words also is not free. One may investigate a different
fixed input-form recipe in a future source, but it must include the
corresponding coefficient preparation, positivity and consumer argument.

**Open question 1 (unrestricted local optimization).** Root asked whether
the integral quotient can lower the current paid append further. The
family above rules out the specified unit-pivot, unimodular companion
and triangular shortcuts. It does not rule out arbitrary integer linear
circuits, a cheaper shared consumer schedule, independent left/right
factorizations with all conversions charged, or special relations among
the actual universal relator matrices. Those remain separate questions;
no generic arithmetic-circuit lower bound is claimed here.

## 5. Provenance and execution boundary

Root requested the quotient follow-up and independently checked the
explicit g=3 matrix, the whole family, scalar residue, cyclic determinant,
discriminant and three-product tie by hand. The author derived those
formulas and the positive raw-coordinate division counterexample.
Aristotle subsequently read the full draft and independently checked the
exact quotient recipe, every congruence/index/triangular obstruction,
the positive raw-coordinate example and all paid counts, requesting no
correction. Exact dependency bytes and read spans are recorded in the
companion metadata.

All work is handwritten algebra and inert proof reading. No supplied,
archived, committed, predecessor or frozen helper is run or imported;
no saved scientific source or coefficient array is evaluated or degree-
propagated. No scientific sampling, local emitter or build is used.
New files remain in/tmp; repository files, Git and earlier frozen
artifacts are unchanged. No existing complete compiler bound is altered.
