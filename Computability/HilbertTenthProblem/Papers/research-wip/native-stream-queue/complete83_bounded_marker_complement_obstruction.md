# A bounded marked word does not rescue the combined complement chart

Replacing the two positive coordinates `F,alpha` of the actual complete84
source by positive `U,beta`, with `U=q−F` and `beta=F+alpha`, permits a
complete **83=47M+36A** source with the same eighteen witnesses. It is
unsound: for every valid fixed compiler and every positive ordinary input
`x`, the modified polynomial has a positive zero. This remains true with

    C=Z+2^u>0, W=2^u>0, C+Z+2dx<q,
    R>q^4, F_restored<0, alpha_restored>0,

and with all six normalized unscaled factors equal to one and the scaled
strong factor equal to Delta. In particular this failure needs neither a
negative input Pell root nor cancellation of negative unit factors.

The new point is the **combined chart** and this stronger counterexample
domain. The old positive-complement collapse supplied a nonpositive marked
word and a negative input root; the old positive-transport projection let
the marked word exceed q. Their arithmetic-progression and canonical
converse arguments are useful predecessors, not new claims here. The
current proof binds the actual `Kconstant+w` transport and the normalized
strong/Bezout quotient of complete84.

## 1. The fully charged candidate and its exact signed identity

Write ell=2d, B=2^d and J=Jrep. The actual fixed compiler has d>=4,
positive odd inner_bits=b, K=Kconstant>0, and its literal positive MC and
shifted MF numerals. Thus MF below means the **source** MF, including its
inherited B−1 shift. No mask is chosen to fit the input. Keep

    q=(B−1)J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=Y(X+1),
    A=a+2, Delta=A^2−1, H=4a+3.

The source register named A is Delta, not the proof parameter A. In the
parent let U_old=q−F and V_old=U_old−Z. Its relevant expressions are

    C=V_old−alpha−ell*x, W=C−Z, u=ell*x+b,
    gap=(q−1)U_old+V_old,
    R=gap*(q^2−1)+(MC+q*MF)J,
    Nt=(K+w)C+U_old−transport_quotient*(q−1).

Supply `outer_complement` U and `outer_beta` beta in place of F and alpha.
Delete the row `q_minus_F=q−F`, and make exactly these five retained edits:

    q_minus_FZ       = q−Z
    C_after_alpha    = q_minus_FZ−outer_beta
    gap_product      = q*outer_complement
    gap              = gap_product−Z
    transport_partial= innerC+outer_complement.

Every other row is literal. In particular the already paid `scaled_t`,
the final subtraction defining C, W, all seven factors and the entire
finalizer remain. There are 78 literal retained rows and five edited rows;
the deleted instruction is one subtraction. The complete count is
83=47M+36A, with eighteen positive witnesses and the same ordinary input.
The emitted candidate array is inert evidence, not an executed program.

For arbitrary signed supplied values restore

    F_old=q−U, alpha_old=beta−q+U.                  (1)

Then U_old=U, C=q−Z−beta−ell*x and gap=qU−Z. All retained
register values agree except the two private registers `q_minus_FZ` and
`gap_product`; their downstream uses agree exactly. Therefore

    P83(new tuple)=P84(restored tuple)               (2)

over every commutative ring. This follows from the literal full-array
binding and the displayed local identities, without evaluating either
array. The coordinate change is an invertible affine transformation on
each fixed-program slice, so the exact degree remains 187. Its gate-degree
bound and native semantics are not being inferred from finite samples.

Every parent positive zero maps forward to a positive child tuple:
U=q−F>Z>0 by the parent's recovered outer inequalities, and beta=F+alpha>0.
The inverse requires two additional signs. The zeros constructed below
violate exactly the F sign, while restoring a positive alpha.

**Remark 1 (retained failed proposal).** The proposed inference “the
positive beta retains the marked-word/input-width inequality, so the saved
subtraction preserves the accepted inputs” is false. Sections 2–5 give
positive zeros at every input of every actual compiler, including any
compiler for the empty language. They satisfy the retained width
inequality and have positive marked word, positive input root and positive
restored alpha. This is a full counterexample, not merely an off-zero
failure of the inverse map.

## 2. A small Z and a genuine positive width slack

Fix a valid compiler and any x>=1. Put u=ell*x+b, W=2^u. Let
L=lcm(1,...,d), and let D be its odd part. Choose a power of two M large
enough that

    M>=8, L divides t=DM,
    q=2^t > W+2M+ell*x.                            (3)

Such M exist because D is fixed and 2^(DM) grows faster than M. Since d
divides t, J=(q−1)/(B−1) is a positive integer. Also D divides q−1:
if p^e divides D, then p^e<=d, both p^(e−1) and p−1 divide L, and their
coprime product phi(p^e) divides t. Euler's congruence applies at each odd
prime power. Consequently

    q=0 (mod M), q=1 (mod D), t divides q(q^2−1). (4)

For D=1 the congruences modulo D are vacuous. Choose e in [0,4D) with

    e=(MC+MF)J (mod D), e=3 (mod 4).

Since D is odd, this representative exists uniquely and satisfies
0<e<4D<t. Choose Z in [1,M] with

    Z=e−MC*J (mod M),
    C=Z+W, beta=q−2Z−W−ell*x.                     (5)

All four quantities Z,C,W,beta are positive. Moreover
C+Z+ell*x=q−beta<q. Thus the genuine ordinary-input width constraint is
retained; no oversized marked word is used.

For any integer U define the actual packed index

    R(U)=(qU−Z)(q^2−1)+(MC+q*MF)J.                (6)

Modulo D its first term vanishes; modulo M it equals Z+MC*J. Hence

    R(U)=e (mod t), R(U)=3 (mod 4),               (7)

independently of U. This uses both coprime parts of t and does not assume
that the compiler's d is a power of two.

## 3. Exact current transport and arbitrarily high population

Choose U0 in [1,q−1] with

    U0=1−(K+2^e)C (mod q−1).

Let R0=R(U0)>0, S=q(q^2−1)(q−1), and put

    l0=floor(R0/S)+1, D0=S*l0−R0, 0<D0<=S.

For sufficiently large N take

    l=2^N−l0>0, U=U0+(q−1)l,
    R=R0+Sl=S*2^N−D0.                            (8)

When 2^N>D0, the two binary blocks in

    R=(S−1)2^N+(2^N−D0)

are disjoint. Their exact population is

    pc(R)=pc(S−1)+N−pc(D0−1).                     (9)

We can therefore choose N so that simultaneously

    U>q, R>max(q^4,3q+1,3t,u,e), pc(R)>=3t+2.    (10)

All congruences (7) persist. Set X=2^R and w=2^(R−t), so the actual
source equation X=wq holds. Modulo q−1, the relation R=e modulo t gives

    w=2^(R−t)=2^e (mod q−1).

Therefore

    transport_quotient=((K+w)C+U−1)/(q−1)          (11)

is a positive integer and the actual Nt equals one. Formula (11) uses w,
not X, in its coefficient. The proof constructs this quotient
existentially; the source continues to pay its multiplication by q−1.
Equations (1), (5), and U>q give F_old<0 and alpha_old=beta+U−q>0.

## 4. Fresh positive first, main and input coordinates

Let r=(R−1)/2 and define the actual half-binomial value

    M_R=sum(j=0..r) binom(2r,r+j) X^j, Y=M_R/2.   (12)

It is an integer. The central term has valuation pc(r)<R, and every other
term is divisible by X=2^R. Thus

    v2(Y)=pc(r)−1=pc(R)−2>=3t.

In particular s=Y/q^3 is a positive integer. There is no appeal to an
unhalved binomial convention. The much smaller asymmetric scale w=X/q
was already supplied in Section 3.

Use the standard integer Pell sequences chi_A and psi_A, and set

    a=Y(X+1), A=a+2, Delta=A^2−1, E=XY, P=2XY^2+1,
    c=psi_A(R), Dmain=chi_A(R),
    k=2psi_P(r+1), tau_root=chi_P(r+1),
    eta=c−kY, zeta=k−eta, h=(k−R−1)/E.            (13)

Here both strict ratio slacks are positive, even though R>q^4. For
completeness, the positive-converse argument in the pinned transport
projection note uses xi=(X+1)^(2r)/X^r=2Y+theta with 0<theta<1/4.
The elementary Pell estimates at these newly chosen X,Y give

    xi<c/(k/2)<xi*(1+8r/a),
    0<c/k−xi/2<4r*xi/a<16r/(X+1)<1/2.

Their prerequisites 6XY^2>a and 4r/a<1/2 follow directly from
Y>=X^r/2 and X=2^R; they do not require an upper bound on R or an assumed
ratio. Hence Y<c/k<Y+1. Since P=1 modulo E, k=R+1 modulo E;
strict Pell growth gives h>0. These identities make the first factor and
index factor exactly one, including the actual first-root expression
tau_root^2−(XY^2 k)(XY^2 k+k).

For j>=0 put

    G_j=(chi_A(j)−a psi_A(j)−2^j)/H, H=4a+3.

The recurrence

    G_0=G_1=0, G_2=1,
    G_(j+2)=2A G_(j+1)−G_j+2^j

proves integrality and strict increase from j=1. Since u>=3 is odd and
u<R, define

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa−u)/Delta, rho=G_u, sigma=G_R−G_u. (14)

For odd u the recurrence modulo Delta gives psi_A(u)=u modulo Delta;
strict growth gives delta>0. Both rho and sigma are positive. The literal
main and input roots are now

    X+ac+(rho+sigma)H=Dmain,
    W+a*kappa+rho*H=mu.

Both norms equal one. These are positive roots: the construction does
not exploit sign ambiguity in the input norm.

## 5. The current normalized strong and Bezout auxiliary completion

Rebuild the canonical auxiliaries at this same A,c,R:

    m=2cR, f=chi_A(m), i=psi_A(m)/c^2,
    Saux=Delta*psi_A(m)=Delta*i*c^2,
    y_aux=psi_Saux(R), Vaux=chi_Saux(R)/Saux.       (15)

The quotient i is an integer: expand
(chi_A(R)+c sqrt(Delta))^(2c). The term with one square-root factor
contains 2c^2, and every higher odd term contains c^3. All values are
positive. The canonical minus identities, as proved in normalized-strong87
Section 3 and the half-binomial kernel Section 6, give

    Saux^2=Delta*(f^2−1),
    Vaux=−c (mod f), Vaux=−R (mod c),
    Saux^2*(Vaux^2−y_aux^2)+y_aux^2=1.             (16)

They require c=psi_A(R), m=2cR and R=3 modulo 4, all established here;
they have no R<q^4 premise. In particular Vaux is an integer because R is
odd. Since f^2=1 modulo c, gcd(c,f)=1. Thus the positive quotient

    auxiliary_quotient=(Vaux+c+R*f^2)/(c*f)        (17)

is integral: the numerator vanishes modulo f and modulo c separately.
It makes the exact current expression c*(auxiliary_quotient*f−1)−R*f^2
equal Vaux. Consequently the auxiliary factor is one and the literal
scaled strong factor is Delta*f^2−Saux^2=Delta.

Equations (3), (5), (8), and (11)–(17) now supply every one of the
eighteen positive coordinates

    J,U,beta,transport_quotient,f,h,i,auxiliary_quotient,
    s,w,tau_root,eta,zeta,y_aux,Z,delta,rho,sigma.

Every actual factor has been checked: first/main/input/auxiliary/index/
transport are one and scaled strong is Delta. The unchanged full product
minus Delta therefore vanishes. This holds for each x>=1 with the same
fixed compiler numerals. The projection is all positive integers, so the
candidate cannot be a compiler for any proper subset of that domain.

## 6. Evidence, provenance and limits

The accompanying fresh standard-library checker reads the actual84 JSON
inertly, emits the complete modified array as data, and checks topology,
liveness, the literal delta and operation/witness counts. It does not
execute either array, any predecessor helper, or a copied predecessor.
Its independent local polynomial arithmetic checks the boundary identities
in Section 1. Handwritten arithmetic-progression checks corroborate
Sections 2–3 on explicitly synthetic numeral choices; these are not
compiler instances. Separate small canonical Pell components check the
ratio/input and normalized/Bezout identities without materializing the
enormous complete native witnesses in the theorem.

The receipt records exact dependency hashes, including actual84 source,
its positive parent, the normalized auxiliary and half-binomial proofs,
and the two older projection obstructions. The all-size proof above, not
the finite diagnostics, supplies the compiler-quantified counterexample.
There is no successful83 compiler, optimality assertion, deletion of the
source's strong condition, or new external analytic-number-theory premise.

The finite evidence consists of five exact local polynomial identities,
80 synthetic outer CRT/population cases, four positive first/main Pell
components, twenty positive input splits, and five normalized auxiliary
components. Both complete saved source arrays have execution count zero.

The principal immutable dependency hashes are:

| File in `native-stream-queue` | SHA256 |
|---|---|
|`complete84_scaled_strong_output.json`|`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`|
|`complete84_scaled_strong_output.md`|`01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`|
|`complete85_auxiliary_bezout_projection.md`|`d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b`|
|`complete75_normalized_strong87.md`|`9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b`|
|`pell_kernel_half_binomial42.md`|`0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992`|
|`complete75_positive_transport_projection_obstruction.md`|`6fed5e50d1f07039b0243c40ae712dc4e618b821d308327d36d05803d8a94ee8`|
|`complete75_positive_complement86_all_input_collapse.md`|`8a1049e155f0ce8b59ab10c7f7bd7ef69b82798e56888beafed1ff5e35cbc1da`|

The receipt additionally pins the earlier outer-slack, marked-word and
input-bound obstructions used to distinguish the present route. Only the
new author helper was run during preparation; its normal and `python -O`
checks reproduce the receipt from `/`. No predecessor imports, saved DAG
evaluations, compiler execution, builds or repository edits were performed.

Author helper SHA256:
`fd6c980271d6b52a0d9120aabce4e4eb54cafe83c37a94b707ed59090618cbd9`.
Author receipt SHA256:
`5a2f248a0edbcb2af6abc2a2fb27cb4ec2b64b8eb663c6305fcd229396f400e5`.
