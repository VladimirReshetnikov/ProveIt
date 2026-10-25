# Cancellation-preserving partial centering: thirteen integers, degree152, 119 operations

## Result and precise boundary

`integer13_degree152_ops119.json` is one fixed ordinary polynomial in thirteen
unrestricted integers, of exact total degree152 and119 live binary operations
(71 multiplications,24 additions,24 subtractions). Every scalar multiplication
and square is charged. The six complete integer coefficients are retained in
`inherited/coefficients`, including their bytes and finite reconstruction recipe.
No new coefficient, quantified register, division gate or variable exponent is
introduced. The finite checks below do not search for any Diophantine zero.

This polynomial is identically the incoming thirteen-variable degree152,
126-operation polynomial after the triangular shear n_old=n_new-k. Since k is
independent of n, this is a polynomial automorphism of Z^13. Thus the entire
integer zero sets correspond bijectively. The incoming signed-index theorem
and its retained native/compiler/refutation calibration transfer verbatim:
ordinary ZFC proves that universal nonvanishing is equivalent to syntactic
Con(ZFC). This neither asserts consistency nor constitutes a new end-to-end
proof-assistant theorem or a global optimum result.

The immediate authenticated source is `inherited/PROOF.md`, especially its
Sections1--5. That proof changes the first-index modulus to XY^2 and weakens
the magnitude guard from q^8 to q^6; those changes are inherited here, not
claimed as new. It supplies a complete soundness map into its B0-only calibrated
predecessor and a canonical completeness construction. Its complete signed
packet, source files, six numeral payloads and recipe are retained byte-for-byte.
The new contribution is the exact cancellation-preserving chart and evaluator.
It strictly dominates the incoming13/152/126 at fixed degree and variable count.
Against the earlier13/156/117 it trades two gates for four degrees.

## 1. Entire polynomial

The thirteen unrestricted inputs, in literal order, are

    j,C,z,h,r,v,w,T,c,n,y,p1,p2.

The six fixed ports, all fully supplied, are beta,K0,MC,MF,cone_A,cone_B.
MF is already shifted. In particular beta=2^1064921-1, cone_A=2^1113 and
cone_B=2^666104. Define the following polynomial abbreviations:

    J=6j+1, qm=beta J, q=qm+1, W=12w+4, X=qW, Y=v,
    F=(K0+W)C-z qm,
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    ell=EY, k=R+1+h ell, eta=c-Yk, L=ell k,
    I=(2r+1)c^2, Ds=Delta I^2, Fs=1+Ds,
    Q=Delta Ds, V=Fs(cT-R)-c,
    q3=q^3, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=(Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq^2)^2],
    G=4(budget-p1^2-p2^2)-3,
    Dt=1+L(L+k), U2=U^2, ga=U2 G, db=4U2 Dt, fc=16U2 Fs,
    Zc=U(n+2L)+M Klo+H(Y-q3),
    gc=ga+fc, Z2=Zc^2, gaf=ga fc,
    inner=(Z2-gc-db)^2-4(gaf+db gc),
    N=inner^2-64 gaf db Z2,
    uu=(V+y)^2, Ea=uu-Q(uu-V^2),
    P=(N+1)Ea-1.

This is the entire literal polynomial; intermediate names introduce no unknowns.
The alternative auxiliary identity

    Ea=V^2-(Q-1)y(2V+y)                                  (1)

holds by expansion. Its schedule saves one operation through reuse of uu.

## 2. Universal identity to the incoming chart

For proof only write

    Z=Un+M Klo+H(Y-q3), b=2L+k,
    A(z)=(z+Uk)^2+4U(Lz-U).

The incoming norm, with old numerator Z_old, is

    K_old=(A(Z_old)-ga-fc)^2-4[ga fc+db(ga+fc)],
    N_old=K_old^2-64 ga db fc[A(Z_old)+db].

Substituting n_old=n-k gives Z_old=Z-Uk. The exact identities are

    A(Z-Uk)=Z^2+4ULZ-4U^2(1+Lk),
    A(Z-Uk)+db=(Z+2UL)^2=Zc^2.                       (2)

Consequently inner=K_old and N=N_old identically after the shear. Identity(1)
also identifies the auxiliary factors. Therefore

    P_new(n)=P_incoming(n-k)

as whole polynomials, not merely at zeros or at leading degree. The inverse
substitution is n_new=n_old+k. The other twelve inputs and all fixed ports
are unchanged. These polynomial maps are defined on every integer assignment.

Only k, of degree5, is removed from the completed carrier. Removing 2L as well
would spoil the degree152 cancellation because L has degree9. This chart is
not the full centering used in the earlier degree156 packet.

## 3. Direct signed-root proof, including all boundary cases

We also give complete direct maps to the incoming fifteen-variable kernel,
so the reduction does not conceal a root-extraction hypothesis.

Unconditionally q is even and nonzero: beta is odd and greater than1, and
beta(6j+1)=-1 is impossible. Thus |q|>=2, |W|>=4, |X|>=8, and X is even.
The integer a=(X+1)Y is zero or has absolute value at least7. Hence
Delta=(a+2)^2-1>=3. H=4a+3 is odd and nonzero, so U is nonzero.
Also ell=XY^2 is even, ell(ell+1)>=0, and

    Dt=1+ell(ell+1)k^2>=1,  Dt odd,  Fs=1+Delta I^2>=1.

G is1 modulo4, hence odd and nonzero. These facts do not assume a zero or
a positivity guard. Since N is a square modulo4, N cannot equal-2.
At P=0 the two integral factors (N+1),Ea are units. The first must be+1,
so N=0 and Ea=1. Conversely those two equalities imply P=0.

Put rho=Zc/U in Q. The universal complex factorization is

    N/U^8 = product_(eps in {+1,-1}^3)
      [rho-eps1 sqrt(G)-2 eps2 sqrt(Dt)-4 eps3 sqrt(Fs)]. (3)

It is verified by multiplying all eight factors, without sign assumptions.
If G<0, its radical is the sole nonreal term in every factor, with nonzero
imaginary part, while rho and the other two radicals are real. Thus N=0
is impossible. Hence G>0. The case G=0 is excluded by its oddness; the
other two radicands are strictly positive, including their possible value1.

Write each positive radicand as u_i^2 d_i, with u_i a positive integer and
d_i squarefree. Distinct squarefree radicals, including sqrt(1), are linearly
independent over Q. One proof adjoins the square roots of all relevant primes:
the sign-change automorphisms have distinct characters, and character averaging
projects onto each distinct radical. Group any vanishing factor of(3) by its
squarefree class. An irrational group involving G has an odd coefficient plus
even coefficients, and cannot sum to zero. One without G but with Dt has a
coefficient of2-adic valuation exactly1 plus at most a multiple of4, and cannot
sum to zero. One containing only Fs is nonzero. The roots of G and Dt have
odd u_i since these radicands are odd. An even squarefree class can contain
only Fs and is likewise excluded. Thus no distinct-class or genericity
assumption is being made: coincident irrational square classes have been
explicitly ruled out by their2-adic coefficients.

All three classes are1. The signs of the vanishing factor give integers

    g^2=G, tau^2=Dt, f^2=Fs,
    rho=g+2tau+4f.                                      (4)

In particular rho is an odd integer and is nonzero. No division by rho has
been used; zero-carrier cancellation is excluded as a conclusion. Neither
f nor tau was assumed positive; all eight signed branches are allowed.

The incoming fifteen-variable kernel has common inputs j,C,z,h,r,v,w,T,c,n
and f,y,p1,p2,p3. Its residuals, using its own n and Z, are

    A=(Z+Uk)^2+4U(LZ-U),
    B=f^2-Delta I^2-1,
    Caux=V^2-(Q-1)y(2V+y)-1,
    Guard=budget-1-p1^2-p2^2-p3(p3+1).

For it Q=Delta(f^2-1) and V=f^2(cT-R)-c. At a new zero select the signed
integers in(4), and restore

    f_old=f, p3_old=(g-1)/2, n_old=n-k-g-4f.             (5)

All are integers. The old numerator satisfies

    Z_old/U+(2L+k)=rho-g-4f=2tau.

The exact identity A=(Z+U(2L+k))^2-4U^2 Dt gives A_old=0. The equation
f^2=Fs gives B=0, and identifies old Q,V with the new ones. Thus Caux=0.
Finally p3_old(p3_old+1)=(G-1)/4=budget-p1^2-p2^2-1 gives Guard=0.
This is a literal zero of the fifteen-variable kernel.

Conversely take any integer zero of that kernel. Its first row gives

    (Z_old/U+2L+k)^2=4Dt.

A rational number whose square is an integer is an integer: reduce its
fraction to lowest terms and its denominator squared divides its numerator
squared. The displayed rational is also even since its square is divisible
by4. Write it2tau. Set g=2p3_old+1 and

    n_new=n_old+k+g+4f_old,                            (6)

delete f_old,p3_old and retain every other coordinate. The guard and strong
rows give g^2=G and f_old^2=Fs. The new rho is g+2tau+4f_old, so one factor
of(3) vanishes. Its auxiliary factor is1. Hence P_new=0. These are maps on
every zero, with all proof-only quotients shown integral. No simultaneous
Pell existence or unrestricted canonical-witness flexibility is added.

## 4. Exact degree, including both deliberate cancellations

Naive max/sum propagation on the literal DAG gives only an upper bound172;
the two exact cancellation cuts below are essential to the attained degree152.

Let the highest homogeneous forms be

    q0=6 beta j, X0=12q0 w, Y0=v,
    F0=12wC-q0 z, R0=-q0^3 F0,
    ell0=X0 Y0^2, k0=R0+h ell0, a0=X0Y0,
    U0=8q0^3 a0,
    T0=cone_A^2 Y0^2 F0^2+4q0^2 Y0^4+q0^6.

The complete degree16 budget top is -k0^2 T0. In particular k0 is NOT
replaced by R0: the h ell term has the same degree and must be retained.
The leading forms of G,Dt are -4k0^2 T0 and ell0^2 k0^2 respectively.
The three scaled radicands ga,db,fc have degrees28,30,24.

Zc has degree15, so a naive max/sum propagation incorrectly leaves a
degree30 term in Zc^2-db. Identity(2), in full, proves instead that

    Zc^2-db=Z^2+4ULZ-4U^2(1+Lk)

has degree26, with top -4U0^2 ell0 k0^2. Thus the first square in inner
has degree56, whereas -4db ga has degree58. It follows that

    [inner]_58=64 U0^4 ell0^2 k0^4 T0,
    [N]_116=4096 U0^8 ell0^4 k0^8 T0^2.                 (7)

The outer subtracted product has degree112 and cannot cancel the degree116
square. The complete formal calculation is independently checked with weights
(Z,U,L,k,G,Fs)=(7,6,9,5,16,12); its entire norm top is256 U^8 L^4 G^2.

The second deliberate cancellation is uu-V^2=2Vy+y^2. Although uu has
degree34, this difference has degree18. Thus Ea has degree36, with top

    [Ea]_36=32 a0^6 r^4 c^8 R0 y.                       (8)

Multiplying(7),(8) gives the entire degree152 output top; the final -1
cannot affect it. In particular the actual fixed-coefficient witness is

    [j^90 w^18 v^22 z^9 r^4 c^8 y] P
         =2^167 3^108 beta^90 >0.                      (9)

The exponents sum to152. To check this coefficient one may first set C=h=0,
which removes only terms with those absent variables; then select the q0^6
term from both copies of T0. The verifier checks this extraction symbolically,
not on a sampled line. Equations(7),(8) supply the complete leading forms.
Thus152 is an attained exact degree on the authentic six-number slice.

## 5. Verification and reproducibility

`build.py` deterministically emits the one literal DAG from the complete formula
specification. `check.py` imports neither producer nor circuit implementation.
It checks the incoming126-gate and new119-gate graphs against independently
written polynomial cuts, every gate's topology, coverage and liveness, all six
ports, exact operation counts, the whole-polynomial shear, both full leading
cancellations, the complete signed-factor identity and coefficient(9). Every
one of the119 live binary gates is separately corrupted and rejected.
Normal and Python -O executions have the same acceptance conditions.

`reconstruct_coefficients.py` calls only the inspected retained finite tuple
constructor and recomputes all six raw payloads. It does not execute a blank
machine, search for a refutation, use upstream networking, or rebuild a kernel
certificate. `INHERITED_PINS.json` authenticates the full retained source packet.
The unbounded sign, squareclass and root-map proof is Section3 above; finite
controls are not offered as substitutes for it or for the inherited compiler
calibration. The retained degree300 fixed-frame obstruction concerns a different
eleven-variable architecture and is not repurposed here as a global bound.

No twelve-variable breakthrough is claimed. Exploratory denominator-transfer,
primitive-carrier and strong-scale variants did not yield an audited improvement
and are not mathematical results in this release.
