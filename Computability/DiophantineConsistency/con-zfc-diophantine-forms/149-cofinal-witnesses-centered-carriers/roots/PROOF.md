# Centered norm charts: 14/88/110 and 13/156/117

## Result and exact dependency boundary

The two new literal fixed integer polynomials have respectively fourteen
unrestricted unknowns, exact degree 88 and 110 live binary operations; and
thirteen unrestricted unknowns, exact degree 156 and 117 operations. They are
polynomial triangular coordinate transforms of the retained Round18 14/88/115
and 13/156/125 equations. The first strictly dominates the retained 14/94/110
point, but not 14/86/112. The second saves eight operations at unchanged degree.
No global minimum, consistency proof, new kernel certificate, or new native
encoding is asserted. All six complete fixed numeral payloads are unchanged.

For the exact shear comparison, only n changes: n_old=n_new-(2L+k). Both L and k
are polynomials in retained inputs, independent of n. Hence this is a genuine
polynomial automorphism of Z^14 or Z^13, with inverse n_new=n_old+(2L+k).
The distinct root-dependent maps below restore the fifteen-variable parent;
they are not incorrectly described as polynomial maps on thirteen coordinates.

The immediate fifteen-variable equation and ordinary proof are retained in
inherited/baseline/source/free_scale15_equation.json and FREE_SCALE15_PROOF.md.
Its strong/signed-Pell, source34/native/compiler and syntactic-refutation
calibrations remain the exact inherited dependencies. The source closure and
finite numeral recipe are retained byte-for-byte. Universal maps on every zero
are given here, so no new simultaneous Pell existence or canonical-witness
freedom is required. Ordinary ZFC-provable equivalence between universal
nonvanishing and syntactic Con(ZFC) transfers through those dependencies.

## 1. Common arithmetic front and precise parent

Let the fixed ports be beta,K0,MC,MF,cone_A,cone_B, with MF already shifted.
In particular beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104. Define

    J=6j+1, qm=beta J, q=qm+1, W=12w+4, X=qW, Y=v,
    F=(K0+W)C-z qm,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    k=R+1+hE, eta=c-Yk, L=E(Yk), I=(2r+1)c^2,
    q3=q^3, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Z=Un+M Klo+H(Y-q3),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=(Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(k q3)^2],
    Dt=1+L(L+k), b=2L+k.

All names are polynomial abbreviations, not additional quantified witnesses.
The fifteen-variable parent has shared coordinates j,C,z,h,r,v,w,T,c,n and
f,y,p1,p2,p3. It uses

    Q=Delta(f^2-1), V=f^2(cT-R)-c,
    A=(Z+Uk)^2+4U(LZ-U), B=f^2-Delta I^2-1,
    Caux=V^2-(Q-1)y(2V+y)-1,
    Guard=budget-1-p1^2-p2^2-p3(p3+1),
    P15=A^2+B^2+Caux^2+Guard^2.

Its zero set is exactly A=B=Caux=Guard=0. The exact centered identity is

    A=(Z+Ub)^2-4U^2 Dt.                                      (1)

This identity, rather than an incomplete leading-form quotation, is used below.
The already-known carrier leading-form erratum is not a new discovery here.

Unconditionally q is even and nonzero: beta is odd and beta>1, so beta J=-1
is impossible. H is odd and nonzero; hence U is nonzero. Since |W|>=4,
|X|>=8. The integer a=(X+1)Y is zero or |a|>=7, giving
Delta=(a+2)^2-1>=3. With D=XY^2, one has L=Dk and
Dt=1+D(D+1)k^2>=1. Since X is even, D is even and Dt is odd.
Finally Delta is 0 or 3 modulo 4, so B is 0,1 or3 modulo4 and never -2.
These assertions require neither a source zero nor a positivity guard.

## 2. Fourteen inputs: centered two-root norm

Use precisely

    j,C,z,h,r,v,w,T,c,n,f,y,p2,p3.

Keep Q,V from Section1, and set

    S=f^2-Delta I^2, Ea=V^2-(Q-1)y(2V+y),
    G=budget-[1+p2^2+p3(p3+1)],
    U2=U^2, ga=U2 G, db=4U2 Dt,
    N2=(Z^2-ga-db)^2-4 ga db,
    P14=(N2+1) S Ea-1.                                      (2)

This is the full division-free polynomial in integer14_degree88_ops110.json.
Since N2 is a square modulo4, N2!=-2. Also S=B+1!=-1. At a zero of (2),
the three integral factors are units. The first two must equal+1, forcing
N2=B=0 and Ea=1. Thus Caux=0. Conversely these three equalities imply P14=0.

### Soundness, including G=0 and the zero-carrier boundary

Write rho=Z/U in Q and Aroot=4Dt>=4. The equation N2=0 is exactly

    (rho^2-Aroot-G)^2-4 Aroot G=0.                          (3)

If G<0, its left side is a square plus a strictly positive number, impossible.
Hence G>=0 and budget=G+1+p2^2+p3(p3+1)>0. The budget is nonpositive if
Y=0 or k=0, so both are nonzero. Also budget<=Y^2 k^2 q^2. Because |D|>=8,
D(D+1)>=D^2/2, and therefore

    Aroot >=4+2X^2 Y^4 k^2
          >=4+32q^2 Y^4 k^2 >Y^2 k^2 q^2 >=budget>G.        (4)

Consequently rho!=0: otherwise (3) would say (Aroot-G)^2=0. This exclusion
is established before making any division by rho. Define proof-only rationals

    p=(rho^2+G-Aroot)/(2rho), u=rho-p.

Equation (3) gives p^2=G and u^2=Aroot. A rational number whose square is an
integer is an integer, by reducing its fraction to lowest terms. Thus p,u
are integral; since u^2=4Dt, u is even. Put tau=u/2. This includes G=0,
where p=0 and rho^2=Aroot>0. No distinct-square-class assumption was made.

Restore parent coordinates

    p1_old=p, n_old=n-b-p,

retaining all other inputs. Since Z is affine in n with coefficient U,
Z_old/U+b=rho-p=2tau. Identity (1) gives A_old=0. The strong and auxiliary
rows are unchanged, and p^2=G gives Guard_old=0. This is a literal parent zero.

### Completeness on every parent zero

At a parent zero, (1) says (Z_old/U+b)^2=4Dt. The rational number on the left
before squaring is integral by the same reduced-fraction argument, and is even;
write it as2tau. Delete p1 and put

    n_new=n_old+b+p1_old.

Then rho=2tau+p1_old, G=p1_old^2. Substitution in (3) gives N2=0; the other
rows are unchanged. Hence (2) vanishes. Every proof-only quotient has been
proved integral; the reverse map itself is polynomial in all parent inputs.

## 3. Thirteen inputs: centered three-root norm

Use precisely

    j,C,z,h,r,v,w,T,c,n,y,p1,p2.

Replace f^2 throughout its auxiliary interface by

    Ds=Delta I^2, Fs=1+Ds, Q=Delta Ds, V=Fs(cT-R)-c,
    Ea=V^2-(Q-1)y(2V+y), G=4(budget-p1^2-p2^2)-3.

Keep Dt and the front of Section1. Define the literal shared evaluator

    U2=U^2, ga=U2 G, db=4U2 Dt, fc=16U2 Fs,
    gad=ga db, gab=ga+db, Z2=Z^2,
    inner=(Z2-gab-fc)^2-4(gad+gab fc),
    N3=inner^2-64 gad fc Z2,
    P13=(N3+1) Ea-1.                                      (5)

This is integer13_degree156_ops117.json. Since N3 is a square modulo4,
it cannot equal-2. At a zero, the two integer factors in (5) are units; the
first must be+1, hence N3=0 and Ea=1. Conversely these equalities suffice.

### Full root extraction: negative, zero and shared-class branches

Here Fs>=1, Dt>=1 and Dt is odd, while G=1 modulo4 is odd and nonzero.
The universal signed-root factorization, over C, is

    N3/U^8 = product_(eps in {+1,-1}^3)
      [rho-eps1 sqrt(G)-2 eps2 sqrt(Dt)-4 eps3 sqrt(Fs)],    (6)
    rho=Z/U.

It follows by multiplying all eight factors; it is valid regardless of sign.
If G<0, every factor has a nonzero imaginary part from its sole imaginary
radical sqrt(G), since the other radicals and rho are real. Thus N3=0 forces
G>0. There is no G=0 branch because G is odd, and Fs and Dt are never zero.

Write each positive radicand as u_i^2 d_i with u_i a positive integer and d_i
squarefree. A zero factor in (6) yields

    rho=eps1 u1 sqrt(d1)+2 eps2 u2 sqrt(d2)+4 eps3 u3 sqrt(d3).

Distinct squarefree radicals, including sqrt(1), are Q-linearly independent.
For completeness, adjoining the square roots of all involved primes gives a
multiquadratic field whose sign-change automorphisms separate the distinct
characters; character averaging projects onto one squarefree radical.
Group the displayed terms by squarefree class. Every irrational class must
have total rational coefficient zero, but this is impossible: a group with
the G term has an odd coefficient plus even coefficients; one without G but
with Dt has a coefficient of exact2-adic valuation1 plus at most a multiple
of4; a group with only Fs has one nonzero coefficient. G and Dt are odd, so
their u_i and d_i are odd. An even squarefree class can only contain Fs and
is therefore excluded as well. No assumption that Fs is odd is made.

All classes are1. The signs in the vanishing factor supply integers

    g^2=G, tau^2=Dt, f^2=Fs, rho=g+2tau+4f.

Here g is odd, so rho is an odd integer and in particular nonzero. Thus zero
carrier cancellation is ruled out by the proof; no division by rho was used,
and coincident square classes were explicitly included, not ignored.

### Universal maps to and from the fifteen-variable parent

At a zero of (5), restore

    f_old=f, p3_old=(g-1)/2, n_old=n-b-g-4f,

retaining every other shared coordinate. All are integers. The old centered
carrier is Z_old/U+b=rho-g-4f=2tau, so (1) gives A_old=0. The strong row is
f^2-Fs=0. The old Q,V are identical to the new ones since f^2=Fs, so its
auxiliary row is Ea-1=0. Finally p3_old(p3_old+1)=(G-1)/4 gives Guard_old=0.

Conversely from any parent zero, put g=2p3_old+1 and retain every shared input
except

    n_new=n_old+b+g+4f_old.

Delete f and p3. As above the parent carrier yields an integral tau with
Z_old/U+b=2tau and tau^2=Dt. The parent guard gives G=g^2, and its strong
row gives Fs=f_old^2. Thus rho=g+2tau+4f_old, so one factor of (6) vanishes.
Its auxiliary row is unchanged. This constructs a new zero from every parent
zero, without any new canonical-witness or simultaneous-root existence claim.

## 4. Exact polynomial shear versus retained Round18 equations

For either retained equation, substitute n_old=n_new-b. The old carrier obeys
A_old=Z_new^2-4U^2Dt. For the two-root norm this yields exactly

    (A_old-U^2G)^2-16U^4GDt = (Z_new^2-ga-db)^2-4ga db.

For the three-root norm it yields exactly the inner and N3 of (5), since
A_old+db=Z_new^2. No other register depends on n. The finalizers therefore
agree identically as polynomials after that substitution. The inverse shear
adds b. These are bijections of the corresponding complete integer zero sets,
not merely existence reductions. They do not assert that the direct maps to
the parent, which involve selected recovered roots, are bijections.

## 5. Exact degree and arithmetic length

Let the highest homogeneous forms be

    q0=6 beta j, X0=12q0 w, Y0=v,
    R0=q0^4 z-12q0^3 w C, a0=X0Y0,
    U0=8q0^3 X0Y0, L0=X0Y0^2R0.

The degree18 budget top is -R0^2q0^8. The two-root norm has degree60 with
complete top form

    (N2)60=U0^4 R0^4(q0^8+4X0^2Y0^4)^2.

Its strong and auxiliary unit degrees are12 and16, respectively, and

    [j^56 w^8 v^8 z^5 r^2 c^4 f^4 y] P14
       =-2^87 3^64 beta^56 !=0.

Thus its total degree is exactly88 at the authentic fixed numeral tuple.
The three-root norm has degree120 with complete top form

    (N3)120=2^8 U0^8 R0^8(q0^8+X0^2Y0^4)^4.

Its auxiliary unit has degree36 and top form32a0^6r^4c^8R0y. Therefore

    [j^106 w^14 v^14 z^9 r^4 c^8 y] P13
       =2^171 3^120 beta^106 !=0.

Its degree is exactly156. Both selected monomials have the asserted total
degree. The coefficient is unchanged from the corresponding old chart,
but the complete top homogeneous forms have changed and are checked afresh.
The literal counts are14:64 multiplications+23 additions+23 subtractions=110;
13:70 multiplications+23 additions+24 subtractions=117. Every input and all
six coefficient ports are live. These are arithmetic lengths, not bit costs.

## 6. A scoped obstruction: n-shears cannot lower these degrees

Consider any polynomial triangular change n->n+Theta in either centered equation,
where Theta is independent of n and its coefficients are fixed real numbers
(in particular integer coefficients are allowed). If deg(Theta)<=9, let Theta9 denote
its degree9 part, taking Theta9=0 if its degree is smaller. Only Z changes, to Z+U Theta;
its possible degree15 part is U0 Theta9. The three-root inner degree60 part is

    U0^4[(Theta9^2+4R0^2q0^8-4L0^2)^2+(8R0 q0^4 L0)^2].       (7)

This is nonzero: a sum of squares in a real polynomial ring is zero only when
every summand is zero, and its second summand is a nonzero polynomial.
The subtracted outer product in N3 has degree at most114, hence cannot cancel
its degree120 square. The output retains degree156. For the two-root case,
replace the coefficient4 on R0^2q0^8 by1 and8 by4 in (7); the resulting degree60
norm top is again nonzero and the output retains degree88.

If m=deg(Theta)>9, Z+U Theta has degree m+6>15. Its highest power dominates all the
fixed radicands. N2 then has degree4(m+6)>60, and N3 degree8(m+6)>120.
The unchanged finalizer factors add28 or36, respectively. Thus no polynomial
n-shear alone can improve these exact degrees. This is a local, explicitly
specified obstruction, not a lower bound over all reductions or polynomials.

## 7. Verification and retained closure

check.py does not import the builder or circuit implementation. It obtains
old independent audit formulas only as inert AST literals, then independently
checks every new named cut, topology, coverage, liveness, all live binary
counts, full leading norm forms and fixed-coefficient witnesses. It proves
the universal shear, signed-factor, extraction and rigidity identities in
free polynomial rings. Every live gate is separately corrupted and rejected.
Normal and Python -O runs have identical acceptance conditions. The exact
square-class and sign arguments are the unbounded ordinary proofs above,
not claims inferred from the diagnostic samples.

INHERITED_PINS.json authenticates the full retained Round18 root packet,
including all six numeral payloads and the native/signed source closure.
reconstruct_coefficients.py uses its inspected, retained finite recipe to
rebuild every coefficient byte; no blank-machine simulation, consistency
search, upstream code execution, publication, or proof-assistant theorem
rebuild is involved. The known leading-form correction remains inherited.
