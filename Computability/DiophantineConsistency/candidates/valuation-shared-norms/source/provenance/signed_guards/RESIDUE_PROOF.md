# Residue orientation replaces a positivity witness

Source snapshot: ProveIt commit `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.
All variables in this note are unrestricted integers unless explicitly stated.

## 1. Concrete equations and theorem

The delivered `quartic40.json` lists exactly 40 unknowns and 25 quadratic
residuals. Define Q40 to be their sum of squares. Its four coefficient
ports are the literal integers of the entire source34
`mixed-parity-unrounded-1064921` tuple. The supplied gzip payloads store
minimal unsigned little-endian bytes; the mask MF already includes its
shift by beta. They are rebuilt from the literal 943-tile list by
`build_verify.py`. No input depends on an assumption about consistency.

The main theorem is the ordinary mathematical statement, formalizable in ZFC,

    Q40 has an integer zero  <=>  ZFC has a finite syntactic refutation.

Consequently ZFC proves that Q40 has no integer zero if and only if
Con(ZFC). The polynomial has exact degree four, uniformly on the authentic
fixed coefficient slice, because its coefficient of tau^4 is 1.

Two exact polynomial coordinate eliminations give `sextic34.json`, with
34 unknowns and 19 cubic residuals, and `octic29.json`, with 29 unknowns
and 14 quartic residuals. Their sums of squares have exact degrees six
and eight. They share the same consistency equivalence and coefficient tuple.

These improve the inspected degree-four, degree-six, and degree-eight
unrestricted-integer variable counts 41, 35, 30 to 40, 34, 29. They do
not lower the nine-positive or ten-integer high-degree bounds. No global
minimum, new machine calibration, or new end-to-end proof-assistant
certificate is claimed.

For the smallest displayed quartic in this packet, use the additional
`quartic40_direct.json` described in section 9. It replaces only X by
3 X3-1 in the same parent, and has 393 symbolic expanded monomials.
The `quartic40.json` used for sections 2--7 has 614; it is retained
because it preserves the monic X definition needed for the best projections.

## 2. The literal change from the 41-variable parent

Use the source64 quartic41 retained as `upstream/quartic41.json`. In every
row make the affine substitutions

    J_old = 3 J3 + 1,
    w_scale_old = 3 w3 + 1.

Delete its row X-2u^2 and its private coordinate u. All other rows remain
exactly the affine substitutions of the parent rows. There are therefore
41-1=40 unknowns and 26-1=25 rows, still of degree two.

Set

    J0 = 3J3+1,  W = 4(3w3+1),  q = beta J0+1,
    C = q-F-alpha, Q = |q|,
    s = 2 v_scale+1, i = 2r+1,
    Y = s q^3, X = qW, E = XY,
    k = eta+zeta, c = kY+eta,
    a = (X+1)Y, A = a+2, H = 4a+3, Delta = A^2-1,
    R = ((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J0.

These are abbreviations; the literal low-degree lifts specify the same
identities. The exact retained row also gives

    D = X+ac+gamma H,
    k = R+1+hE,
    V = of-c = jc-R.

The new restrictions have a purpose beyond making witnesses larger.
Since beta=2^1064921-1 and 1064921 is odd, beta=1 mod 3. Therefore

    q = 2 mod 3, W = 1 mod 3, and X = 2 mod 3.       (2.1)

Instead of imposing X>=0 using a square witness, we will recover
X=+2^R or -2^R while allowing every sign. The residue (2.1) will then
choose the positive sign. This delayed orientation is the new argument.

## 3. Preliminary bounds with every sign still permitted

At a zero of Q40 each residual vanishes. Write

    Pos(x,y,z) = 1+x^2+y^2+z(z+1).

This is strictly positive on all integer triples and represents every
positive integer: apply Legendre's three-square theorem to 4n-3, whose
representation has one odd and two even squares.

The retained guards F alpha=Pos and F C=Pos imply that F,alpha,C have the
same nonzero sign. Their sum is q, so |q|>=3 and J0 is nonzero. The fixed
mask inequalities, checked for the actual tuple, are

    beta>=17, 0<MC<beta, beta<MF<2beta, K0>=0.

The sign-free packing argument of source64 PROOF44, section 3, applies
without a square-scale hypothesis and gives

    Q>=16, Q(Q^2-1)<R<Q^4-2.                         (3.1)

For completeness, when q=Q>0, writing
G=Q(Q-F)-C gives Q+2<=G<=Q^2-Q-1 and
0<(MC+Q MF)J0<(2Q+1)(Q-1). When q=-Q<0, put
F0=-F,C0=-C. Then G=Q(Q-F0)+C0 satisfies
2Q+1<=G<=Q^2-2, and the mask term is
(Q MF-MC)(Q+1)/beta, strictly between 0 and 2Q(Q+1).
These inequalities give (3.1) in both branches.

The integer W=12w3+4 is nonzero and has absolute value at least 4.
The odd integer s is nonzero. Consequently, with U=|X| and Z=|Y|,

    U>=4Q>=64, Z>=Q^3>=4096,
    M:=|E|=UZ>=4Q^4>3R+1.                          (3.2)

The retained guard eta zeta=Pos implies that eta,zeta have one common
nonzero sign. Define

    xi=sign(X), sigma=sign(k), delta=sign(Y),
    K=|k|, eta0=|eta|, c0=|c|.

Then K>=2, 0<eta0<K, and

    c0=KZ+delta eta0,
    K(Z-1)<c0<K(Z+1), sign(c)=sigma delta.          (3.3)

The positive absolute Pell parameters are

    B=|A|=(U+xi)Z+2xi delta,
    P=|2XY^2+1|=2UZ^2+xi.

The signs used in these formulas are valid because (U-1)Z>2.
They satisfy

    B >= (U-1)Z-2 >= (4Q-1)Q^3-2 > Q^4 > R,
    P > B >= 2, c0 > K.                            (3.4)

For P>B one may use P>=2UZ^2-1 and B<=(U+1)Z+2; the
resulting difference 2UZ^2-(U+1)Z-3 is positive in (3.2).

## 4. Signed power-recovery lemma

The following argument isolates the new unbounded arithmetic. It uses
only (3.1)--(3.4), the displayed polynomial identities, and the standard
Pell rank interfaces explicitly recorded below.

### 4.1. Classify the first and main norms

The retained rows give

    tau^2-XY^2(XY^2+1)k^2=1,
    D^2-(B^2-1)c^2=1.

For b>=2 write chi_b(t)+psi_b(t)sqrt(b^2-1)
=(b+sqrt(b^2-1))^t. Consecutive-product Pell classification gives

    |tau|=chi_P(n), K=2psi_P(n), n>=1,
    |D|=chi_B(p), c0=psi_B(p), p>=1.               (4.1)

This classification is also valid when X<0. In that case let m=UZ^2;
the first coefficient is m(m-1)=(m-1)m, with positive Pell parameter
2m-1=P. Thus no positive-X hypothesis has entered (4.1).

By P>B and c0>K, monotonicity of psi implies p>n. Indeed p<=n would
give c0=psi_B(p)<=psi_P(n)=K/2, contrary to (3.3).

### 4.2. Bootstrap the ordinary strong-rank hypotheses

Since P=xi mod M, the recurrence of psi gives

    psi_P(n)=xi^(n-1)n mod M.

The index equation k=R+1+hE therefore implies

    sigma xi^(n-1) 2n = R+1 mod M.                 (4.2)

If the sign on the left is positive, n>=(R+1)/2. If it is negative,
then 2n>=M-R-1>2R, hence n>R. In either case n>=(R+1)/2 and
p>n>=24. Standard Pell growth gives

    c0>B(B^2-1)^2, c0>2p, c0>2R.                  (4.3)

For example psi_B(p)>=(2B-1)^(p-1); at p>=6 this exceeds
B(B^2-1)^2. Also c0>=psi_B(2)=2B>2R, and the same growth
bound gives c0>2p.

The retained ordinary strong equation is

    (i c^2)^2=(B^2-1)(f^2-1), i=2r+1 != 0.

By the ordinary strong-rank lemma, whose large-coordinate condition is
now proved in (4.3), there is an m such that

    |f|=chi_B(m), p|m, c0|m, m>2p.                 (4.4)

The precise source is `upstream/PELL_RELAXED_AUXILIARY_PROOF.md`; its
signed use is documented in `upstream/ODD_SCALE_27_PROOF.md` and
`upstream/SIGNED_DOMAIN_29.md`. The argument applies to B,c0 and the
absolute values of f,i; no sign of X,Y,k,c is needed.

### 4.3. Recover the exact rank before orienting any sign

Put rho=|i|c0^2. The remaining auxiliary rows give

    rho^2 V^2-(rho^2-1)y^2=1,
    V=-c mod |f|, V=-R mod c0.

For an odd auxiliary index ell and a sign e0, standard Pell classification
gives V=e0 Q_((ell-1)/2)(rho^2). The odd Chebyshev identities are

    Q_j(1-B^2)=(-1)^j psi_B(2j+1),
    Q_j(0)=(-1)^j(2j+1).

Here rho^2=1-B^2 mod |f| and rho^2=0 mod c0. Squaring the first
congruence removes sign(c) and e0. The signed Pell step-down theorem,
with 0<2p<m from (4.4), gives ell=+p or -p mod m. The second
congruence gives ell=+R or -R mod c0. Because c0|m, we obtain
R=+p or -p mod c0. The strict intervals 0<R,p<c0/2 from (4.3) imply

    p=R.                                           (4.5)

This is exactly the sign-insensitive auxiliary interface used in the
parent, with its hypotheses re-established for negative X as well.

### 4.4. Unwrap the first index

Since p>n and p=R, the negative-sign alternative in (4.2), which required
n>R, is impossible. In the positive-sign alternative write
2n=R+1+vM with v>=0. If v>=1, then M>3R+1 forces n>R, again
impossible. Therefore

    sigma xi^(n-1)=1, 2n=R+1, R odd.              (4.6)

### 4.5. A single ratio bound covers all four X,Y signs

Put r0=n-1=(R-1)/2>=2. Elementary Pell growth gives

    c0/K = psi_B(2r0+1)/(2psi_P(r0+1))
          >= (1/2) ((2B-1)^2/(2P))^r0.

For U>=64 and Z>=6 one has

    (2B-1)^2/(2P) > U-3.                           (4.7)

Indeed B>=(U-1)Z-2 and P<=2UZ^2+1, and the difference after
clearing denominators is

    (2(U-1)Z-5)^2-(U-3)(4UZ^2+2)
      =4(U+1)Z^2-20(U-1)Z+31-2U > 0.

Positivity follows, for example, by writing this as
U(4Z^2-20Z-2)+(4Z^2+20Z+31); both parentheses are positive for Z>=6.
Combining (3.3) and (4.7) gives

    Z+1 > (U-3)^r0/2 >= 61^r0/2.

For r0>=2, 61^r0/2-1>2^(2r0+1). Thus

    Z>2^R.                                         (4.8)

The verifier checks the exact difference identity and its positive
coefficient expansion after U=64+u,Z=6+z. The proof above is universal,
not a finite-box verification.

### 4.6. Exclude reciprocal roots and recover the signed power

Let e=sign(c). Since R is odd, psi_A(R)=psi_B(R), even if A<0.
Thus c=e psi_A(R). Write D=lambda chi_A(R), lambda in {+1,-1}.
The standard polynomial Pell congruences, valid for signed A,H, are

    chi_A(R)-a psi_A(R)=2^R mod H,
    chi_A(R)+a psi_A(R)=2^(-R) mod H.               (4.9)

The odd H makes 2 invertible. For a direct verification the two base
values are A-a=2 and 2(A+a)=1 mod H; Pell recurrence gives every index.

If lambda=-e, the defining root row D-ac=X+gamma H gives

    X 2^R = -e mod H.

But (3.2), (4.8) give

    1<U2^R<UZ<4(U-1)Z-4<=|H|-1.

Hence neither positive nor negative X2^R can be congruent to either
unit +/-1 modulo |H|. This branch is impossible.

If lambda=e, then X=e2^R mod H. Moreover

    |X-e2^R| <= U+2^R < U+Z < 4(U-1)Z-3 <= |H|.

The multiple of H must be zero. We have proved the sign-uniform conclusion

    X=e2^R, R odd.                                 (4.10)

No positive-X assumption was used anywhere in sections 3--4.

## 5. Orient the sign and restore the parent

Now use the congruence (2.1). Since R is odd, 2^R=2 mod 3, whereas
-2^R=1 mod 3. Equation (4.10) and X=2 mod 3 force

    e=+1 and X=2^R.

In particular X is twice the square of the integer

    u=2^((R-1)/2).

Restore the old coordinates J_old=3J3+1 and w_scale_old=3w3+1 and
this value of u. Every retained parent residual is literally one of the
new residuals under the affine substitution, and its deleted square row
now vanishes. Thus every Q40 zero supplies a Q41 zero. The ordinary
Q41/native compiler/K215 calibration theorem yields a finite syntactic
ZFC refutation. This invokes Q41 only after its square guard is restored.

One may also read off the other signs: (4.6) with xi=+1 gives sigma=+1;
then e=sigma delta=+1 gives delta=+1. However, these extra conclusions
are not needed for the direct transfer to Q41.

## 6. Completeness of both affine restrictions

A finite ZFC refutation supplies the source34 canonical witnesses used
in Q41 completeness. They satisfy

    q=2^t, t odd, R=3 mod 4, X=2^R,
    J_old=(2^t-1)/(2^d-1), d=1064921 odd,
    w_scale_old=2^(R-t-2), R-t>=2 and R-t even.

Modulo 3, beta=1 and 2^t=2, so J_old=1 mod 3. Also R-t-2 is
nonnegative and even, so w_scale_old=1 mod 3. Hence the integers

    J3=(J_old-1)/3, w3=(w_scale_old-1)/3

exist. Keep every other parent coordinate and discard u. All 25 new rows
vanish. No claim is made that every Q41 zero admits these affine lifts;
the canonical completeness family is sufficient for existential equivalence.

This proves both directions of the main theorem.

## 7. Exact low-degree projections

These are bijections of the corresponding integer zero sets, unlike the
cofinal restrictions of section 6. Let q=beta(3J3+1)+1 and W=4(3w3+1).
An equation v=P(other coordinates) may be deleted after substituting that
integer polynomial for v in every other row. The inverse map restores v.
Each deleted row is checked to vanish identically after substitution.

### The sextic in 34 unrestricted integers

Make the triangular change tau_old=tau_tail+E(c-eta). Eliminate

    P=eta+zeta+E(c-eta), N=q(L+1), X=Wq,
    C2=c^2, F2=f^2, g=y^2-V^2.

The first Pell row becomes

    tau_tail^2+(2tau_tail-eta-zeta)E(c-eta)-1.

This exact cancellation keeps degree at most three. Six coordinates and
six defining rows disappear, leaving 34 variables and 19 cubic rows.
The sum of their squares has coefficient 4 at r^2 c^4, because the
only row involving r is I-(2r+1)c^2. It therefore has exact degree six.

### The octic in 29 unrestricted integers

Put k0=1-V+jc+hE and eliminate the eleven coordinates

    L=q^2-1, N=q^3, X=Wq, C2=c^2, F2=f^2,
    g=y^2-V^2, Baux=I^2,
    D=Wq+ac+gamma(4a+3), Delta=a^2+4a+3,
    zeta=k0-eta, P=k0+E(c-eta).

Every right-hand side uses only retained coordinates. The index-exposure
row is the monic definition of zeta, and the usual P row gives its
restoration. Fourteen rows remain, each of degree at most four. The ordinary
strong row I^2-(a^2+4a+3)(f^2-1) is the only row containing both a and f.
Its square contributes a^4 f^4 with coefficient 1. Thus the one
sum-of-squares equation has exact degree eight.

These companion methods use the centered-root and triangular substitutions
already exploited by source62; the new sign orientation removes their
last dedicated positivity witness. They are not presented as independent
discoveries of those elimination methods.

## 8. Evidence and metatheory

The newly proved statement is the signed power-recovery argument and its
residue orientation. The native compiler, fixed tuple semantics, K215
calibration, ordinary strong-rank lemma, and signed auxiliary step-down
remain explicitly inherited theorems. All are ordinary mathematics
formalizable in ZFC; this packet does not export an internally encoded
ZFC derivation or a new Lean/Rocq proof of the final polynomial theorem.

`build_verify.py` authenticates the retained sources against SHA256 and
Git blob identities, rebuilds every supplied coefficient byte, generates
the complete polynomial packets, verifies exact substitution identities,
expands each sum of squares with the fixed ports symbolic, and checks the
dimensions, liveness, total degrees, and nonzero coefficient certificates.
It uses only the Python standard library and works with Python -O.
These finite checks do not replace the unbounded proof above.

The comparison is to the inspected repository snapshot, not to every
possible Diophantine equation. The new residue substitutions enlarge the
expanded expressions while reducing their numbers of variables. Native
coefficient payload size is unchanged at 532,479 bytes; expanded coefficient
height and total circuit length are separate measures and are not claimed
to decrease.

## 9. A smaller direct-coordinate quartic with the same 40 unknowns

For a compact main quartic, retain the parent coordinates J and w_scale
unchanged and make only the affine substitution

    X_old = 3 X3 - 1.

Delete the row X_old-2u^2 and its private coordinate u. The complete
literal result is `quartic40_direct.json`, again with 40 integer unknowns
and 25 quadratic rows. Its sum of squares has exact degree four, with
coefficient 1 at tau^4, and only 393 symbolic monomials, compared with
388 for the source64 parent and 614 for the affine-J,w form above.

The proof in sections 3--5 applies with the following minor changes.
Set q=beta J+1 and W=4 w_scale. The coordinate identity now gives
X=3X3-1=2 mod 3, in particular X!=0. Since X=qW and q!=0, W!=0,
so |W|>=4. This yields the same |X|>=4Q bound even though zero was
an allowed input for w_scale before the retained equations were imposed.
Every remaining row is the same parent arithmetic row. The sign-uniform
argument therefore recovers X=e2^R with R odd; its residue forces
e=+1. Restore u=2^((R-1)/2) and X_old=3X3-1 to get a parent zero.

For completeness the canonical parent witnesses have X_old=2^R with
R odd, so X3=(2^R+1)/3 is an integer. Keep J,w_scale and every other
coordinate, and discard u. This gives the required direct zero.
Unlike the affine-J,w version, this completeness step needs no separate
modulo-three conditions on J or w_scale, and its orientation argument
does not require beta=1 mod 3. The actual bound coefficient tuple is
nevertheless exactly the same complete source34 tuple.

The direct variant is the recommended 40-variable equation when the
expanded expression is a secondary simplicity criterion. The affine-J,w
variant remains the source of the 34-variable sextic and 29-variable
octic: there X is a monic polynomial coordinate, which can be deleted
without introducing division by 3. No rational reconstruction is silently
used in either companion.
