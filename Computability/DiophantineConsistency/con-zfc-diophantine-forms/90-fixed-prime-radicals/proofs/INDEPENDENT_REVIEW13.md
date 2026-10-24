# Independent mathematical audit of the thirteen-integer construction

## Verdict and scope

The proposed thirteen-unrestricted-integer construction is sound as an ordinary mathematical existence equivalence, provided its literal norm is the stated denominator-cleared five-root polynomial and its fixed coefficient ports are the exact whole source34/determinant tuple. The proof restores an integer zero of the incoming CRT17 parent from every new zero, and constructs a new zero from the parent's canonical finite-refutation witness family. It does not claim a bijection with every old zero.

This review independently checked the normalization, parity restrictions, positivity compression, valuation lemma, denominator exceptions, and coordinate restoration. It does not certify the as-yet-separate literal graph metrics or reprove the inherited native/compiler/refutation endpoint. This is review by another AI research worker, not external peer review or a proof-assistant certificate.

## 1. Complete framework being reviewed

The13 independent variables are

    j,C,z,h,r,v,w,T,c,s,u,vp,xi in Z.

The fixed tuple is beta,K0,MC,MF,cone_A,cone_B from source34 plus the calibrated determinant scales, with beta=2^1064921-1. Define

    J=6j+1, q=beta J+1, W=4(3w+1),
    F=(K0+W)C-z(q-1), X=qW, Y=(2v+1)q^3,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    k=R+1+hE, eta=c-kY, zeta=k-eta,
    ell=EkY, Atau=ell(ell+k)+1,
    I0=(2r+1)c^2, Df=1+Delta I0^2,
    Q=Delta^2 I0^2, delta=Q-1,
    V=Df(cT-R)-c, Cmain=1+Delta c^2, D0=X+ac,
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Z=eta*zeta,
    N=GZ-(s^2-G-Z+1)^2,
    S=24N-21-(6u-1)^2-(6vp-1)^2.

Let F32(t;d1,...,d5) be the product of the32 linear factors

    t - epsilon1 sqrt(d1) - ... - epsilon5 sqrt(d5),

over all signs. It is an integer polynomial in t,d1,...,d5, monic of degree32 in t and of degree16 in any one d_i. Put p=D0+Hxi, or more generally p=D0+H(xi+L) for a specified integer-polynomial shear L in the other variables. The polynomial to be set to zero is

    delta^16 F32(p;
       9H^2 Atau,81H^2 Df,Cmain,6561H^2 S,
       729H^2(QV^2-1)/delta).

The displayed division is definition shorthand only: after expansion or a division-free norm recurrence, multiplication by delta^16 clears every denominator. The delivered circuit must contain no division operation.

## 2. Preliminary facts hold on every integer assignment

beta is odd and beta=1 modulo3. Thus

    q is even and q=2 mod3,
    W is divisible by4 and W=1 mod3,
    X is divisible by8 and X=2 mod3,
    Y is divisible by8,
    a=(X+1)Y is divisible by24.

Consequently Delta=(a+2)^2-1 is odd, positive, divisible by3 and at least3. H=4a+3 is odd, nonzero, and divisible by3. These facts do not use a retained strong equation or any positivity guard. Since J=6j+1 cannot be zero and beta>17, |q|>=beta-1>16; Y is nonzero and |Y|>=|q|^3.

The quantity Q is divisible by9 on every assignment. Therefore delta=-1 modulo3 is never zero, even before recovering positivity. In particular denominator clearing creates no delta=0 solutions. The cases c=0 or I0=0 give Q=0, not an undefined denominator.

Writing b=XY^2 gives Atau=b(b+1)k^2+1. Because b is0 or-1 modulo3, Atau=1 modulo3. Also Df=1 modulo3, Cmain=1 modulo3, and S=1 modulo3. Both the numerator and denominator of

    B=(QV^2-1)/(Q-1)

are-1 modulo3, so v3(B)=0 and B=1 modulo3. All five *unweighted* radicands Atau,Df,Cmain,S,B are nonzero rational3-adic units.

Atau,Df,Cmain are positive on every assignment, but S and B may initially be negative. The proof must not assume their positivity or argue that there is only one imaginary radical. The general signed-radicand lemma below is what resolves these branches.

## 3. Signed-radicand valuation lemma

Let d1,...,dn be arbitrary nonzero rational numbers, possibly negative, with v3(di)=0. Let nonzero rational weights wi have pairwise-distinct v3(wi). If a signed sum of wi sqrt(di), interpreted in a complex multiquadratic splitting field, is rational, every sqrt(di) is rational.

Partition the radicands by their classes in Q*/Q*^2. In one class choose a representative d. Write sqrt(di)=ri sqrt(d), with ri rational; valuation0 of both radicands gives v3(ri)=0. The coefficient contributions epsilon_i wi ri therefore have pairwise-distinct valuations. Their sum cannot vanish: its unique least valuation survives after clearing denominators and reducing modulo3.

Square roots belonging to distinct Q-squareclasses are linearly independent over Q. One proof embeds them in their finite multiquadratic field and uses its distinct characters to project onto each class. This remains true for negative squareclasses; it does not assume independently available sign-flips for dependent generators. A rational sum requires every nontrivial class coefficient to vanish. The preceding paragraph excludes every such class, proving the lemma.

For the candidate the weights are

    3H,9H,1,81H,27H.

Writing e=v3(H)>=1, their valuations are e+1,e+2,0,e+4,e+3, all distinct. Thus a zero of the cleared norm supplies rational signed roots tau,f,D,sigma,y satisfying

    tau^2=Atau, f^2=Df, D^2=Cmain,
    sigma^2=S, y^2=B,
    p=D+H(3tau+9f+81sigma+27y).

The first four square values are integers, so tau,f,D,sigma are integers by rational-square-root integrality. The last root is initially only rational. In particular sigma^2=S forces S>=0, without a prior sign assumption.

## 4. Positivity and the auxiliary denominator are recovered in the right order

Since (6u-1)^2 and (6vp-1)^2 are at least1,

    24N-21=(6u-1)^2+(6vp-1)^2+sigma^2 >=2.

Therefore N>=1. From

    GZ-(s^2-G-Z+1)^2=N>0

we infer G>0 and Z>0. Indeed G and Z have the same nonzero sign; if both were negative, write G=-b,Z=-d with b,d>0. The square is at least(b+d+1)^2>bd=GZ, a contradiction.

Now eta*zeta>0 gives |k|>=2 and |eta|<|k|. As c=eta+kY,

    |c| > (|Y|-1)|k| > 1.

Thus I0=(2r+1)c^2 is nonzero and Q=Delta^2 I0^2>1. The rational root y satisfies

    QV^2-(Q-1)y^2=1.

The adjacent-coefficient Pell descent lemma now makes y integral. Its hypotheses Q>1 and integral V have been established without appealing to the deleted auxiliary equation or to a later rank-recovery theorem. The lemma's standard proof is reproduced in proofs/NORMALIZATION.md and retained source69.

## 5. Restoration of the literal CRT17 parent

The old parent's coordinates are restored as follows:

    J3_old=2j,
    f_old=f,
    r_old=(Delta(2r+1)-1)/2,
    T_old=f T,
    tau_half=2tau-(2ell+k),
    y_gap=y-V,
    gamma_old=xi+L-3tau-9f-81sigma-27y.

Here L=0 for the unsheared carrier. All expressions are integers: Delta and2r+1 are odd, and all roots have already been proved integral. Keep C,z,h,v,w,c,s unchanged. Choose the old three positivity coordinates to represent the positive integer N by

    N=1+t1^2+t2^2+t3(t3+1).

This representation is surjective onto positive integers by the same Legendre three-square lemma used in the inherited parent, and N>0 has been proved.

The old ordinary strong coordinate is

    I_old=(2r_old+1)c^2=Delta I0,

so I_old^2=Q=Delta(f^2-1). The old auxiliary expression is

    f_old*c*T_old-f_old^2*R-c
       =f^2(cT-R)-c=V.

The old main root D0+H gamma_old equals D by the norm carrier identity. The first half-centered row and auxiliary gap row follow respectively from tau^2=Atau and QV^2-(Q-1)y^2=1 by direct polynomial identities. The shared positivity row is restored by the representation of N. These are all five parent residuals.

The new zero therefore gives an integer zero of the exact CRT17 packet, with unchanged source34 coefficient ports. The old parent's soundness supplies the calibrated finite refutation. No signed root needs to be silently treated as positive; the parent permits all signs, and f_old*T_old depends only on f^2.

## 6. Canonical restrictions J=6j+1 and R=3 modulo4 are actually available

The precise source34 promise is in integrated package70,

    70-residue-orientation/integer/PROOF.md, Section6.

It states that a finite refutation supplies canonical witnesses with

    q=2^t, t odd, R=3 mod4, X=2^R,
    J_old=(2^t-1)/(2^1064921-1),
    W/4=2^(R-t-2), R-t even and at least2.

The odd exponent and beta=1 modulo3 give J_old=1 modulo3. Also beta*J_old=q-1 is odd, so J_old is odd. Therefore J_old=1 modulo6, and j=(J_old-1)/6 is an integer. The even exponent R-t-2 gives W/4=1 modulo3, so the existing w coordinate restriction is also available. This establishes the stronger parity slice without a new source or a mixed coefficient tuple.

R=3 modulo4 is an explicit canonical property, not an inference from an arbitrary satisfying assignment. It is used only in constructing completeness witnesses below.

## 7. An explicit normalized strong witness, with the required odd multiplier

Keep the canonical source geometry and put A=a+2>=2, Delta=A^2-1, c=psi_A(R), D=chi_A(R). Here A is even and R odd, hence c is positive odd. Define

    m=R*c,
    I0_new=psi_A(m), f_new=chi_A(m).

Composition gives I0_new=c psi_D(c). Since D^2=1 modulo c, the recurrence yields

    psi_D(n)=n D^(n-1) mod c.

At n=c this shows c^2 divides I0_new. The parity recurrence gives psi_A(n)=n modulo2 for even A, so I0_new is odd. Its quotient by c^2 is therefore a positive odd integer2r+1. Thus the proposed I0 form represents this normalized witness, and

    f_new^2-Delta I0_new^2=1.

No claim is needed that every old ordinary witness can be divided by Delta. Completeness constructs a new explicit witness while retaining all geometry and positivity coordinates.

## 8. The stronger auxiliary congruence is supplied constructively

Let M=Delta I0_new and R=2n+1. Since R=3 modulo4, n is odd. There is an integer polynomial Q_n with

    chi_Z(2n+1)=Z Q_n(Z^2),
    Q_n(1-A^2)=(-1)^n psi_A(R),
    Q_n(0)=(-1)^n R.

Choose

    Vstar=chi_M(R)/M=Q_n(M^2),
    ystar=psi_M(R).

Both are positive integers and M^2 Vstar^2-(M^2-1)ystar^2=1. Since

    M^2=Delta(f_new^2-1)=1-A^2 mod f_new^2,
    c|M,

the polynomial identities give

    Vstar=-c mod f_new^2,
    Vstar=-R mod c.

The normalized strong equation gives f_new^2=1 mod c. Hence gcd(c,f_new^2)=1, and

    T=(Vstar+c+R f_new^2)/(c f_new^2)

is an integer (indeed positive). It makes V=f_new^2(cT-R)-c exactly Vstar. This universal arithmetic argument is explicitly present in integrated source61 `positive/SIGNED_INDEX_LEMMA.md`, Section5. It is coefficient-independent and applies to the source34 canonical geometry; no compact44 coefficient is imported.

## 9. Positivity compression is complete

For every positive N, the exact identity needed is

    24N-21=(6u-1)^2+(6vp-1)^2+sigma^2.

The constructive proof in `proofs/PENTAGONAL_GUARD.md` is correct. Write M=24N-21=9^e M0 with9 not dividing M0. Since M0=3 modulo8, Legendre supplies an odd three-square representation. It is primitive modulo3. The integer matrix

    [[1,2,2],[2,1,-2],[-2,2,-1]]

satisfies L^t L=9I. Appropriate independent signs make x-y-z nonzero modulo3; applying L then makes all coordinates nonzero modulo3 and preserves oddness. Repeat e times. When e=0, divisibility of M by3 but not9 already forces all three coordinates to be units modulo3. Signs make each coordinate-1 modulo6. This proves the displayed identity.

This is the classical universality of three generalized pentagonal numbers, not a newly claimed number-theoretic theorem. Its use as a uniformly3-adic-unit radicand in the shared norm is the new application.

The canonical CRT17 source already supplies s and a positive N through its old positivity triple. Keep s and choose u,vp,sigma by this identity. The normalization changes neither G nor eta*zeta, so it changes neither N nor that positivity witness choice.

## 10. Completeness of the norm and logical composition

The unchanged canonical first and main geometry supplies integral tau and D. Sections7-8 supply f_new and ystar; Section9 supplies sigma. Set

    xi=gamma_old+3tau+9f_new+81sigma+27ystar-L.

This is integral and makes one signed factor of the five-root norm vanish. Therefore every finite calibrated refutation gives a zero of the13-integer equation.

Together with the explicit soundness restoration, this proves equality of existence with the calibrated source predicate. Negation gives the desired no-zero/Con(ZFC) equivalence by composition with the inherited ordinary theorem. The argument does not assume or decide consistency and does not create a new encoded object-language or kernel-checked ZFC derivation.

## 11. Items for the literal-artifact checker

The separate exact implementation audit should verify:

1. The graph expands to delta^16 F32 for the declared radicand order and shear.
2. The graph contains exactly the13 declared inputs and six correct fixed ports.
3. Every polynomial abbreviation is inlined or a DAG register, never an extra unknown.
4. Any norm recurrence division has been eliminated in the actual equation.
5. The fixed beta satisfies the parity and residue used above, and MF is not shifted a second time.
6. Exact degree and live arithmetic operation counts use the actual fixed coefficient slice.
7. Finite diagnostics are described as algebra/data verification, not evidence deciding the semantic no-zero statement.
