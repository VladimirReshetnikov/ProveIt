# Even strong traces and unweighted first roots: 14/85/110 and 14/87/108

## Result and boundary

The two supplied fixed ordinary polynomials have fourteen unrestricted integer
unknowns. `integer14_degree85.json` has exact total degree 85 and 110 live binary
operations (63 multiplications, 24 additions, 23 subtractions).
`integer14_degree87.json` has exact degree 87 and 108 operations
(62 multiplications, 23 additions, 23 subtractions). Every scalar multiplication
and square is charged. Registers are abbreviations, not quantified unknowns.
The full six coefficient payloads, including the already-shifted MF, and their
finite reconstruction recipe are retained. The 85/110 point strictly improves
both degree and cost over the matched 86/112 point; 87/108 similarly improves
88/110. Neither dominates the lower-degree 82/113 point. These are not global
minimality claims, consistency assertions, or new end-to-end kernel certificates.

The new steps are an even strong-Pell normalization that licenses an unsquared
trace in the auxiliary congruence, and a first-root merger with coefficient one
rather than two. Ordinary zero-existence equivalence with the inherited calibrated
signed kernel is proved below. Composing its retained native/compiler/refutation
theorem gives, in ordinary ZFC, equivalence of universal integer nonvanishing and
syntactic Con(ZFC). Finite circuit checks are not substitutes for that theorem.

## 1. Complete literal polynomials

Both input lists, in order, are

    j,C,z,h,r,v,w,T,c,n,f,y,p2,p3 in Z.

The fixed ports are beta,K0,MC,MF,cone_A,cone_B. In particular
beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104. Common registers are

    J=6j+1, qm=beta J, q=qm+1, W=12w+4, X=qW, Y=v,
    F=(K0+W)C-z qm,
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    eta=c-Yk, ell=XY^2, L=ell k,
    I=(8r+4)c^2, Q=Delta(f^2-1), V=f(cT-R)-c,
    q3=q^3, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Z0=Un+M Klo+H(Y-q3),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2.

Choose the chart:

| equation | k | budget | Z |
|---|---|---|---|
| degree 85 | R+1+h ell | (Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq^2)^2] | Z0+UL |
| degree 87 | R+1+h E | (Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq3)^2] | Z0 |

For the 87 chart the literal evaluator computes L=E(Yk) and need not compute
ell separately. Finish, in either chart, with

    G=budget-[1+p2^2+p3(p3+1)],
    S=f^2-Delta I^2, uu=(V+y)^2, Ea=uu-Q(uu-V^2),
    Dt=1+L(L+k), U2=U^2, ga=U2 G, db=U2 Dt,
    N=(Z^2-ga-db)^2-4ga db,
    P=(N+1) S Ea-1.                                      (1.1)

The exact identity Ea=V^2-(Q-1)y(2V+y) identifies the auxiliary row.
Sharing uu saves one charged multiplication; Q-1 is not separately formed.
These are complete polynomial formulas. There is no division, variable exponent,
unspecified coefficient, hidden positivity convention, or search in either DAG.

## 2. Unweighted two-root extraction and exact maps

Unconditionally q is even and nonzero: beta>1 is odd and beta(6j+1) cannot be -1.
Thus |q|>=2, |W|>=4, |X|>=8. The integer a=(X+1)Y is zero or has |a|>=7, so
Delta=(a+2)^2-1>=3. H is odd and nonzero, hence U!=0. Also ell=XY^2 is even and
ell(ell+1)>=0, so Dt=1+ell(ell+1)k^2>=1.

At a zero of (1.1), all three integer factors are units. N is a square modulo4,
so N+1 cannot be -1. Since 4 divides I, S=f^2 modulo16 and S cannot be -1.
Consequently

    N=0, S=1, Ea=1.                                      (2.1)

Conversely these three equations imply P=0. Put rho=Z/U in Q. Then N=0 says

    (rho^2-G-Dt)^2-4G Dt=0.                              (2.2)

If G<0, its left side is strictly positive, so G>=0. Thus budget>0, whence
Y and k are nonzero. The bound budget<=q^2Y^2k^2 and |ell|>=8 give

    Dt >=1+ell^2 k^2/2
       >=1+8q^2Y^4k^2 > q^2Y^2k^2 >=budget>G.            (2.3)

Therefore rho is nonzero; otherwise (2.2) would give Dt=G. This exclusion
precedes every division by rho and includes G=0. Define proof-only rationals

    p=(rho^2+G-Dt)/(2rho), tau=rho-p.

Equation (2.2) gives p^2=G and tau^2=Dt. A rational number with integral square
is integral, by reducing its fraction to lowest terms. Therefore p,tau are
integers, with rho=p+tau. This proof requires neither distinct square classes nor
nonzero p; it includes shared classes and the zero-guard-root case. Equivalently,
the universal complex identity is

    (x^2-A-B)^2-4AB=product_(eps1,eps2=+/-1)
                         (x-eps1 sqrt(A)-eps2 sqrt(B)).  (2.4)

Let s=1 for the 85 chart and s=0 for the 87 chart. The corresponding even-trace
fifteen-variable kernel retains all common coordinates and p1,p2,p3, has carrier
numerator Zold=U nold+M Klo+H(Y-q3), and residuals

    Acar=(Zold+Uk)^2+4U(L Zold-U),
    Bstrong=f^2-Delta I^2-1,
    Caux=Ea-1,
    Guard=budget-1-p1^2-p2^2-p3(p3+1).                   (2.5)

Restore from any new zero

    p1=p, nold=n+sL-(2L+k)-p+tau.                       (2.6)

The identity

    Acar=(Zold+U(2L+k))^2-4U^2 Dt

shows Acar=0, since Zold/U+2L+k=rho-p+tau=2tau. The other three rows vanish
by (2.1) and p^2=G. Every restored coordinate is integral.

Conversely, at every zero of (2.5), (Zold/U+2L+k)^2=4Dt. A rational whose
square is integral is integral; its square is divisible by4, so it is even.
Write Zold/U+2L+k=2tau with tau integral. Delete p1 and set

    n=nold-sL+(2L+k)+p1-tau.                            (2.7)

Then rho=p1+tau and (2.4) gives N=0; S=Ea=1 are unchanged. These are total
maps on all zeros. Unlike the earlier coefficient-two merger, they are not
claimed to be polynomial coordinate automorphisms: the selected integral Pell
root is explicit proof data. It is precisely this freedom that removes a gate.

## 3. Why the unsquared trace is sound on signed zeros

We now calibrate the even-trace kernel (2.5). Its comparison kernel uses
Iold=(2rold+1)c^2 and Vold=fold^2(cTold-R)-c. For the 85 chart its complete
ordinary proof is `inherited_round20/inherited/PROOF.md`, Sections1--4
(source153); for the 87 chart it is
`inherited_round20/inherited/inherited/roots_baseline/source/FREE_SCALE15_PROOF.md`.
Their normalized strong and signed auxiliary lemmas are supplied in the same
`source/06_PROOF.md`, Sections2--4. We explicitly verify the changed hypotheses;
we do not apply the old zero theorem to the new rows without a restoration.

The carrier, budget, mask and first-index arguments do not use oddness of the
strong scale or the discarded square on f. At a zero of (2.5) they give
c!=0, kY!=0, q0=|q|>=16, x=|X|>=4q0, the strict centered strip, and

    q0(q0^2-1)<R<q0^4-2,
    |Y|>q0^2 and |XY^2|>3R+1                (85 chart),
    |Y|>q0^3 and |XY|>3R+1                  (87 chart).

Also the integral carrier yields Y even, M|H(Y-q^3), H|M Klo. These are
integer divisibilities; no nonunit has been canceled modulo H or M.

Put B=|a+2|, c0=|c| and Iplus=|8r+4|c0^2. Then Delta=B^2-1, B>=3,
Iplus>=c0 and fplus=|f| satisfies

    fplus^2-Delta Iplus^2=1, fplus>2Iplus.

In particular Iplus is positive and even; the zero-ordinate escape is excluded
because 8r+4 is never zero and c!=0. Pell classification gives
fplus=chi_B(m), Iplus=psi_B(m) with m>0. Here chi and psi are defined by
(B+sqrt(B^2-1))^m=chi_B(m)+psi_B(m)sqrt(B^2-1).

The auxiliary equation has Q=(Delta Iplus)^2 and the unchanged residue
V=-c modulo fplus. Its ordinary odd-index classification and folding therefore
recover c0=psi_B(p)>0, exactly as in the retained free-scale proof Section4:
the auxiliary odd index gives psi_B(lambda)=+/-c0 modulo fplus; fold to
0<=p<=m, and use psi_B(p)+c0<=2Iplus<fplus to force equality. This step does
not yet require a residue modulo c0. The first Pell classification gives
|k|=2psi_|2XY^2+1|(n0); the centered strip and base comparison give p>n0.
The appropriate first-index modulus above gives n0>=(R+1)/2 or n0>R.
Hence p>n0>=24 and c0>2p,2R.

The normalized rank lemma, which requires c0^2|Iplus but explicitly does not
require odd scale, now gives m=p nu with c0|nu. For clarity, strong divisibility of
psi gives p|m; putting D=chi_B(p), composition gives Iplus=c0 psi_D(nu).
The expansion psi_D(nu)=nu D^(nu-1) modulo c0, and gcd(D,c0)=1, imply c0|nu.

Here is the new parity step. The recurrence gives psi_B(m)=m modulo2 for every
integer B. Since Iplus is even, m is even. If c0 is even, c0|nu makes nu even.
If c0 is odd, psi_B(p)=c0 implies p odd, so m=p nu even again makes nu even.
The same recurrence gives chi_D(nu)=D^nu modulo c0 because D^2=1 modulo c0.
Therefore

    fplus=chi_D(nu)=1 modulo c0.                         (3.1)

The signed f may be either fplus or -fplus; consequently the new literal V obeys

    V=-c modulo fplus,       V=+/-R modulo c0.           (3.2)

The retained signed auxiliary-index theorem uses precisely these sign-insensitive
residues. To recall its mechanism, odd quotient identities give
psi_B(lambda)=+/-c0 modulo chi_B(m) and lambda=+/-R modulo c0. Squaring the first
congruence, using chi_B(2lambda)=1+2Delta psi_B(lambda)^2, and signed abscissa step-down
give lambda=+/-p modulo m. Since c0|m and 0<p,R<c0/2, they force p=R. Thus
allowing the additional sign in (3.2) changes no conclusion. The negative
first-index branch is then impossible and 2n0=R+1.

All subsequent inherited whole-product, sign and scale steps use only these
indices, the centered strip and the unchanged carrier. They give

    c>0, k>0, Y>0, X=2^R, R odd,
    Y=(2v_scale+1)q^3, H|Klo, 0<eta/k<1/4.              (3.3)

For completeness, the signed ratio bound gives |H|>x(x-3)^((R-1)/2);
together with the divisibility H|q^3 K it bounds the entire projected product
strictly below |H| and forces sign(c)X=2^R. The modulo3 restrictions select
sign(c)=+1. Only afterwards does integer cancellation recover the cubic Y
scale. No parity of Iplus was needed in that argument. In particular
B=a+2 is now positive and B=2 modulo8, and c=psi_B(R) is odd.

## 4. Fresh-witness restoration and constructive completeness

It would be invalid to keep f,T when restoring the old odd-scale kernel.
Instead, after (3.3), construct fresh witnesses while preserving every outer
coordinate, the carrier coordinate and all three guard coordinates.

Let

    m0=Rc, f0=chi_B(m0), I0=psi_B(m0).

Both R and c are odd. Composition and the normalized expansion show c^2|I0;
I0 and c are odd, so I0/c^2 is odd. Hence

    rold=(I0/c^2-1)/2 in Z.

The old strong row vanishes with fold=f0. The following signed auxiliary
completion works for EVERY odd R, not just R=3 modulo4. Write R=2d+1 and
let Q_d be the integer polynomial satisfying

    chi_Z(2d+1)=Z Q_d(Z^2),
    Q_d(0)=(-1)^d(2d+1),
    Q_d(1-B^2)=(-1)^d psi_B(2d+1).

They follow from Q_0=1, Q_1=4x-3 and
Q_(d+1)=(4x-2)Q_d-Q_(d-1). Set S0=Delta I0 and

    V0=(-1)^(d+1) Q_d(S0^2), u0=psi_S0(R).

Then S0^2 V0^2-(S0^2-1)u0^2=1, and the two quotient evaluations give
V0=-c modulo f0^2 and V0=-R modulo c. Since gcd(c,f0)=1 and f0^2=1 modulo c,

    Told=(V0+c+R f0^2)/(c f0^2), yold=u0-V0              (4.1)

are integers. They give Vold=f0^2(cTold-R)-c=V0 and the old auxiliary row.
Together with rold, these are a literal zero of the corresponding authenticated
odd-scale fifteen-variable kernel. Its calibrated theorem supplies a finite
syntactic refutation. This is a map on every new zero, not a silent canonical
assumption about R modulo4 or a claim that the new even scale fits the old one.

Conversely, any zero of either old fifteen-variable kernel has the outer data
(3.3), as its own ordinary proof establishes. Use the same f0,I0 above and double:

    f=2f0^2-1, I=2f0 I0.

Since B=2 modulo4 and m0 odd, the recurrence (or odd quotient polynomial)
gives f0=2 modulo4. Therefore I/(4c^2)=(f0/2)(I0/c^2) is an odd positive
integer. Set

    r=(I/(4c^2)-1)/2.

Then I=(8r+4)c^2, f^2-Delta I^2=1, and f=1 modulo c directly from f0^2=1 modulo c and f=2f0^2-1.
With S=Delta I form the same signed auxiliary quotient Vstar and ustar at
index R. It gives Vstar=-c modulo f^2, Vstar=-R modulo c, so

    T=(Vstar+c+Rf)/(cf), y=ustar-Vstar                  (4.2)

are integers. The quotient is integral because its numerator is divisible by f
and by c, which are coprime; f=1 modulo c is essential. It satisfies
V=f(cT-R)-c=Vstar. All outer, carrier and guard coordinates remain unchanged.
This constructs a zero of the even-trace kernel (2.5). Apply (2.7) to obtain a
new fourteen-variable zero. Both directions work on arbitrary old/new zeros;
the fresh strong witnesses, not an inverse change of T, supply completeness.

## 5. Exact degrees on the authentic fixed-coefficient slice

Let highest homogeneous parts be

    q0=6 beta j, X0=12q0 w, Y0=v, a0=X0Y0,
    F0=12wC-q0z, R0=-q0^3F0, ell0=X0Y0^2, U0=8q0^3a0.

In both charts the complete strong and auxiliary leading forms are

    [S]_12=-64a0^2 r^2 c^4,
    [Ea]_15=2a0^2 f^3 R0 y.                            (5.1)

The unsquared trace, not a generic-coefficient estimate, lowers the auxiliary
from degree16 to15.

For degree87, k0=R0, [G]_18=-R0^2q0^8 and [Dt]_18=ell0^2R0^2.
The unshifted Z has degree7, hence the complete norm top is

    [N]_60=U0^4 R0^4(q0^8+ell0^2)^2.                   (5.2)

Multiplying (5.1),(5.2) gives the whole degree87 top. In particular

    [j^56 w^8 v^8 z^5 r^2 c^4 f^3 y] P87
        =-2^91 3^64 beta^56 !=0.                       (5.3)

For degree85, k0=R0+h ell0 (the h term MUST be retained), and put

    T0=cone_A^2 Y0^2F0^2+4q0^2Y0^4+q0^6.

Then [G]_16=-k0^2T0, [Dt]_18=ell0^2k0^2. Although Z=Z0+UL has degree15,
the exact cancellation is

    (Z0+UL)^2-U^2Dt=Z0^2+2ULZ0-U^2(1+Lk),             (5.4)

of degree26. Therefore the square in N has degree56, while -4ga db has
complete degree58 top

    [N]_58=4U0^4 ell0^2 k0^4 T0.                       (5.5)

Again (5.1),(5.5) are the entire degree85 top. Its explicit attained coefficient is

    [j^48 w^10 v^12 z^5 r^2 c^4 f^3 y] P85
        =-2^89 3^58 beta^48 !=0.                       (5.6)

To isolate these coefficients set C=h=0 and select the pure q0 power in the
bracketed forms; every alternative has a different exponent. Exponents sum to
87 and85 respectively. The checker expands all coefficients of the formal norm
cuts and the full leading forms (18 and70 monomials), not a sampled line or a
replacement of the supplied tuple by generic constants.

## 6. A separate correlated-radical lemma

The following useful unbounded lemma was established during the twelve-variable
investigation; no improved twelve-variable endpoint is claimed from it here.
Let Fs,Dt be integers congruent to1 modulo3, G any integer, Q an integer divisible
by3, b,c integers and delta=Q-1. Choose algebraic square roots satisfying

    f^2=Fs, tau^2=Dt,
    t^2=[Q(fb-c)^2-1]/delta, g^2=G.

If rho=f+3tau+9t+27g is rational, then f,tau,t,g are rational. The result includes
negative radicands, coincident classes and the dependence of t on f.

Proof: let R3=Z_(3), and work in the integral closure of R3 in a normal number
field containing the roots. All f,tau,g are integral over R3. As delta is a unit,
t^2=alpha+beta f with alpha,beta in R3, so t is integral as well. Subtract the
conjugated trace equation. If an automorphism flips f, it gives f=3u with u
integral over R3. Then Fs/9=u^2 is rational and integral over R3, hence belongs
to R3, a contradiction. (The latter rational-integrality fact follows directly
from a monic equation and a reduced denominator.) Every automorphism fixes f,
so f is rational. Now the identical subtraction divided by3 forces tau rational.
With f rational its square equation makes t^2 rational and congruent to1 modulo3;
dividing the conjugate difference by9 similarly forces t rational. The original
trace then gives g rational. No real-positivity or independent-squareclass
premise was used. QED.

In particular, a polynomial norm for this setting must use the triangular roots
`t_(eps f)^2=[Q(eps f sqrt(Fs)b-c)^2-1]/delta`. Substituting a single fixed
auxiliary radicand into the independent four-root norm would be wrong. Raw or
centered attempts here remained dominated by existing eleven-integer points;
they are not represented as a new circuit record.

## 7. Reproducibility and precise closure

`build.py --check`, `check.py` and `reconstruct_coefficients.py` use only the
Python standard library. The independent checker imports neither producer nor
circuit implementation. It binds every register to a separately written formula,
checks all topology, coverage, liveness, inputs, six ports and charged counts,
verifies the signed factor identity, root maps, doubling and restoration identities,
whole degree cancellations and actual fixed-coefficient witnesses, and rejects a
separate corruption of every live binary gate. Python normal and -O executions
have identical explicit acceptance conditions. Modular Pell samples are labeled
diagnostics; the unbounded arguments above are not inferred from those samples.

`INHERITED_PINS.json` binds all 212 retained source files. Reconstruction recomputes
all six raw payloads (615883 bytes) by the inspected finite recipe, including all
943 tiles and 69230 basis convolution checks. It performs no blank-machine run,
network request, refutation search or proof-assistant rebuild. The authentic source
family is unchanged. The current comparison snapshot is
5274bc751a1566879ddc028a2d2a2af3c031654a; source attribution and earlier pins are
preserved, not rewritten to suggest that all inherited proofs were authored here.
