# Independent adversarial review of the twelve-positive merger

## Outcome and limits

PASS for the new local reduction, after deletion of one invalid optional
shortcut that was not used by the main proof. The complete saturation-first
argument survives unchanged. The circuit and all stated counts are unchanged.
This is an independent AI-assisted mathematical review within this project,
not external human peer review or an end-to-end proof-assistant certificate.

The reviewed claim is conditional on the explicitly preserved authentic-tuple,
ordinary compiler/rank, source50 absorber, and literal K215/refutation
interfaces. This review does not silently promote their finite audits into
unbounded semantic proofs. The complete coefficient tuple, especially shifted
MF, must be kept intact.

The local equation is P=Nt(1+Nmain)(1+Ninner)-1 on the twelve positive
variables in the inert JSON. Its exact degree is 316 and its operation count
is 102; the three-equation forms use 95 or 94 operations, with residual
degrees 2,26,288. The optional sum-of-squares version has degree 576 and
103 operations.

## Independent finite work

`check_merger_independent.py` imports neither the builder nor its checker.
It expands the four-factor norm over the formal ring with generators
sqrt(p),sqrt(r), reducing their squares to independent indeterminates p,r.
The result is exactly the displayed integer polynomial, with 35 terms.
It separately checks all four DAGs for valid operand order, live gates,
live inputs, and exact operation counts. Sixteen independent literal
formula evaluations agree with the product DAG. All four possible square
residues modulo 4 exclude -2.

A separate bounded diagnostic examines 79,600 rational-Pell candidates
(m=2..200, V=1..400). Every rational square found has integral square root.
That bounded result is NOT the proof of saturation; the universal proof
is checked below. Normal and optimized Python produce byte-identical
`INDEPENDENT_CHECK.json` receipts. These checks do not claim to certify
unbounded solvability or the degree upper bounds by sampling.

## 1. Four-factor identity and degenerate square classes

For independent x,p,r,d,Z put

    M=d(x^2+p+r)-Z,
    C0=M^2+4d^2[x^2(r-p)-pr], B=2dp-M.

Multiplying d(x-rho-b)^2-Z over both signs of rho and b, with rho^2=p
and b^2=r, first gives C0+4dx(2dp-M)b and then

    C0^2-16d^2 x^2 r B^2.

The independent formal expansion verifies this identity universally,
including square, repeated, zero, and negative specializations. For the
soundness proof, p=Q>1 and r=c^4 f^2 A>0, so all four factors are real.
A zero product therefore supplies a zero real factor even when some
formal factors coincide. Independent Galois sign choices are not assumed.

Pairing the two signs of sqrt(d Eaux) in the eight-linear-factor norm
produces d times the corresponding quadratic factor, so the total is
d^4 Ninner. The circuit never divides by d. The soundness proof explicitly
has d>0 before considering the zero-set interpretation.

## 2. Unit guard and excluded zero cases

U=4q^4 implies Nmain=Dstar^2 modulo 16. The norm formula gives
Ninner=C0^2 modulo 16. If the product equation vanishes, all three integer
factors are units. A value -1 for either norm+1 factor would require
that norm to equal -2, impossible even modulo 4. Hence both norm factors
are +1, both residuals vanish, and Nt=1. No positivity assumption on the
individual integer factors is needed.

The explicit positive substitution f=f0+1 gives f>=2. With Delta>0,
Q=Delta(f^2-1)>1 and d=Q-1>0. Thus f=1, Q=0, and d=0 are genuinely
excluded by the witness domain, not by an unmentioned division.

If V=0, Eaux=-1 and every real norm factor equals a nonnegative square
multiplied by d, plus the strictly positive c^4 M2^2. It cannot vanish.
For any other integer V, Eaux=QV^2-1>=Q-1=d. Therefore the positive
root y=sqrt(Eaux/d) exists and y>=1. Negative V is allowed throughout.
No unsound assumption that V is a positive auxiliary coordinate occurs.

## 3. Separation works before main-index growth

The author's uniform bounds are stronger than the initially suggested
main-Pell lower bound. The transport interface gives X>=16, Y>=4096,
E=XY, k>=2. Thus

    a+2=E+Y+2<2E,
    ell-k=k(EY-1)>=2EY-2>2E>a+2.

Also rho=sqrt(Q)<f(a+2), and
ell<sqrt(A)<ell+k because A=ell^2+k ell+1 and k>=2. Consequently

    0<rho/c^2<f ell<f sqrt(A),
    rho/c^2+f sqrt(A)<f(a+2+ell+k)<2f ell=M2.

As y>=1, the largest weighted radical M2 y strictly exceeds the sum
of the other two, and the middle radical strictly exceeds the smallest.
These strict inequalities already hold before ordinary rank, Pell index
comparison, or integrality of the roots. There is therefore no circular
bootstrap hidden in root recovery.

A rational signed sum of the three radicals can only have zero total
coefficient in each nontrivial square class. The largest term cannot be
canceled by any subset of the smaller terms, so its square class is rational.
Then the middle and smallest cannot cancel each other either. This proves
rationality of all three roots even if two or three original radicands
have the same square class. Since Q and A are integers, rho and sqrt(A)
are integers. Rationality of y alone is not enough; the next lemma is essential.

## 4. Rational Pell saturation, including negative V

Let m>=2, V integer, and y rational satisfy

    m^2 V^2-(m^2-1)y^2=1.

Neither V nor y can vanish. Write y=b/r in lowest terms, r>0. Multiplying
through by r^2 and using gcd(b,r)=1 gives r^2|(m^2-1). The positive integer
D0=(m^2-1)/r^2 is nonsquare, since division by a square preserves square class.
Both (m,r) and (m|V|,|b|) are nontrivial positive integer-coordinate Pell
solutions for D0. Express them using the fundamental positive norm-one unit
with indices j,l>=1. Their abscissas are chi_j=m and chi_l=m|V|, so
chi_j divides chi_l.

The identities chi_(n+2j)=-chi_n and chi_(2j-n)=-chi_n modulo chi_j
reduce l, up to sign, to an index in [0,j]. Strict growth gives
1<=chi_h<chi_j for 0<=h<j, so divisibility requires h=j. Hence l is an
odd multiple of j. Pell composition gives psi_j|psi_l, which here says
r divides |b|. Coprimality then forces r=1. Thus y is integral.

This uses only the ordinary classification and addition formulas for
integer-coordinate Pell solutions. No unjustified cancellation of a
nonsquare discriminant or square factor is involved. It covers negative
V through the absolute abscissa m|V|.

Once y and sqrt(A) are integers, the signed zero-factor identity

    t=+/-rho/c^2 +/-f sqrt(A) +/-M2 y

forces rho/c^2 to be an integer. Its positive value is the restored i.
Therefore (ic^2)^2=Delta(f^2-1) is recovered exactly, before invoking
ordinary strong rank.

A draft also proposed deriving c^2|rho from c^2|d rho and gcd(rho,d)=1.
That implication is false: rho=8, d=63, c=3 is a counterexample. The
paragraph has been deleted. The valid saturation-first proof above never
uses that shortcut. This correction affects neither the equation nor its
main proof, and must not be reintroduced.

## 5. Absorber and dependency order

Nmain=0 yields a rational square root Dstar/U of integer G, hence an integer.
Its positivity follows from Dstar>U b0-Hk>ak(UY-5)>0; the transport bounds
supply R>0, H<5a, and UY>5. The congruence U|H(k-R-1) is obtained without
canceling H. All signs are checked before classifying positive Pell indices.

After the inner roots are recovered, the two Pell equations give p>n>=1.
The first recurrence supplies k=2n modulo 4EY, and U divides4EY.
The common divisor gcd(U,H) is at most3: H is odd and congruent to3 modulo q;
if 3 divides q, H is 3 modulo 27, so its 3-adic valuation is exactly 1. Thus
mu=U/gcd(U,H)>=4q^4/3>R+1. The congruence
2n=R+1 modulo mu forces n>=(R+1)/2, with no sign assumption on a deleted
quotient. In particular n>=25 and p>=26, giving the strict hypothesis
c>(a+2)Delta^2 needed by the inherited ordinary strong-rank lemma.

Only now is ordinary strong rank applied. It supplies f=chi_(a+2)(m),
p|m, c|m, m>2p, and c^2|(f^2-1). The inherited signed auxiliary-index
argument is therefore applicable to the possibly negative V and gives p=R.
Since 1<=n<R and mu>R, the previous congruence then forces 2n=R+1.
The quotient u=k-2n is positive and divisible by 4EY, hence by E and U.
The restored h=u/E is positive; gamma_old=(g-b0)/H is integral and positive
because g>(a+1)c and c>X. This recovers all required ordinary compiler
coordinates rather than merely producing rational placeholders.

## 6. Constructive completeness and transport boundary

For a canonical positive ordinary witness, u=k-2n is a positive multiple
of 4EY and U. The replacements

    gamma=gamma_old+u/U, f0=f-1,
    t=i+f tau+M2 y

are positive integers. The strong equation with positive i forces f>=2,
so f0 does not fall on the forbidden zero boundary. Substitution gives
Dstar=Ug and makes a real norm factor vanish exactly. All other coordinates
are unchanged and Nt=1 persists.

For the shifted system z_old=z+1 is an exact polynomial substitution.
The canonical bound w=2^R/q>q>F and Cw>0 implies z_old>=2, making the
new z positive. The shift therefore does not merely preserve unrestricted
integer solutions: its positive-domain converse is justified.

## 7. Exact degree checks

With q0=beta J, E0=w s q0^4, c0=(eta+zeta)s q0^3, their degrees are 1,6,5.
The new quantities have leading terms

    Q0=E0^2 f0^2, V0=c0 T f0,
    (M2)0=2f0 E0 c0,
    Z0=4E0^4 c0^8 T^2 f0^6.

Z has degree 72, strictly above the at-most-58 degree of all other summands
in M. Consequently M_top=-Z0, C0_top=Z0^2, and
Ninner_top=Z0^4 at degree 288. The subtracted term has degree at most 238,
so it cannot cancel this leader. The leader is nonzero for every beta>0.

For Nmain, expanding the a^2 c^2 cancellation first gives the degree 26
leader 128 q0^8 E0^2 c0 gamma. The two absorber correction terms have
bounds 25 and 20. The transport leader is
w(q0-F-alpha)-zq0, nonzero for every beta>0. Multiplication therefore gives
the degree 316 leader

    2^15 q0^8 E0^18 c0^33 gamma T^8 f0^24
      [w(q0-F-alpha)-zq0].

This independently confirms the analytic degree argument, without treating
finite random rays as a universal upper-bound proof. Only the inner residual
reaches degree 288, so the sum of squares has exact degree 576.

## Final disposition

The core merger passes this adversarial review. Important safeguards are:
keep f=f0+1; retain the nonzero-V argument; use weighted square-class
separation rather than independent sign automorphisms; prove rational Pell
saturation before restoring i; establish the absorber's early index bound
before ordinary rank; and retain the mod 4 unit guard for the product.
The deleted divisibility shortcut and arbitrary substitutions of compiler
ports are not part of the accepted proof.

## Circuit-only common-factor refinement

The final evaluator reuses c^4 f^2 in r=c^4 f^2 A and
Z=4(c^4 f^2) ell^2 Eaux, instead of separately constructing
M2=2f ell and c^4 M2^2. This is the exact identity
c^4(2f ell)^2=4(c^4 f^2)ell^2. The independent literal formula checker
still uses the original M2 expression and agrees with the revised DAG.
The two-gate reduction changes no polynomial, proof, or degree. Final counts
are 102,95,94,103 for product, system, shifted system, and sum of squares.
