# Inputless ordinary-strong hybrid: 15 unknowns, six equations, degree 28

Final combined instance: use the complete four-port T4 tuple in ../bridge/T4_CONSTANTS.json. Its full compiler contract and canonical rank R = 3 modulo 4 are proved in ../bridge/BRIDGE_AUDIT.md. Historical packet06/08 coefficient discussions below document the derivation or a separate fallback, not a license to mix numerical ports. The arithmetic and witness arguments are unchanged.

## Result and precise status

This combines the raw-blank coefficient construction of packet 06 (also the
Start-only arithmetic skeleton of packet 08) with the ordinary-strong Pell
recovery of packet 02. All repository sources below are pinned at
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`; their original shared parent is
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

The new literal circuits give:

| Presentation | Positive unknowns | Equations | Exact degree | Binary operations |
|---|---:|---:|---:|---:|
| `hybrid_system61.json` | 15 | 6 | maximum 28 | 61 = 34M + 27A |
| `hybrid_product69.json` | 15 | 1 | 99 | 69 = 39M + 30A |
| `hybrid_sos78.json` | 15 | 1 | 56 | 78 = 40M + 38A |

These counts charge every binary addition, subtraction, and multiplication,
including arithmetic with fixed numerals. Comparisons and shared reuse are
free in a system; coefficient bit length is not charged.

Using the specified fixed coefficients, the ordinary mathematical argument
below is formalizable in ZFC and proves that each presentation has a positive
solution iff K215 halts on blank tape, hence iff ZFC has a finite refutation.
Consequently ZFC proves unsolvability iff Con(ZFC). This is not a proof of
Con(ZFC), not a global minimality claim, and not an end-to-end Lean/Rocq
formalization. The fixed native compiler and machine endpoint are imported
with the exact proof obligations described below, not inferred from toy tests.

The ordinary-strong and normalized-strong source systems are equivalent in
**existence of solutions**, not claimed to have the same positive zero tuples.

The arithmetic theorem is parametric over a fully proved compatible blank-input
compiler contract. The JSON explicitly selects packet 06 as its authenticated
fallback binding. A smaller coefficient recipe may replace all four ports
together after separately proving the same Start/impossible-End, carry, mask,
and completeness interfaces; the arithmetic circuit and degree proof do not
change. Merely satisfying the displayed congruences is not enough.

## Fixed coefficients and literal equations

The main instance uses the four coefficients beta=B-1, K, M_C, M_F^src from ../bridge/T4_CONSTANTS.json, with B=2^(5^18). The mathematical coefficient adapter is ../bridge/BRIDGE_AUDIT.md.

For a separate historical fallback, packet 06 uses beta=B-1, K, M_C, M_F^src with B=2^d, d=5^67, and M_F^src its native mask plus B-1. The following size figures describe that fallback only. The full finite
recipe is `sources/06-blank67/data/k215_constants.json`, together with
packet 06's `code/blank_helical.py` and `code/compiler_constants.py` at the
pin. The underlying machine is raw K215, not another packet's normalizer.
The recipe enumerates 1,420,903,358,357,108,792,377 center-valid windows
over 439 cell symbols. Its radix bit length is b=5^33. These are four
specific integers defined by a terminating finite algorithm, not four free
parameters. Their gigantic binary expansions have not been materialized.

The fifteen strictly positive unknowns are

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

All the following are polynomial abbreviations, not extra unknowns:

    q=beta J+1,            C=q-F-alpha,
    X=wq,                 Y=sq^3,             E=XY,
    k=eta+zeta,            c=kY+eta,           a=E+Y,
    H=4a+3,               A=a+2,              Delta=a^2+H=A^2-1,
    D=X+ac+gamma H,
    G=(q-1)(q-F)+alpha=q(q-F)-C,
    R=G(q^2-1)+(M_C+q M_F^src)J,
    V=c(Tf-1)-Rf^2,
    I=ic^2,               Baux=Delta(f^2-1), L=E(kY).

The six equations are

    tau^2-L(L+k)=1,
    D^2-Delta c^2=1,
    Baux(V^2-y^2)+y^2=1,
    k-hE-R=1,
    (K+w)C+(q-F)-z(q-1)=1,
    I^2=Baux.

For a single product polynomial, define

    N0=tau^2-L(L+k),      N1=D^2-Delta c^2,
    Na=Baux(V^2-y^2)+y^2,
    Nk=k-hE-R,            Nt=(K+w)C+(q-F)-z(q-1),
    Ns=1+I^2-Baux.

Then

    P69=N0 N1 Na Nk Nt Ns-1.

For the lower-degree single polynomial use the sum of squares of the six
displayed residuals, with the sixth residual I^2-Baux. The JSON circuits
contain only binary +,-,* gates and fixed constants. There is no hidden
division, variable exponent, variable-length conjunction, or computation
predicate in any equation.

## 1. Every product zero satisfies the six equations

The following proof includes the system case. A product zero makes each
factor an integer unit. The negative Pell equation x^2-v(v+1)z^2=-1,
v>1, has no integer solution by descent using the inverse unit
2v+1-2 sqrt(v(v+1)); here v=XY^2. Thus N0=1.

Delta is 0 or 3 modulo 4, so N1 cannot be -1. Furthermore
Baux=Delta(f^2-1) is 0 or 1 modulo 4. If Delta=0, Ns is
1+I^2 modulo 4; if Delta=3, Ns is I^2+f^2 modulo 4. In neither
case is it -1. Thus Ns=1 and I^2=Baux>0. Now Na modulo 4 is
either y^2 or V^2, so Na also cannot be -1. Therefore

    N0=N1=Na=Ns=1,
    Nk=epsilon, Nt=nu, epsilon,nu in {+1,-1}, epsilon nu=1.

One must not assert C>0 yet. Since

    (q-F)-z(q-1)=1-F-(z-1)(q-1)<=0,

C<=-1 would give Nt<=-(K+w)<=-2, impossible. Thus C>=0 and
q-F=C+alpha>0. The boundary C=0 really is possible at this preliminary
stage (for example F=2,z=1 gives Nt=-1), so its exclusion is postponed.

The authentic masks satisfy 0<M_C,M_F^nat<B-1. Hence

    q <= G=q alpha+(q-1)C <= q^2-q,
    0<(M_C+q M_F^src)J<(q-1)(1+2q),
    q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2.

Since q>=B>=16, these imply

    R-2>3q+1,  E>=q^4>R+2,  a>R+2,  R<a<Delta.

No computation, dyadic typing of q, or auxiliary Pell rank was used here.

## 2. Bootstrap before ordinary-strong rank or auxiliary positivity

Put P0=2XY^2+1. The first Pell equation gives

    tau=chi_P0(n), k=2 psi_P0(n), n>=1.

Here chi and psi are the integer Pell recurrences with parameter shown.
Since P0 is 1 modulo E,

    2n=R+epsilon+vE, v>=0, n>=(R-1)/2>=24.

The nonnegative v follows from 0<R+epsilon<E. The main norm gives
D=chi_A(p), c=psi_A(p), p>=1. As P0>A and c>k, p>n.
Elementary Pell growth consequently gives

    c>A Delta^2, c>2p.

Also k=R+epsilon+hE>2R, so c>2R. This is the required noncircular
large-main-index bootstrap. It uses neither auxiliary positivity nor the
desired conclusion p=R.

## 3. Ordinary strong norm: the essential integrality argument

The change from normalized strong to ordinary strong is not an unconditional
algebraic equivalence. The isolated equation I^2=Delta(f^2-1) may have
rational Pell coefficients I/Delta. The large-main-index condition above
is essential.

The precise imported lemma, proved in
`Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`, is:

    If A>=2, c=psi_A(p)>A Delta^2, I=ic^2>0,
    and I^2=Delta(f^2-1), then for some m>0,
    f=chi_A(m), p|m, c|m, and I=Delta psi_A(m).

For completeness, its integrality mechanism is as follows. Write
Delta=d0 s0^2 with squarefree d0>1, and let F+y0 sqrt(d0) be the
least positive integer-coefficient norm-one unit. Write A=chi_F(e),
S=psi_F(e), Delta=(F^2-1)S^2. Composition gives psi_F(ep)=Sc.
The ordinary strong norm gives an integer unit f=chi_F(n) and
I=(F^2-1)S psi_F(n). Put T0=(F^2-1)S<=Delta and
g=gcd(n,ep). Strong divisibility gives h0=psi_F(g)>=c/Delta.
If g<ep, then 2g<=ep, so 2h0^2<psi_F(ep)=Sc<Ac,
contradicting c>A Delta^2. Thus ep|n. Writing n=em yields
p|m, f=chi_A(m), I=Delta psi_A(m). Finally the binomial
expansion at m=pb and gcd(chi_A(p),c)=1 gives c|Delta b;
gcd(c,Delta)=gcd(p,Delta) divides p, hence c|pb=m.

In particular

    f^2-1=Delta psi_A(m)^2=i c^2 psi_A(m),

so c^2 divides f^2-1. This is obtained from the rank lemma, not by
illegally dividing the original strong equation, and it does not require
Delta|i. Also m>=c>2p.

## 4. Recover the missing auxiliary coordinates and main index

The ordinary strong equality and c>A Delta^2 imply

    f>c^2/sqrt(Delta)>c^2/A>2c,
    f^2>Delta+c,
    Baux-(Rf^2+c)=(Delta-R)f^2-Delta-c>0.

From Na=1,

    Baux V^2-(Baux-1)y^2=1.

If |V|>1, then |V|>=2Baux-1: otherwise
(V^2-1)=(Baux-1)(y^2-V^2), with y>=|V|+1, is impossible.
But T>0 gives V>-(Rf^2+c)>-Baux, excluding V<-1. The
congruence V=-c modulo f, with 2<c<f/2, excludes 0,+1,-1.
Thus V>1. Define the integers

    o=cT-Rf,
    j=Tf-1-R(f^2-1)/c.

Integrality of j uses c^2|(f^2-1), just established. The identities
of=V+c and jc=V+R make o,j positive and give

    V=of-c=jc-R.

Apply the signed auxiliary step-down lemma with target R. Its hypotheses
are now c=psi_A(p), f=chi_A(m), c|m, c|I, I^2=Delta(f^2-1),
0<p,R<c/2, m>2p, and the last two congruences. It gives p=R.

Explicitly, Pell classification of (IV)^2-(I^2-1)y^2=1 gives
IV=chi_I(ell) for odd ell. Writing ell=2u+1, the odd quotient
polynomial Q_u satisfies

    V=Q_u(I^2),
    Q_u(1-A^2)=(-1)^u psi_A(ell),
    Q_u(0)=(-1)^u ell.

Reduction modulo f and c yields ell=+p or -p modulo m and
R=+p or -p modulo c. The strict half-interval bounds force R=p.
The signed chi step-down needed here follows by reducing an index
modulo 2m and using monotonicity together with
2 chi_A(m-1)<chi_A(m).

Return to 2n=R+epsilon+vE. If v>=1, E>R+2 implies n>R=p,
contradicting p>n. Thus v=0. If epsilon=-1, then p=2n+1;
Pell duplication, chi_A(2)>P0 and A>Y+1 give

    c=psi_A(2n+1)>A k>k(Y+1),

contrary to kY<c<k(Y+1). Hence epsilon=nu=1. Now Nt=1 rules
out C=0, establishing C>0. Every product zero therefore satisfies
the six individual equations; the reverse implication is immediate.

## 5. From the equations to a genuine blank computation

At p=R=2n-1, the lower Pell-ratio argument gives X<a and 2^R<a.
The recurrence for chi_A(R)-a psi_A(R), reduced modulo H=4a+3,
gives X=2^R modulo H, hence X=2^R exactly. This argument needs
X>=q, Y>=q^3 and 6XY^2>a, not the old upper-ratio margin.
Since q|X, q is a power of two, and R>3q implies q^3|X.
Thus the symmetric half-binomial kernel applies after the proof-only
rescaling X=(X/q^3)q^3. Its ordinary strong coordinate is exactly i,
not an attempted quotient i/Delta.

The kernel yields the population threshold, and beta|q-1 implies
q=B^N. The shifted packing identity at C (no input marker) is

    S=(C-1)+qF,
    Tmask=(M_C J+1)+q(M_F^nat J-1),
    R=(q^2-S)(q^2-1)+Tmask.

The native inverse-population, convolution, clean-band and anchor lemmas
recover a genuine cyclic local tableau. Its origin has Start and the
globally impossible selector 1 is forbidden. Packet 06's blank-helical
lemma extracts the finite rectangle containing that Start. Its initial
row is entirely blank with one K215 head; the final row is halting.
Multiple Starts elsewhere are harmless. No input-erasing normalizer or
End marker is needed.

These finite-window and kernel lemmas are substantive imported results.
The local arithmetic verifier does not prove them. The relevant audited
interfaces are in packet 06's `proofs/pell_lemma_audit.md` and
`proofs/blank_helical_proof.md`, copied beside this proof.

## 6. Completeness and the one-way coordinate map

If K215 halts on blank tape, packet 06's completeness proof supplies a
positive normalized-strong zero. It chooses a padded helical tableau,
tunes the actual packed R using dummy bits, proves the canonical mass,
population and parity bounds, and supplies fresh Pell witnesses at that
same R. None of those steps requires any assumption about consistency.

Keep every coordinate except put i_ordinary=Delta i_normalized.
The normalized equality f^2-1=Delta i_normalized^2 c^4 gives

    (i_ordinary c^2)^2=Delta(f^2-1).

The auxiliary coefficient is unchanged; the other four equations are
unchanged. Thus the new system has a positive zero. In reverse, the proof
above decodes directly using the ordinary rank lemma. It does not assert
i_ordinary/Delta is an integer for every new zero.

The K215 endpoint calibrates blank halting against the intended ZFC finite
refutation predicate. This last passage uses the ordinary calibration
argument formalizable in ZFC, not an assumption that Lean's own soundness
is provable in ZFC.

## 7. Uniform exact-degree and operation certificates

Let Q=beta J, k0=eta+zeta, C1=Q-F-alpha be homogeneous leading forms.
Then X_top=wQ, Y_top=sQ^3, a_top=wsQ^4,
c_top=k0 sQ^3 and Delta_top=w^2s^2Q^8. In factor order the exact
degrees are 22,18,28,7,2,22. Their leading forms are

    N0: -k0^2 w^2 s^4 Q^14,
    N1: 8 gamma k0 w^2 s^3 Q^11,
    Na: k0^2 w^2 s^4 Q^14 T^2 f^4,
    Nk: -h w s Q^4,
    Nt: w C1-zQ,
    Ns: i^2 k0^4 s^4 Q^12.

For N1 the apparent degree-22 cancellation is exact:

    D^2-Delta c^2
      =2ac(X+gamma H)+(X+gamma H)^2-Hc^2.

Its unique degree-18 contribution is 8 gamma a_top^2 c_top.
The product's degree-99 homogeneous part is therefore

    8 Q^55 h gamma i^2 k0^9 w^7 s^16 T^2 f^4 (w C1-zQ).

For example the coefficient of
J^56 h gamma i^2 eta^9 w^7 s^16 T^2 f^4 z is
-8 beta^56, nonzero for the authentic beta>0. Thus degree 99 is
uniformly exact. Only the auxiliary residual has degree 28, so the
sum-of-squares degree is exactly 56. These are identities of formal
polynomials, not simplifications that hold only at solutions.

Relative to packet 06's 67-gate source, replace its four-row strong block
by six rows (same three multiplications, two additional additions), use
Delta(f^2-1) in the auxiliary factor, and subtract 1 rather than Delta.
This yields 69 gates. For the system compare I^2=Baux directly, remove
the two strong-factor additions and the six product finalizer gates:
61 gates. Six residual subtractions, six squares and five sums give
61+17=78 gates for the SOS.

`build_hybrid.py` reads JSON as data only, emits all three full circuits,
checks schema/dependencies/liveness and exact counts, tests exact local
source identities under i_o=Delta i_n, and independently evaluates line
specializations over a finite field to attain the displayed degrees.
Those degree diagnostics supplement, not replace, the uniform leading-form
proof. No downloaded program, astronomical enumeration, proof-assistant
build, or hypothetical K215 accepting witness was executed.

## 8. Ordinary integer domain

The positive domain is essential. Directly reading P69 over all integers
is not justified. A uniform safe conversion is to replace each of the
15 variables by 1+u^2+v^2+w(w+1). This form is positive for every
integer triple and represents every positive integer by Legendre's
three-square theorem. It yields 45 unrestricted integer unknowns,
degree 198 for the product or degree 112 for the SOS.

As in packet 06, tau and y occur only squared. At an admissible zero
neither can be zero (the first norm and auxiliary norm exclude this).
They may therefore remain signed, reducing that elementary conversion
to 41 integer variables. This proof does not claim optimality of that
conversion or preempt further signed-coordinate improvements.
