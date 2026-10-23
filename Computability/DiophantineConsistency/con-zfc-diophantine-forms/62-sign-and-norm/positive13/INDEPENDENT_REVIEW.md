# Independent review of the thirteen-positive centered norm

## Verdict and review scope

**No local mathematical defect found.** The supplied thirteen-positive
polynomial has the same existence condition as the identified ordinary
fourteen-coordinate absorber, with the complete compact44 tuple. Its
exact degree is 114 and its literal circuit has 83 live binary gates.
The proof establishes both directions without a square-class independence
assumption or an unproved sign/cofinality premise for the new coordinate.

I reviewed `PROOF.md`, its literal `polynomial.json`,
the complete coefficient binding, the original source50 absorber proof,
the ordinary strong-rank and signed auxiliary proof, and the compact
tuple's transfer statement. I did not alter the author's files.

The independent checker `p13_independent_check.py` imports neither the
author's builder nor the author's checker. It computes complete sparse
polynomial expansions at the two genuine cancellations, propagates exact
highest homogeneous forms elsewhere, verifies the full final leading
form, checks all gate/input liveness, authenticates the coefficient
payloads, and checks the actual mask invariants and all source pins.
Its receipt is `REVIEW_CHECKS.json`.

The reviewed primary polynomial SHA-256 is
`37c2382bbcdf137eee9714c6d59ead0c9215c71ff6bd0edb502191d16542a85b`.
The semantic conclusions below are ordinary mathematical review; the
finite checker does not prove the native compiler or the K215 calibration,
and neither review supplies an end-to-end proof-assistant certificate.

## 1. The product-unit guard is sound

From

    Nt (1+Nmain) Ns (1+N) = 1

each integer factor is a unit. Since U is divisible by 4, Nmain is a
square modulo 4, so it cannot be -2. Similarly N is a square modulo 4,
because its correction is divisible by 4. Thus Nmain=N=0.

For every integer a, Delta=(a+2)^2-1 is 0 or 3 modulo 4. Therefore
Q=Delta(f^2-1) is 0 or 1 modulo 4. The factor Ns=1+I^2-Q consequently
has residue 0, 1 or 2, and cannot be -1. Hence Ns=1 and then Nt=1.
This proves the simultaneous conclusions Q=I^2, Nt=1, Nmain=N=0.
No sign of an individual factor was assumed before this modular argument.

The positive input domain implies c>1 and I=i*c^2>1. Consequently
d=Q-1=I^2-1>0. The case f=1 is excluded by Q=I^2>0. All denominators
used in root restoration are therefore nonzero for proved reasons.

## 2. Root restoration is direct and complete

The exact identity

    (d(x^2-A)-e)^2-4dAe
      = (d(x^2+A)-e)^2-4d^2*x^2*A

was independently expanded. With d,x,A positive, a zero makes

    tau0 = (d(x^2+A)-e)/(2dx)

a rational square root of the integer A. Thus tau0 is an integer, and
the identity gives d(x-tau0)^2=e. There is no premise that distinct
formal radical signs act as independent field automorphisms.

In the actual construction x=t+ell>0 and A=A1>0. If V=0, then e=-1 and
the norm equals (d(x^2-A)+1)^2+4dA>0, which contradicts its vanishing.
Therefore V is nonzero, e=QV^2-1>=Q-1=d>0, and y0=x-tau0 is nonzero.
Taking the positive integers |tau0| and |y0| recovers exactly

    tau^2=1+ell(ell+k),
    QV^2-(Q-1)y^2=1,
    (ic^2)^2=Delta(f^2-1).

These equations are unchanged by the absolute values. In particular,
ordinary rational Pell saturation is unnecessary here: y0 is already
the difference of two integers.

Conversely, an ordinary parent witness has positive tau,y and
tau^2=1+ell(ell+k)>ell^2. Thus tau>ell, and

    t=tau-ell+y

is a strictly positive integer. It gives x=tau+y, which annihilates the
norm exactly. This proves positivity of the new coordinate on the
constructive completeness branch. It does not assert a positive affine
bijection on arbitrary parent tuples.

## 3. The absorber is used with the correct hypotheses and order

Nt=1 excludes C<=0 using the positive old transport coordinate z:

    Nt <= 1-F-(z-1)(q-1) <= 0.

The authentic native-mask inequalities then yield the recorded R bounds.
The main norm supplies the integer root g=Dstar/U; its positivity follows
from Dstar>ak(UY-5)>0. Integrality gives U|H(k-R-1), without premature
cancellation of H.

The restored first Pell equation gives k=2*psi_P0(n). Its recurrence is
modulo 4XY^2, a multiple of U. H is odd and H=3 modulo q, with valuation
exactly one at 3 whenever 3 divides q. Therefore gcd(U,H)<=3, and

    mu=U/gcd(U,H) >= 4q^4/3 > R+1.

The congruence 2n=R+1 modulo mu and n>0 imply n>=(R+1)/2 before the
claim p=R is made. The main/first Pell comparison gives p>n, hence the
required c>A0*Delta^2, c>2p and c>2R bounds. This avoids the circular
bootstrap that would arise from using a recovered quotient prematurely.

The ordinary strong-rank theorem is then applicable exactly as stated.
It supplies p|m, c|m, I=Delta*psi_A0(m), and c^2|(f^2-1). The congruence
V=-R modulo c is justified by this final divisibility; it is not obtained
by informally dividing the original strong equation by Delta.

The signed auxiliary argument, with 0<2p<m and 0<p,R<c/2, gives p=R
without requiring V>0. Hence n<R and the already proved congruence forces
2n=R+1. Both omitted quantities h=(k-R-1)/E and
gamma_old=gamma-(k-R-1)/U are integers and positive by the supplied
growth bounds. This restores exactly the positive ordinary compiler.

## 4. Coherent compact tuple and transport convention

All four actual payloads have the compact44 hashes; the local aliases are
beta->beta, K0->K, MC->MC and MF->MF_source. I independently verified

    beta=2^590069-1, K>0,
    0<MC<beta, 0<MF_source-beta<beta,
    MC=2 modulo4, MF_source-beta=4 modulo8,
    popcount(MC)+popcount(MF_source-beta)=590069.

These are the ordinary source's native low-mask and population hypotheses.
The compact matching proof explicitly transfers the complete tuple to
compatible positive and ordinary skeletons. The source50 absorber proof
states its uniformity over complete authentic native tuples. Canonical
normalized witnesses give ordinary ones by i_ordinary=Delta*i_normalized.
The tuple's unbounded compiler/blank calibration remains an identified
inherited theorem, rather than being inferred from hash checks.

The circuit uses the old product transport coordinate, where Nt=1 means

    (K0+w)C=F+(z-1)(q-1).

This differs by exactly one from the shifted transport coordinate in the
quartic component. The author's proof states this explicitly. No silent
substitution of the shifted source row occurs.

The three compact proof/builder Git-blob identifiers were independently
re-read from the pinned GitHub source during review and matched the
retained source pins. The checker validates all 14 retained pin hashes
and lengths.

## 5. Exact degree and circuit claims

The independent checker expands the complete main residual with all
13 witnesses and four fixed ports symbolic: 2994 monomials and exact
witness degree 26. The centered difference x^2-A1 expands to 42 monomials
of exact degree 12. All other highest homogeneous forms are propagated
without an unresolved cancellation.

Writing q0=beta*J, E0=w*s*q0^4, c0=(eta+zeta)*s*q0^3 and
Nt2=w(q0-F-alpha)-z*q0, the checked complete highest form is

    -512*q0^8*E0^8*c0^9*gamma*i^2*T^2*f^6*Nt2.

Its degree is 114. The four factor degrees are 2,26,22,64. On the
all-variables-equal diagonal its leading coefficient is
2^19*beta^67, nonzero for the actual beta. This proves exact degree on
the fixed instance, not only for generic parameter values.

The literal DAG has 46 multiplications, 19 additions and 18 subtractions,
totaling 83, with every gate, witness and port live. Scalar multiplication
and squaring are included. The source59 degree126/91 comparator and the
source57 degree132/83 entry agree with the retained proof and inspected
repository README. The new result dominates both named points on the
relevant degree/operation comparisons; no universal optimum is established.

## 6. Additional critical review of Q42's common-sign recovery

I also inspected the common-sign soundness argument in
`../quartic42/PROOF.md`. No critical local defect was found.

The exclusion of u=0 uses the main norm modulo H and does not assume a
sign for Y. The stronger scale w=4u^2 gives |E|>4R+8. For either sign
of Y, A=|a+2|>|E| and |c|>|k|, so positive Pell classification supplies
p>n. Writing sigma for the common sign of eta,zeta, the first recurrence
and retained index equation give sigma*2n=R+1 modulo |E|. Either sign
forces n large before ordinary strong-rank recovery. The latter and the
signed auxiliary argument give p=R with no sign assumption on c or V.

If sigma were negative, |E| would divide 2n+R+1 even though
0<2n+R+1<3R+1<|E|, a contradiction. The missing individual positivity
guards are therefore recovered before invoking the full old Q45 theorem.
Canonical R and binary exponent t are odd, making
w=2^(R-t) a multiple of four times a square, as required for completeness.
The correction of the old transport prose to the literal z>0 conclusion
is appropriate; it does not alter the polynomial.

This Q42 check addresses the new sign argument. Its full inherited native
compiler and arithmetic dependencies remain outside the finite review.
