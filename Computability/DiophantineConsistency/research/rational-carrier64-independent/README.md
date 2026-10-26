# The identical Carrier65 polynomial in64 rational-leaf operations

The complete accepted reversed2521 Carrier65 polynomial has an evaluator
with64 live binary operations and the same fourteen strictly positive
integer inputs. The operation metric allows one fixed noninteger rational
leaf. The maintained65-operation integer-leaf record is unchanged.

This composes the exact rank identity already proved in
`../single-rational-rank65/README.md` with the accepted Carrier65 graph.
It changes neither the coefficient tuple nor the specialized polynomial,
its degree150, any witness or the positive zero set. The complete literal
graph is `polynomial.json`; the entire parent graph is retained in
`source/parent65.json`. No variable division is introduced.

## Complete fixed-port binding and equation

The source ports are the same complete integers beta,K0,MC,MF from
`../../candidates/one-page-reversed-carrier65-2521/polynomial.json`.
MF denotes MF_source, including its source shift exactly once. All four
whole ports, their compressed files, individual byte/bit lengths, hashes,
native certificate and ordinary proof are authenticated by the audit.
The reverse-discovery decimal page has exactly the same graph and ports;
the finite seed representation is immaterial to this pointwise identity.

Define two fixed leaves

    Urank=MF/beta,       Wrank=MC-MF.

The runtime leaves are beta,K0,Urank,Wrank. Urank has the explicit fixed
numerator MF and fixed positive denominator beta. Wrank is integral and
negative. The coherent tuple satisfies beta<MF<2beta, so1<Urank<2 and
Urank is not an integer. These leaves are not new quantified inputs.

The fourteen positive integer inputs are

    J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma.

All other names below are abbreviations:

    qm=beta*J, q=qm+1, C=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
    ell=E*k*Y, c=k*Y+eta, a=E+Y,
    H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H,
    G=qm*(q-F)+alpha,
    R=(q^2-1)*(G+Urank)+Wrank*J,
    tau=E*n+k-R,
    V=f^2*(c*T-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,
    Nt=(K0+w)*C+(q-F)-z*qm,
    Ns=Delta*f^2-S^2.

The single equation is

    N0*N1*Na*Nt*Ns-Delta=0.

The complete64-row JSON graph specifies every reused intermediate and
every multiplication, addition and subtraction. Exponent notation in
this displayed summary abbreviates those explicit repeated products.

## Universal identity and integrality

For every fixed beta!=0 and arbitrary inputs, q=beta*J+1 gives

    q^2-1=beta*J*(q+1).

Therefore

    (q^2-1)*(G+MF/beta)+(MC-MF)*J
      =(q^2-1)*G+MF*J*(q+1)+(MC-MF)*J
      =(q^2-1)*G+(MC+q*MF)*J.

The final expression is the exact rank R in the accepted Carrier65 graph.
The entire retained prefix and every row after R are unchanged. In
particular tau=E*n+k-R is unchanged, as are every norm and the complete
five-factor finalizer. Substitution at R proves equality of the entire
polynomial, for every input, rather than only equivalence at zeros.

Only the computed register G+Urank is nonintegral on integer inputs.
Multiplication by q^2-1 immediately gives

    (q^2-1)*G+MF*J*(q+1),

an integer-coefficient polynomial even when beta,MC,MF are treated as
coefficient indeterminates. The other branch Wrank*J is integral too.
Every remaining computed register is obtained from integral registers
by the unchanged integer arithmetic. This proves the output belongs to
the original integer polynomial ring, with no variable denominator or
extra integrality condition. The identity map on all fourteen inputs is
the complete zero correspondence in both directions.

The accepted reversed2521 native theorem and uniform Carrier65 theorem
therefore transfer without a new witness transformation. Their existing
syntactic-refutation and ordinary arithmetic calibration remains the
same; this local identity is not a new formal-kernel/internal-ZFC replay.

## Exact operation count and degree

After q squared and G are available, the old six-row rank tail is

    q2minus1=q^2-1;
    rproduct=q2minus1*G;
    qMF=q*MF;
    maskfactor=MC+qMF;
    mask=maskfactor*J;
    R=rproduct+mask.

The replacement is exactly five rows:

    q2minus1=q^2-1;
    shifted_gap=G+Urank;
    rank_product=q2minus1*shifted_gap;
    rank_linear=J*Wrank;
    R=rank_product+rank_linear.

It removes one multiplication. The full graph has36 products,16 sums
and12 differences, totaling64. Every row, all fourteen witnesses and
all four runtime leaves are live. The accepted integer-leaf graph has
37 products,16 sums and12 differences, totaling65. Computing Urank or
Wrank offline is not charged in this fixed-rational-leaf convention.

The exact factor degrees remain22,18,62,2,46. Put q0=beta*J and
k0=eta+zeta. The complete leading homogeneous polynomial is

    8*q0^87*gamma*i^4*k0^13*w^12*s^25*T^2*f^4
      *[w*(q0-F-alpha)-z*q0].

Its term on

    J^88*gamma*i^4*eta^13*w^12*s^25*T^2*f^4*z

has coefficient−8*beta^88, nonzero for the actual positive beta. Thus
the exact total degree is150. The self-contained sparse Laurent audit
checks the complete rank equality, both integral intermediate cuts,
the full retained prefix/suffix, the323-term main-norm cancellation,
and the entire56-term output leader.

The original four integer ports still total59297 raw bytes. That is
the inherited integer-tuple metric, not storage measured for a rational
encoding of Urank and Wrank. No coefficient-height/storage gain or
integer-leaf64 record is claimed. Clearing the fixed denominator by
rewriting R=J*((q+1)*(beta*G+MF)+(MC-MF)) needs six rank-tail operations
and restores the65-operation integer-leaf count.

## Reproduction and controls

The stdlib-only `audit.py` reads reviewed inert JSON and raw compressed
integer files. It imports no repository implementation or incoming code.
Both modes enforce every guard through explicit exceptions:

    python -B Computability/DiophantineConsistency/research/rational-carrier64-independent/audit.py --write
    python -B Computability/DiophantineConsistency/research/rational-carrier64-independent/audit.py --check
    python -B -O Computability/DiophantineConsistency/research/rational-carrier64-independent/audit.py --check

The receipt authenticates the complete64-row graph and frozen65-row
parent, proof inputs and whole tuple. Negative controls alter the rank
denominator, offset sign, offset denominator, q-squared subtraction and
the downstream carrier sign; each is rejected by exact algebra or the
complete retained-suffix check. The unlicensed shortcut Wrank=-beta is
also rejected: it would require MC=MF_native, incompatible with the
actual unequal populations whose sum is the odd integer118487.

This is a separately measured exact evaluator tradeoff. It leaves the
maintained page and integer-leaf65 result untouched and makes no global
minimality or consistency-decision claim.
