# A 65-operation evaluator with one rational constant and one rational gate

The complete complemented47 P66 polynomial admits a65-operation evaluator
with **one fixed noninteger rational leaf**. Exactly one computed register
is nonintegral on integer inputs; its next multiplication cancels the fixed
denominator. The entire output remains the identical integer-coefficient
polynomial of degree157 on the same fifteen positive inputs.

This simplifies the earlier
[two-rational-leaf65 evaluator](../rational-rank-factorization65/README.md)
without reducing its operation count or degree. It is not an integer-leaf65
record or a64-operation evaluator. The current66-operation integer-leaf
page is unchanged. No coefficient-storage reduction is claimed.

## 1. Complete equation and whole coefficient binding

Use all four integers from the coherent complemented47 parent
[polynomial.json](../../candidates/one-page-complemented47-independent/polynomial.json):
beta,K0,MC,MF. MF means MF_source, with its source shift occurring once.
The actual parent, including its whole coefficient binding and controller
certificate pointer, is frozen in [source/parent66.json](source/parent66.json).
The local circuit's `coefficient_binding_base` identifies the parent
directory against which that complete binding's relative paths resolve.

Define only these two derived fixed constants:

    U=MF/beta,             W=MC-MF.

The runtime leaves are beta,K0,U,W. Only U is rational rather than integral.
Its denominator beta is a fixed positive integer, never an unknown.
The actual tuple satisfies beta<MF<2beta, so1<U<2 and U is nonintegral.
The full fifteen-variable domain is

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma > 0,

with every variable an integer. All the following names are abbreviations:

    qm=beta*J, q=qm+1, C=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
    ell=E*k*Y, c=k*Y+eta, a=E+Y,
    H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H,
    G=qm*(q-F)+alpha,
    R=(q^2-1)*(G+U)+W*J,
    V=f^2*(c*T-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,
    Nk=k-h*E-R, Nt=(K0+w)*C+(q-F)-z*qm,
    Ns=Delta*f^2-S^2.

The single equation is

    N0*N1*Na*Nk*Nt*Ns-Delta=0.

The complete literal evaluator is [polynomial.json](polynomial.json).
There are no extra quantified variables, variable divisions, variable
exponents or unprinted rank conditions.

## 2. Exact polynomial identity and complete zero correspondence

For every fixed beta!=0, independently of positivity or any equation,

    (q^2-1)*(G+MF/beta)+(MC-MF)*J
      = (q^2-1)*G + MF*J*(q+1)+(MC-MF)*J
      = (q^2-1)*G + (MC+q*MF)*J.

Here the first equality uses

    q^2-1=(q-1)*(q+1)=beta*J*(q+1).

The final expression is exactly the parent's rank. Therefore the complete
integer polynomial, not just its zeros, is unchanged. Every integer or
positive input tuple maps identically in both directions. The accepted
ordinary complemented47 native/Pell/refutation proof transfers directly;
no old55 coefficient component, new positivity assertion or replacement
witness is involved. This local algebra supplies no new end-to-end formal
kernel proof of that inherited calibration.

The only nonintegral computed register is G+U. Its product with q^2-1 is

    (q^2-1)*G + MF*J*(q+1),

which has integer coefficients even when beta,MC,MF are treated as formal
coefficient indeterminates. W*J is also integral. Every other computed
register is either retained before this cut or obtained from these integral
registers by the unchanged integer arithmetic suffix. This proves the
integrality claim for all integer inputs, not merely for roots.

## 3. Exact operation ledger and scope of the improvement

After q^2 and G are available, the entire rank tail is

    q2minus1=q^2-1;
    shifted_gap=G+U;
    rank_product=q2minus1*shifted_gap;
    rank_linear=W*J;
    R=rank_product+rank_linear.

That is five binary operations: two products, two sums and one difference.
The old tail needed six operations: three products, two sums and one
difference. Thus the full graph uses37 products,15 sums and13 differences,
all65 live. All fifteen witness inputs and all four fixed runtime leaves
are live, and all four original integer coefficient ports remain bound.

Compared with the earlier65 graph, this graph retains q^2-1 and replaces
its rational W=(MC-MF)/beta by the integer MC-MF. It reduces two rational
leaves to one and three potentially nonintegral computed registers to one.
The previous graph had37 products,16 sums and12 differences; the total
count remains65. The two artifacts bind different complete tuples:55 for
the earlier packet,47 here. Their universal identities apply to each tuple
separately; no equality of the different specialized55 and47 polynomials
is asserted.

The metric counts fixed rational constants as free leaves, just as the
integer-leaf metric counts fixed integer constants as free leaves. It does
not charge their offline construction or storage. The207214 raw bytes
authenticated below belong to the existing original integer tuple, and
are not a measurement of a separately materialized U,W encoding.

There is an integer-only version

    R=(beta*G+MF)*J*(q+1)+(MC-MF)*J,

or, after factoring J,

    R=J*((q+1)*(beta*G+MF)+(MC-MF)).

The second tail has six operations after G, yielding66 total. This local
denominator clearing therefore does not improve the established integer
gate count. No lower bound for every possible four-operation rank tail or
every possible integer evaluator is claimed.

## 4. Exact degree, checks and proof boundary

The stdlib-only [audit](audit.py) reads inert JSON and imports no repository
implementation. It was adapted from the previous independent Laurent
auditor, but is self-contained. It checks both complete rank expansions in
Z[J,F,...,gamma,beta,beta^(-1),K0,MC,MF], obtaining the identical ten-term
integer polynomial. It also checks the separate integral polynomial cuts
rank_product and rank_linear, and the literal identity of the entire
retained prefix and suffix.

For degree, each witness has degree1 and each fixed port degree0. The
complete323-term N1 expansion checks its cancellation from apparent22 to18.
Exact homogeneous-leader propagation through every literal gate gives

    deg(N0,N1,Na,Nk,Nt,Ns)=(22,18,62,7,2,46).

Put q0=beta*J and k0=eta+zeta. The full56-term output leader is

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
      *(w*(q0-F-alpha)-z*q0).

The coefficient of

    J^92*h*gamma*i^4*eta^13*w^13*s^26*T^2*f^4*z

is8*beta^92, nonzero on the complete complemented47 tuple. Degree157 is
therefore exact. The audit authenticates all207214 existing raw coefficient
bytes, their compressed hashes, their individual big-endian bit lengths,
and the whole accepted controller certificate hash. It rejects four
corruptions of the rank tail: dropping U's denominator, changing W's
subtraction to addition, adding an unwanted denominator to W, and replacing
q^2-1 by q^2-2.

Run from the repository root:

    python3 Computability/DiophantineConsistency/research/single-rational-rank65/audit.py --check
    python3 -O Computability/DiophantineConsistency/research/single-rational-rank65/audit.py --check

Use --write to reproduce the deterministic circuit and [audit ledger](AUDIT.json)
before checking. This work does not execute a native compiler, a supplied
manuscript program, Lean, TeX or a PDF builder. The new result is the exact
single-rational-register normal form and its full current-tuple binding;
the operation count, degree and semantic calibration otherwise remain at
the stated boundaries.
