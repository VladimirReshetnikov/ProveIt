# A 65-operation rational evaluator of the same integer polynomial

The preserved radix55 compact66 polynomial has an evaluator with **65 binary
operations when fixed rational constants are free leaves**. It is exactly
the same integer-coefficient polynomial, on exactly the same fifteen
positive inputs and the same coherent radix55 coefficient tuple. Its exact
degree remains157. This is a different arithmetic-circuit convention from
the preserved66-operation evaluator, whose fixed leaves are integers.
It is **not an integer-leaf65 record**, a smaller-degree equation, a new
coefficient calibration, or a global minimality result.

The full evaluator is [polynomial.json](polynomial.json). The complete
literal66-gate parent is frozen in [source/parent66.json](source/parent66.json)
and checked byte-for-byte against the preserved radix55 candidate. The independent
stdlib-only [auditor](audit.py) reads that JSON as inert data and imports no
repository implementation. Its exact algebra, degree and byte-binding
results are [AUDIT.json](AUDIT.json).

## 1. The universal identity

Use the whole four-integer tuple from
[the preserved radix55 binding](../../candidates/one-page-compact66-radix55/COEFFICIENT_BINDING.json).
In particular MF is MF_source, shifted from MF_native exactly once. Define
two fixed rational numbers

    U = MF/beta,       W = (MC-MF)/beta.

Here beta is a fixed positive integer, not an unknown. These two denominators
are fixed numerals; no variable division occurs. The four runtime leaves
are beta,K0,U,W. Their definitions retain all four original integer ports;
they do not permit independent choices of components from different tuples.

Let qm=beta*J, q=qm+1, and G=qm*(q-F)+alpha. Then, identically over
the rational polynomial ring for every fixed beta != 0,

    qm*((q+1)*(G+U)+W)
      = qm*(q+1)*G + qm*((q+1)*MF+MC-MF)/beta
      = (q^2-1)*G + J*(q*MF+MC).

The last expression is exactly the old rank R. In particular the rational
denominators cancel identically before imposing the equation or positivity.
This is equality of polynomials, not merely a relation at intended roots.

All other gates remain unchanged. Consequently the entire output is the
same element of Z[J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma] as the
preserved radix55 polynomial. Its complete zero set agrees on every integer
assignment, and hence on the required strictly positive domain. The old
ordinary native/Pell/refutation equivalence transfers without changing any
witness or any coefficient. This local identity supplies no new formal
kernel certificate for those inherited semantic arguments.

The identity is universal in beta,K0,MC,MF with beta!=0. In particular it
also applies pointwise to the coherent complemented47 tuple: its rational
evaluator equals its own66-gate specialization on the same inputs. The
stored circuit, coefficient binding and finite byte audit in this folder
remain bound to the preserved radix55 tuple. No equality of the different
radix55 and radix47 specialized polynomials is asserted, and this identity
does not itself supply a new native calibration for either tuple.

## 2. The complete equation

The only unknowns, all strictly positive integers, are

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

All other names are polynomial abbreviations. With the four fixed runtime
leaves beta,K0,U,W as bound above, define

    qm=beta*J, q=qm+1, C=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
    ell=E*k*Y, c=k*Y+eta, a=E+Y,
    H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H,
    G=qm*(q-F)+alpha,
    R=qm*((q+1)*(G+U)+W),
    V=f^2*(c*T-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,
    Nk=k-h*E-R, Nt=(K0+w)*C+(q-F)-z*qm,
    Ns=Delta*f^2-S^2.

The single equation is

    N0*N1*Na*Nk*Nt*Ns-Delta = 0.

Although the shortened specification uses two fixed rational abbreviations,
the displayed output is an integer-coefficient polynomial by section1.
The literal DAG, including every multiplication required for the fixed
exponents, is supplied in polynomial.json. There are no extra quantified
variables hidden in its named intermediates.

## 3. Exact operation counts and the metric boundary

After G and q^2 have already been produced, the old rank tail is

    q2minus1=q^2-1;  rproduct=G*q2minus1;
    qMF=q*MF;        maskfactor=MC+qMF;
    mask=maskfactor*J; R=rproduct+mask.

That is six operations: three products, two sums and one difference.
Replace those six gates by these five:

    qplus1=q+1;
    shifted_gap=G+U;
    rank_product=qplus1*shifted_gap;
    shifted_product=rank_product+W;
    R=qm*shifted_product.

These cost two products and three sums. The exact full census is

| Evaluator | Multiplications | Additions | Subtractions | Total |
| --- | ---: | ---: | ---: | ---: |
| Maintained integer-leaf DAG | 38 | 15 | 13 | 66 |
| This rational-leaf DAG | 37 | 16 | 12 | 65 |

Every gate, all fifteen witness leaves and all four runtime fixed leaves
are live. Fixed constants are compiled before evaluating the polynomial;
preparing U,W and their storage is not charged as a runtime arithmetic gate.
No coefficient-byte reduction is claimed. Exact rational arithmetic can
also have a different bit cost from integer arithmetic; the table counts
binary operations, not machine time or bit complexity.

If integer leaves are required, clear the rank identity locally instead:

    R=J*((q+1)*(beta*G+MF)+(MC-MF)).

This takes six gates after G: q+1, beta*G, addition of MF, multiplication,
addition of the fixed integer MC-MF, and multiplication by J. Thus it ties
the original66-gate count. Merely suppressing the fixed-denominator charge
must not be described as improving the established integer-leaf metric.

There is also a small obstruction to clearing denominators just by
rescaling the registers of this65-gate graph. Suppose every register is
replaced by a scalar multiple of its old value, witness leaves stay fixed,
and each addition/subtraction is implemented by the identical single gate
without additional scale multiplications. The q-F gate forces the scale of
q to be1. The q=qm+1 gate then forces the scale of qm to be1. Next
G=qm*(q-F)+alpha forces the scale of G to be1, and G+U forces the scale of
U to be1. But the accepted bound0<MF_native<beta and the source shift give
1<U<2, so U is not an integer. This excludes that register-rescaling repair
of this particular DAG. It is not a lower bound for other integer circuits.

## 4. Exact degree and finite verification

The auditor computes in the exact Laurent ring

    Z[J,F,...,gamma,beta,beta^(-1),K0,MC,MF].

It checks the entire old and new rank expressions coefficient-by-coefficient:
both reduce to the same ten-term polynomial with no negative exponents.
It separately checks that the retained complete prefix and suffix are
literally unchanged. The universal rank cut then proves equality of the
entire output without expanding its enormous lower-degree part.

For degree, each witness has weight1 and each fixed coefficient port has
weight0. The actual N1 expression has a complete323-term expansion; its
apparent degree22 cancels to18. Propagating exact full homogeneous leaders
through every remaining gate gives factor degrees

    N0:22, N1:18, Na:62, Nk:7, Nt:2, Ns:46.

They sum to157. Put q0=beta*J and k0=eta+zeta. The complete56-term leading
homogeneous form is

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0).

The monomial

    J^92*h*gamma*i^4*eta^13*w^13*s^26*T^2*f^4*z

has coefficient8*beta^92, nonzero for the fixed positive beta. Thus degree157
is exact; it is not inferred only from a syntactic degree upper bound.

The audit rejects four corrupted rank formulas: omitting U's denominator,
using the wrong sign in W, changing W's denominator/numerator expression,
and replacing q+1 by q+2. It authenticates all242484 existing raw coefficient
bytes and their compressed hashes against the same complete binding.
It does not execute the native compiler, a paper-supplied program, Lean,
TeX or a PDF builder.

From the repository root:

    python3 Computability/DiophantineConsistency/research/rational-rank-factorization65/audit.py --check
    python3 -O Computability/DiophantineConsistency/research/rational-rank-factorization65/audit.py --check

The generated circuit and audit are deterministic. To reproduce them before
comparison, replace --check by --write. The maintained equation.tex,
equation.pdf and CURRENT_EQUATION.json are not changed by this alternative.
