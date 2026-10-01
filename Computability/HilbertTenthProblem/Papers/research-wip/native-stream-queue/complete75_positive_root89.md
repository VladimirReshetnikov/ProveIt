# A positive first-root coordinate gives89 operations at degree148

The fixed complete75 compiler has a single-polynomial representation with
**89=47M+42A operations**, exact total degree **148**, and **19 strictly
positive existential witnesses**. This improves the degree160 and48M+41A
split of [the reversed-auxiliary89 source](complete75_reversed_auxiliary89.md)
without changing the total operation count. Its comparison certificate
has88=47M+41A operations and one equation. The best complete comparison
bound remains75.

Only the first Pell root is recoded. Subtracting a known positive multiple
from that root gives another strictly positive integer on every accepted
tuple. Substitution cancels its highest-degree square term. Both ratio
slacks, the full strong auxiliary condition, the input bridge, the fixed
compiler numerals and the ordinary positive input remain unchanged.

This is a change of witness coordinate. The new and old polynomials are
not claimed to agree at identically named coordinate values; they agree
after the explicit polynomial substitution below.

## 1. The positive coordinate map

Retain all definitions and fixed hypotheses of the degree160 source. In
particular B>=16 and the supplied coordinates other than its first root
are positive, as is the ordinary input x. Recall

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, c=kY+eta.

Write V0=XY^2 and let tau_old denote the old positive first Pell root.
Its unit factor is

    N0=tau_old^2-(E^2+X)(kY)^2
      =tau_old^2-V0(V0+1)k^2.                         (1)

Replace the supplied coordinate tau_old by one positive coordinate g,
named `tau_gap` in the source. Its mathematical reconstruction is

    L=E*(kY)=V0*k,
    tau_old=L+g.                                      (2)

Since V0,k,g are positive, the reconstructed old root is strictly
positive on every positive new assignment, before using any equation.
The remaining eighteen supplied witnesses are unchanged:

    J,F,alpha,zplus,f,h,i,j,o,s,w,eta,zeta,y,Z,delta,rho,sigma.

Thus the total is still nineteen. Both eta and zeta are retained, so
`kY<c<k(Y+1)` remains enforced by its original positive definitions.

Substituting(2) into(1) gives the exact integer-polynomial identity

    N0new=g^2+V0*k*(2g-k).                             (3)

The old root is used nowhere outside N0. Replace that one factor by(3)
in the degree160 eight-factor product, leaving its other seven factors
unchanged. The resulting polynomial is

    P148=N0new*N1*N2*M3*Nk*Nt*N4*Lunit-1.              (4)

Here M3=K*((of-c)^2-y^2)+y^2, K=Delta*(f^2-1), and
Lunit=1+(of-c)-(jc-R), exactly as in the parent source. The name Lunit
is distinct from the computed first-root base L in(2).

## 2. Both directions preserve positive solutions

Given positive new supplied witnesses with P148=0, reconstruct the old
root by(2). It is positive, and all other supplied coordinates already
have the parent's positive domains. Identity(3) and the unchanged other
factors prove that the entire parent polynomial is zero. Its established
soundness theorem now recovers the strong auxiliary square, both exact
indices, positive transport quotient and all earlier complete75 witnesses,
for this same ordinary input x.

Conversely, take any positive zero of the parent degree160 polynomial.
Its theorem proves that N0=1. Equation(1) implies

    tau_old^2-(V0*k)^2=V0*k^2+1>0.

Both tau_old and V0*k are positive, hence tau_old>V0*k. Therefore

    g=tau_old-V0*k                                    (5)

is a strictly positive integer. Keep every other coordinate unchanged.
Equations(2)--(3) show that(4) is zero. The maps(2) and(5) are inverse
on positive solution tuples, so they give a **bijection of the full
positive solution sets**, not just a map of canonical witnesses.

In particular the fixed compiler's canonical completeness and all of
its padding and dummy-alignment margins are inherited. No new condition
on the program constants or input has been imposed.

For an additional direct sign check, N0new is the old norm(1) at the
positive reconstructed root(2). Its negative-unit obstruction therefore
remains valid with V0>1. There is no need to assume positivity of the
computed expression2g-k. It may be negative; only supplied coordinates
have positive-domain restrictions. The parent proof's remaining modular
unit exclusions and conditional index arguments are unchanged.

## 3. Six paid operations replace six

The old first-norm block, apart from the already used E,kY,X, is

    tau_square=tau_old*tau_old,
    E_square=E*E,
    coefficient=E_square+X,
    kY_square=(kY)*(kY),
    term=coefficient*kY_square,
    N0=tau_square-term.

It costs4M+2A. The new block is

    tau_square=g*g,
    first_root_base=E*(kY),
    twice_tau_gap=g+g,
    first_signed_gap=twice_tau_gap-k,
    first_cross=first_root_base*first_signed_gap,
    N0new=tau_square+first_cross.                     (6)

It costs3M+3A. Both blocks have six binary operations. The square of E,
the old coefficient, the square of kY and their old product have no other
users and are removed. Every other certificate gate remains in place,
up to the supplied-coordinate renaming and topological reordering.

The source does not compute tau_old as an extra runtime output. Its
reconstruction in(2) is a proof map to the previous representation;
the final polynomial directly evaluates(3) using(6). Thus there is no
unpaid intermediate required by the circuit.

The exact ledger is

    certificate:88=47M+41A, one equation;
    polynomial:89=47M+42A, nineteen positive witnesses. (7)

The final operation is the unsquared subtraction of1 from the complete
product. Multiplication by fixed numerals remains charged under the
same convention as every parent source. The
[checker](complete75_positive_root89.py) and
[receipt](complete75_positive_root89.json) expose the entire acyclic
polynomial DAG and its output register.

## 4. Exact degree148 and leading form

Give x and all nineteen new witnesses degree one; fixed program numerals
have degree zero. Put Q=(B-1)J, k0=eta+zeta and

    C_top=Q-F-Z-alpha-2d*x.

The root base L=E*(kY) has degree13 with highest part
`w*s^2*k0*Q^9`. Since g^2 has degree2, the new first factor has exact
degree14 and highest part

    N0new_top=w*s^2*k0*Q^9*(2g-k0).                   (8)

This is a nonzero polynomial. The other seven factors keep their exact
degrees and highest forms from the parent construction. In product order,
the eight factor degrees are

    14,22,42,28,9,5,22,6.

Their sum is148. Multiplying their nonzero highest forms gives

    -32*(B-1)^96*h*(rho+sigma)*delta^2*i^2*j*f^2
      *(eta+zeta)^9*w^12*s^20*J^96*C_top
      *(2g-eta-zeta).                                (9)

For every admissible B, C_top is nonzero because its F coefficient is-1,
and the other linear factor has g coefficient2. Hence(9) is nonzero in
the integer polynomial ring. The final subtraction of1 cannot affect it,
proving exact total degree148. This is an actual degree of the new
polynomial, not only a degree bound after imposing its equations.

The degree reduction follows from the cancellation in(3), together with
the new positive witness domain. It is different from replacing a factor
by a congruent polynomial while retaining identical witness coordinates.

## 5. Verification and scope

Default execution recomputes and compares the deterministic receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_root89.py

The checker verifies(3) symbolically and audits every changed gate,
available register and arithmetic count. It compares the complete new
polynomial with the parent degree160 polynomial after(2) on512 supplied
assignments:384 positive and128 signed. The signed assignments verify
polynomial identities only. For every positive assignment the old root
is separately checked to be positive.

It also reconstructs the original nineteen-equation complete75 source,
using the earlier coordinate substitutions and the root(2), and verifies
the entire corrected eight-factor residual identity on all512 assignments.
Three weighted, offset univariate specializations check every factor
degree and the exact coefficient(9). Another384 component Pell tuples
check the positive map and its inverse at varying parameters and indices.
These are component checks, not materialized accepting compiler towers;
the parametric positivity proof in Section2 supplies the general result.

No total operation bound below89 is claimed. In particular the tempting
substitution k=2g+beta would consume a coordinate presently used for the
upper ratio slack. Without a replacement proof of that bound it does not
give an authorized saving; this construction retains both original slacks.
There is no global circuit optimum, real-witness equivalence or proof-
assistant formalization claim.
