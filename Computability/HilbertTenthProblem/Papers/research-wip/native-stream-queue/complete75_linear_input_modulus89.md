# A linear input-index modulus: 89 operations and degree 135

The fixed complete75 compiler has a universal polynomial with **19
strictly positive existential witnesses**, evaluation cost
**89=47 multiplications+42 additions/subtractions**, and exact degree
**135**. The ordinary positive input x and every fixed compiler numeral
are unchanged. This improves the degree-148 bound at the same cost in
[positive-root89](complete75_positive_root89.md); the
[88-operation degree-151 polynomial](complete75_coupled_index_linear88.md)
remains a separate arithmetic tradeoff.

The change replaces the input-index modulus `(a+2)^2-1` by `a+1`.
It adds one paid addition to the actual coupled88 circuit. The equivalence
uses a positive witness coordinate change, rather than equality of the
two polynomials on identical supplied tuples.

## 1. Fixed hypotheses and exact source

Use precisely the complete compiler hypotheses of
[coupled88 Sections 1–2](complete75_coupled_index_linear88.md), including

    B=2^d, d>=4, 0<MC,MF<B-1,
    MC=2 mod4, MF=4 mod8,
    popcount(MC)+popcount(MF)=d.

The original synchronization, marker, transport and ordinary-input layout
conditions on the fixed numerals DC, DR, d and b are also retained. In
particular b is positive and odd, with b<B. These mask assumptions are
used by the inherited coupled-unit proof; no equivalence is claimed
under weaker arbitrary numerical choices of the masks.

The supplied positive witnesses are

    J,F,alpha,zplus,f,h,i,j,o,s,w,g,eta,zeta,y,Z,delta,rho,sigma.

Here g is named `tau_gap` in the source. Write, with the same paid
arithmetic and fixed numeral convention as coupled88,

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, H=4a+3, Delta=a^2+H=(a+1)(a+3),
    D=X+ac+(rho+sigma)H,
    C=q-F-Z-alpha-2d*x, W=C-Z, u=2d*x+b,
    kappa=u+delta*(a+1), mu=W+a*kappa+rho*H,       (1)
    K=Delta*(f^2-1), T=i*c^2, V=of-c,
    G=q^2-Z-qF,
    R=G*(q^2-1)+(MC+q*(MF+B-1))*J.

Only the definition of kappa has changed. A is a mathematical
abbreviation: the source register named `A` contains Delta, just as in
the parent packet. The fixed numerals `B-1`, `2d`, `MF+B-1` and
`K0=DC+B*DR` are supplied program constants. Their runtime products
remain charged. Intermediate expressions such as C, W and mu may be
signed away from zeros.

The output is the product of these eight integer factors, minus one:

    N0=g^2+E*(kY)*(2g-k),
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3=K*(V^2-y^2)+y^2,
    Nk=k-R-hE,
    Nt=(K0+X)C+(q-F)-zplus*(q-1),
    N4=1+T^2-K,
    L=V-jc+k-hE,

    P=N0*N1*N2*N3*Nk*Nt*N4*L-1.                  (2)

There are no additional comparisons or uncounted side conditions.
The full acyclic schedule is in the [checker](complete75_linear_input_modulus89.py)
and [receipt](complete75_linear_input_modulus89.json).

## 2. The coupled proof still restores the main kernel

Take a positive supplied assignment where P=0. Every factor in (2) is
an integer unit. All uses of N2 in
[coupled88 Sections 2–5](complete75_coupled_index_linear88.md) concern its
form `mu^2-Delta*kappa^2`, which cannot equal -1 modulo 4. They do not
use the previous definition `kappa=u+delta*Delta`. Thus those sections
apply without alteration here. More explicitly, their dependency order
is as follows.

First N0, N1, N2, N3 and N4 cannot be negative units. The first case uses
the negative-Pell descent, and the others use the same modulo-4
obstructions. In particular K=T^2. The weak transport unit Nt=+1 or -1
then gives C>=0, F+Z<q, and

    3q+1<R-2<R+2<q^4,
    E>2(R+2), a>R+2.                             (3)

The unchanged ratio coordinates eta and zeta are both positive. The
unchanged strong auxiliary norm and signed-index argument recover the
three possible main indices `R-2,R,R+2`. The ratio bound rejects the
negative linear-unit branch. On the remaining negative index/transport
branch, all ten half-binomial equations hold at p=R-2. The compiler-mask
population argument then excludes that branch: its displaced packing
has population at most 3t+1, whereas the full kernel requires at least
3t+2. None of these steps uses the input-index congruence.

Consequently all eight factors in (2) equal 1, and the main kernel gives

    q=2^t, X=2^R, c=psi_A(R), D=chi_A(R).         (4)

The original first root is restored as `tau=XY^2*k+g>0`. All other
kernel coordinates and both ratio slacks are unchanged. In particular
this step has not replaced or weakened the strong auxiliary equation.

The positive transport unit gives

    (K0+X)C=F+(zplus-1)(q-1)>0.

Thus `0<C<q` and `-q<W<q`. Also `zplus=1` would imply
`(K0+X)C=F<q<X`, impossible for the positive integer C. Hence the old
transport quotient `zplus-1` is positive. These are conclusions on the
zero set, not extra input restrictions.

## 3. Recovering the exact input index

The new kappa is positive. Its possibly signed root is positive on the
zero set, because

    mu=W+a*kappa+rho*H > -q+a > 0.

From N2=1 there is therefore a Pell index v>=1 with

    kappa=psi_A(v), mu=chi_A(v).                  (5)

As in [signed projection101 Section 3](complete75_signed_projection_elimination101.md),
let `E_A(j)=chi_A(j)-a*psi_A(j)`. Its initial values are 1 and 2, and
it satisfies the recurrence `E_A(j+1)=2A*E_A(j)-E_A(j-1)`. Its positive
successive differences show that it is strictly increasing. Equations
(1), (4) and (5) imply

    E_A(v)=W+rho*H
          <X+(rho+sigma)H=E_A(R),

using W<q<X and sigma>0. Thus v<R. Positivity of C and the fixed bound
b<B<=q also give

    0<u=2d*x+b<2q<R<a+1.                         (6)

The smaller modulus suffices because, for every integer j>=0,

    psi_A(j)=j mod (A-1)=j mod (a+1).            (7)

Indeed `psi_A(0)=0`, `psi_A(1)=1`, and its recurrence reduces modulo
A-1 to a sequence with constant first difference one. Definition (1),
(5) and (7) show `v=u mod(a+1)`. Both v and u lie strictly between zero
and a+1 by (6), so **v=u**. No parity case distinction is required for
this recovery.

The original input-index witness can now be reconstructed. The input
index u is odd and at least three. Reduction of the same Pell sequence
modulo Delta gives

    psi_A(j)=j mod Delta when j is odd,
    psi_A(j)=j*A mod Delta when j is even,        (8)

since `A^2=1 mod Delta`. Moreover `psi_A(u)>u` for A>=2 and u>=3;
this follows immediately from its increasing positive differences,
starting with `psi_A(2)=2A>2`. Therefore

    delta_old=(psi_A(u)-u)/Delta                 (9)

is a strictly positive integer. Replacing the supplied delta by
delta_old in coupled88 leaves kappa, mu and every factor unchanged.
It produces a positive zero of that established universal polynomial.
Its complete ordinary-input theorem restores all remaining omitted
coordinates, including W=2^u and `phi=c-kappa>0`, at the same input x.
This establishes soundness without assuming either omitted positivity
statement in the argument for (7).

## 4. Exact positive witness bijection

Conversely, take any positive zero of coupled88 and change only its
input-index witness by

    delta_new=(a+3)*delta_old.                   (10)

The quantity a is independent of delta. Since `Delta=(a+1)(a+3)`,

    u+delta_old*Delta=u+delta_new*(a+1),

so kappa, mu and all eight factors agree exactly. The new witness is
positive, and (2) vanishes. This direction is also a polynomial identity
under substitution (10), with no zero-set assumptions needed for the
identity itself.

For a new positive zero, equations (1) and (9) yield

    delta_new=(a+3)*delta_old.

Thus (9) and (10) are inverse maps on positive solution sets. No
canonical-subfamily restriction is introduced: every parent positive
solution is included. The fixed compiler, ordinary input and all other
eighteen positive coordinates remain unchanged. Degrees in the two
coordinate systems need not agree; (10) is a nonlinear coordinate map.

## 5. Literal cost and exact degree

The checker changes precisely one parent gate and adds one gate:

    a_plus_one=a+1,                 new, one addition;
    index_product=delta*a_plus_one, replacing delta*Delta.

All other 86 parent certificate gates are identical, including the
eight-factor product chain. The comparison certificate therefore costs
**88=47M+41A**, with one equation `eight_units=1`. Its final subtraction
gives the claimed polynomial cost **89=47M+42A**. Squares and products
by fixed numerals are charged in these counts.

Assign degree one to x and each supplied witness, and degree zero to
all fixed numerals. Let

    Q=(B-1)J, k0=eta+zeta, gamma0=rho+sigma,
    Ctop=Q-F-Z-alpha-2d*x.

The factor degrees, in the order (2), are

    14,22,26,28,9,5,22,9.

For the changed input factor, write `r=W+rho*H`. Exact cancellation gives

    N2=r^2+2a*kappa*r-H*kappa^2.

The highest forms of a, kappa and r are respectively
`w*s*Q^6`, `delta*w*s*Q^6` and `4rho*w*s*Q^6`. Thus N2 has highest form

    4delta*(2rho-delta)*w^3*s^3*Q^18,

of degree 26. Multiplying all eight nonzero highest forms gives the
degree-135 highest form of P:

    32*(B-1)^87*h^2*(rho+sigma)*delta*(2rho-delta)
      *i^2*f^2*(eta+zeta)^8*w^11*s^18*J^87
      *Ctop*(2g-eta-zeta).                        (11)

Each displayed factor is a nonzero polynomial for every admissible B.
In particular Ctop has a nonzero F coefficient. Thus the exact degree
is 135, not only an upper bound.

## 6. Reproducible evidence and scope

Default execution recomputes and compares the entire checked-in receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_linear_input_modulus89.py

The checker audits gate dependencies, the single changed multiplication,
the new addition, positive witness list, comparison and operation totals.
It checks 512 independent direct eight-factor/full-polynomial identities
and 512 parent identities under the forward coordinate change. These
include signed supplied assignments, deliberately negative computed mu,
and zero restored old quotients; they verify arithmetic identities,
not accepting compiler solutions. Three weighted and offset univariate
specializations verify every factor degree and the explicit leading
form (11). Separate exact Pell computations check both congruences,
positive forward/inverse witness maps, and every bounded-index pair in
the tested parameter ranges. The parametric proof establishes the
universal equivalence; finite computations supplement that proof.

This packet does not claim a reduction below 88 operations, a global
degree optimum, or equivalence over unrestricted integer witnesses.

Two independent full proof/source/default reviews passed without
findings. They checked the coupled-proof dependency order, positive
input-root restoration, recovery modulo a+1, the odd-index inverse
coordinate map, exact gate ledger and degree-135 highest form. One
review additionally checked 8,888 Pell cases using independent matrix
powers and 1,024 signed full-source identities under the coordinate
change. These audits retain the distinction between off-zero arithmetic
identities and the proved positive zero-set equivalence.
