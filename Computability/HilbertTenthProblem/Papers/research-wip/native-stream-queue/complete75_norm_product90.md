# A shifted transport unit gives a 90-operation universal polynomial

The fixed complete75 compiler has a single-polynomial representation with
**19 strictly positive existential witnesses**, exact degree **276**, and
evaluation cost **90=49M+41A**. Its comparison certificate uses
**82=46M+36A operations and three equations**. The transport quotient is
shifted by one, allowing its unit equation to share the already computed
expression q-F. A Pell-index argument excludes the only additional sign
branch introduced when this unit joins the product from
[norm product91](complete75_norm_product91.md).

Three separately audited partitions give **96 operations at degree84**,
**94 at degree96**, and **92 at degree138**, with the same19 witnesses.
Those three partitions have a simpler proof that does not require the
new negative-index exclusion. The earlier93/degree136 polynomial remains
a separate useful tradeoff. The best complete comparison-certificate
bound remains75. These statements concern positive integer zero sets,
not equality of the old and new polynomials away from zero.

The [eight-factor successor](complete75_norm_product89.md) merges the two
remaining equations and uses an unsquared product, giving89 operations
at degree166. The lower-degree partitions here remain separate options.
The later [reversed auxiliary product](complete75_reversed_auxiliary89.md)
lowers that89-operation degree to160. The
[retained-auxiliary partitions](complete75_auxiliary_degree_tradeoffs.md)
give93/degree128 and improve this packet's92/degree138 to92/degree136.

## 1. Definitions and the new transport coordinate

Keep the fixed compiler numerals from
[bounded projection99](complete75_bounded_projection_elimination99.md).
In particular B>=16, the fixed input constants d,b are positive, and
0<MC,MF<B-1. The ordinary input x is positive. Supply exactly

    J,F,alpha,zplus,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,delta,rho,sigma

as strictly positive integer witnesses. Only zplus replaces the old
coordinate z. Define the same paid expressions as99:

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    D=X+ac+(rho+sigma)H,
    kappa=2d*x+b+delta*Delta, mu=W+a*kappa+rho*H,
    T=i*c^2, U=jc-R,
    C=q-F-Z-alpha-2d*x, W=C-Z,
    G=(q-1)(q-F)+(q-F-Z)=q^2-Z-qF,
    R=G*(q^2-1)+(MC+q*(MF+B-1))*J.                    (1)

Here A is a proof abbreviation; the source register `A` holds Delta.
Every expression in(1) is substituted into the polynomial circuit.
Computed quantities such as C,W,R,mu,U may be signed on assignments
where the final polynomial is nonzero.

Recall the five integer factors computed in91:

    N0=tau^2-(E^2+X)(kY)^2,
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3=T^2*(U^2-y^2)+y^2,
    Nk=k-R-hE.                                        (2)

Put K0=DC+B*DR, a fixed positive compiler numeral, and introduce

    Nt=(K0+X)C+(q-F)-zplus*(q-1).                     (3)

If z=zplus-1, the polynomial identity

    Nt=1+((K0+X)C-F-z(q-1))                           (4)

holds on every assignment. The new coordinate must satisfy zplus>=2
on the zero set before z can be restored as a positive witness; that
fact is proved below rather than imposed by an unpaid inequality.

## 2. Four unconditional norm exclusions

The signed descent lemmas proved in
[91, Section1](complete75_norm_product91.md) say that neither

    u^2-(A0^2-1)v^2=-1,  A0>=2,
    u^2-V(V+1)v^2=-1,    V>=2                         (5)

has integer solutions. They allow signed u and v. The respective
norm-preserving transforms decrease the least positive |v| by replacing
it with `A0*v-u` and `(2V+1)v-2u`, after taking absolute values.

On every positive supplied assignment in this packet, independently
of any equation, these lemmas exclude-1 in all four norms(2):

* N0 has the second form with V=XY^2>1.
* N1 and N2 have the first form with A0=A=a+2>1.
* `N3=(TU)^2-(T^2-1)y^2` has the first form with A0=T.
  Here c=kY+eta>=3 and T=ic^2>=9.

In particular neither positivity of mu nor positivity of U is needed
for these exclusions. They precede every kernel or compiler argument.

## 3. The three equations and the outer bootstrap

Use exactly the following three residuals:

    Q0=T^2-Delta*(f^2-1),
    Q1=U-(of-c),
    Q2=N0*N1*N2*N3*Nk*Nt-1.                           (6)

The final polynomial is `P=Q0^2+Q1^2+Q2^2`. A positive integer zero
forces every residual to vanish. Since every integer factor of a
product1 is1 or-1, Section2 gives

    N0=N1=N2=N3=1, Nk=Nt in {1,-1}.                   (7)

It remains to exclude the paired negative choice. This requires a
bootstrap that permits C=0. Write Nt=epsilon, epsilon in{1,-1}.
Equation(3) gives

    (K0+X)C=F+(zplus-1)(q-1)+(epsilon-1)>=-1.         (8)

The coefficient K0+X is an integer greater than1. Thus **C>=0**.
Its definition in(1), with positive alpha and x, implies

    F+Z<q, 0<F,Z<q,
    q-F-Z=C+alpha+2d*x>0.                            (9)

These statements do not assume that q is a power. As q>=B>=16,
positive F,Z with F+Z<=q-1 give

    2q-1<=G=q^2-Z-qF<=q^2-q-1.                       (10)

For example the lower bound follows by substituting F<=q-1-Z,
giving G>=q+(q-1)Z>=2q-1. The fixed mask bounds imply

    0<(MC+q*(MF+B-1))*J<(q-1)(1+2q).

Substitute into(1) to obtain the full external kernel interval

    R>(2q-1)(q^2-1)>3q+1,
    R<(q^2-q-1)(q^2-1)+(q-1)(1+2q)
      =q^4-q^3<q^4.                                 (11)

In particular R is positive even in the negative transport branch.
Assuming C>0 at this point would be incorrect: the partial assignment
B=16,J=1,F=2,Z=1,alpha=5,d=4,x=1,zplus=1 has C=0 and Nt=-1.
With MC=2,MF=4 its computed R is57171, within(11). This is an outer
interface fixture, not a solution of all three equations.

## 4. The negative index unit is impossible

Assume for contradiction Nk=-1, so

    k=R-1+hE.                                        (12)

Only the four norm equations in(7), the retained strong square Q0=0,
the retained linear auxiliary equation Q1=0, and bounds(11) are used
in this section. The input power theorem and positivity of W or mu
are not used. The entire half-binomial theorem cannot be invoked
directly with the altered first-index equation(12).

First, X,Y>=q^3, E>=q^6>2R and a=Y(X+1)>q^6>R.
Set V=XY^2 and P0=2V+1. The first-norm classification from
[half-binomial42, Section3](pell_kernel_half_binomial42.md) gives

    tau=chi_P0(n), k=2*psi_P0(n), n>=1.                (13)

Its fundamental unit has coefficient2: coefficient1 is excluded by
the strict square interval between V^2 and(V+1)^2. As P0=1 modulo E,
the psi recurrence gives `psi_P0(n)=n modulo E`. Thus

    2n=R-1 modulo E.

Since 0<R-1<E, positivity of n implies n>=(R-1)/2>=24.
The positive main norm gives c=psi_A(p), D=chi_A(p), p>=1.
Here P0>A, and c>kY>psi_P0(n), so monotonicity in the Pell parameter
and index forces p>=n+1>=25. Therefore ordinary Pell growth gives

    c>(2A-1)^(p-1)>A^5>A*Delta^2, c>2p.              (14)

Also h>=1 and E>2R give k=R-1+hE>R, so c>kY>2R.
Consequently U=jc-R>0 for positive j. These inequalities meet the
generic hypotheses of the retained
[relaxed auxiliary-rank proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md).
Applied to Q0=0, it yields an index m with

    f=chi_A(m), c divides m, m>=c>2p,
    T=Delta*psi_A(m)>1.                               (15)

For clarity, the exact signed-index recovery is also unchanged. From
N3=1 and U>0, Pell classification at parameter T gives a positive
index ell with

    TU=chi_T(ell), y=psi_T(ell).

The index ell is odd, since an even chi_T(ell) is1 or-1 modulo T.
Write ell=2v+1. The integer polynomial Q_v satisfying
`chi_T(2v+1)=T*Q_v(T^2)` has the identities

    Q_v(1-A^2)=(-1)^v*psi_A(ell),
    Q_v(0)=(-1)^v*ell.

These are the recurrence identities in
[the half-parameter proof, Sections3–4](../../1980/HALF_PARAMETER_PELL_92_PROOF.md).
Since T^2=Delta*(f^2-1), its reduction modulo f is1-A^2.
The unchanged Q1=0 gives U=-c modulo f, so squaring the resulting
psi congruence gives

    chi_A(2ell)=chi_A(2p) modulo chi_A(m).

The signed chi step-down lemma applies with 0<2p<m from(15), and
gives ell=+p or-p modulo m, hence modulo c. Independently c divides T,
so U=(-1)^v*ell modulo c. The unchanged definition U=jc-R now gives
R=+p or-p modulo c. Both R and p are less than c/2 by(14), so the
alternative R+p=c is excluded by size, with no parity assumption.
Therefore

    p=R.                                             (16)

Since P0>A and c>k, (13) and(16) also give n<R. Both2n and R-1
are now in(0,E), so the earlier congruence is exact:

    2n=R-1, R=2n+1.                                  (17)

This is incompatible with the unchanged positive ratio interval.
Set Q=chi_A(2)=2A^2-1. Direct expansion gives

    Q-P0=2Y^2*(X^2+X+1)+8Y*(X+1)+6>0.

Pell duplication and monotonicity therefore imply

    psi_A(2n)=2A*psi_Q(n)>=2A*psi_P0(n)=A*k,
    c=psi_A(2n+1)>A*k>k(Y+1).                         (18)

But c=kY+eta and k=eta+zeta with eta,zeta positive give
`kY<c<k(Y+1)`, a contradiction. Thus **Nk cannot be-1** under the
three equations. By(7), both Nk and Nt are1.

This argument depends on keeping both the full strong auxiliary square
and the linear congruence on the same root U=jc-R. It does not justify
merging an arbitrary shifted auxiliary linear residual into the product.

## 5. Restoring the old positive quotient and universal equivalence

Now Nt=1 makes the right side of(8) strictly positive, so C>0. If
zplus=1, that equation would read `(K0+X)C=F`. Its left side is at
least X>=q^3>q, while(9) gives F<q. Hence zplus>=2, and

    z=zplus-1>0.                                     (19)

Equation(4) restores exactly the old transport comparison. The four
norms and Nk are1, and both auxiliary comparisons remain unchanged.
We have therefore restored every equation of91 with the same positive
coordinates except for(19). Its theorem applies through99 and101 to
the original complete75 compiler, proving soundness for this same
ordinary input x, including all formerly eliminated positivity claims.

Conversely any positive solution of91 extends by setting zplus=z+1.
All other coordinates are unchanged, Nt=1 by(4), and every equation(6)
holds. Thus the90 source and91 source have a **bijection of their positive
solution sets**. In particular the canonical compiler completeness and
dummy-alignment margin already proved for99 carry over unchanged.
No new condition on the fixed program numerals is introduced.

## 6. Literal circuit and arithmetic count

In91 the transport block includes

    local_rhs=z*(q-1), local_rhs_sum=F+local_rhs,

with the comparison `(K0+X)C=local_rhs_sum`. Replace z by zplus in
the existing product, and replace the single sum by

    transport_partial=innerC+q_minus_F,
    norm_transport=transport_partial-local_rhs.

Here `innerC=(K0+X)C` and `q_minus_F=q-F` are already paid registers.
Append the product `all_units=norm_product*norm_transport`, and delete
the transport comparison. All other79 old certificate gates are
identical under the quotient renaming. The new certificate therefore
has

    80+1A+1M=82=46M+36A, 19 witnesses,3 equations.

Three residual subtractions, three squares and two sums give

    82+3+3+2=90=49M+41A.                              (20)

All binary arithmetic, including multiplication by fixed numerals, is
charged. The [checker](complete75_norm_product90.py) and
[receipt](complete75_norm_product90.json) contain the entire90-gate
polynomial DAG, with no external comparison or uncharged sign test.

For a direct identity against the original nineteen-equation source,
restore its deleted coordinates as in99 and formally set z=zplus-1.
Writing its literal residuals as r_i, the new polynomial is identically

    r12^2+r14^2
      +((1-r5)(1+r11)(1+r17)(1+r13)(1+r8)(1+r2)-1)^2. (21)

This identity is valid off the zero set, even when z=0 or computed C,R,mu
are signed. It is not an assertion of equality with the old sum of squares.
The zero-set equivalence requires the integer proofs above.

## 7. Exact degree and six-factor partitions

Give the input and all19 supplied witnesses degree one; fixed compiler
numerals have degree zero. The old five factor degrees from91 are
26,22,42,34,9. The sixth factor Nt has degree5 with highest part

    Nt_top=(B-1)^3*w*J^3*C_top,
    C_top=(B-1)J-F-Z-alpha-2d*x.                       (22)

Its other summands have degree at most two, and the degree-four X
times degree-one C supplies(22). The six-factor product has degree138.
The remaining two residual degrees are22 and6. Thus the highest
homogeneous part of the90 polynomial is

    1024*(B-1)^180*h^2*delta^4*i^4*j^4*w^22*s^38*J^180
      *(eta+zeta)^18*(rho+sigma)^2*C_top^2.             (23)

This is nonzero for every admissible fixed B>1: C_top is a nonzero
linear polynomial, in particular its F coefficient is-1. Consequently
the total degree is exactly276.

More generally partition the six factors into g nonempty groups and
require the product in each group to be1, retaining Q0=Q1=0. Every
factor is an integer unit, and the four norm exclusions still apply.
If Nk and Nt occur in distinct groups, each group has at most one
unrestricted factor, so the unit argument alone forces all factors1.
Then(8),(9),(19) restore the old quotient without Section4. If Nk and
Nt share a group, they have the same sign and Sections3–4 exclude the
negative branch. These are both directions of equivalence for every
partition, using the same inverse coordinate maps as Section5.

Computing all six factors without their products costs77=41M+36A.
A g-group partition adds6-g multiplications and has2+g comparisons:

    certificate operations=83-g=(47-g)M+36A,
    polynomial operations=88+2g=49M+(39+2g)A.          (24)

These explicit choices are audited separately:

| Factor groups | Certificate operations | Equations | Polynomial operations | Exact degree | Needs Section4 |
|---|---:|---:|---:|---:|---|
| `{N0},{N1,Nk},{N2},{N3,Nt}` |79|6|96|84|No|
| `{N0,N1},{N2,Nt},{N3,Nk}` |80|5|94|96|No|
| `{N0,N3,Nk},{N1,N2,Nt}` |81|4|92|138|No|
| `{N0,N1,N2,N3,Nk,Nt}` |82|3|90|276|Yes|

Every row has19 positive witnesses and49 polynomial multiplications.
The final degree is twice the largest sum of factor degrees in a group.
The products of nonzero highest forms remain nonzero, and the squares
of their real polynomials cannot cancel their highest homogeneous parts.
For96 the unique largest group is N2 of degree42; for94 it is N0*N1
of degree48. Their leading forms are respectively

    16*(B-1)^60*delta^4*w^10*s^10*J^60,
    64*(B-1)^66*w^8*s^14*J^66*(eta+zeta)^6*(rho+sigma)^2.

For92 both groups have degree69; its highest form is precisely
`(N0_top*N3_top*Nk_top)^2+(N1_top*N2_top*Nt_top)^2`, using the five
forms displayed in91 and(22). It is nonzero by the same sum-of-squares
argument, proving exact degree138.

Enumeration of all203 set partitions gives, for g=6,5,4,3,2,1,
respectively1,15,65,90,31,1 choices. The minimum largest group degrees
are42,42,42,48,69,138. This is optimality only among these partitions
of these six factors and literal circuits. It does not dominate every
earlier tradeoff: in particular the five-factor93 polynomial has degree136,
and the original75 comparison certificate uses fewer arithmetic operations
than any displayed six-factor certificate.

## 8. Verification and limits

The deterministic checker verifies exact gate rewiring, acyclic register
availability, arithmetic histograms and the full original-source identity(21)
on256 arbitrary retained assignments across bases16,32,64. These include
negative computed C,R and zplus=1, where the restored old quotient is zero.
Each of the three smaller-degree variants has an independent full circuit,
count audit and64 original-source grouped-product identities. Three weighted
univariate specializations verify all six factor degrees and(23); each
partition also has an exact degree and leading-coefficient specialization.

The checker replays both symbolic signed descent identities and their
finite square-root audits from91, and the actual compiler-margin checks
from99. Separate partial transport fixtures retain the C=0 negative-unit
boundary. Another225 exact Pell fixtures verify the duplication comparison
in(18), and its parameter difference is checked symbolically. These finite
checks supplement the parametric proof; they do not materialize the enormous
auxiliary towers of complete accepting compiler assignments.

Default execution regenerates and compares the complete receipt. The
source retains the strong auxiliary norm and linear equation unchanged;
there is no weaker auxiliary-norm assumption, real-witness equivalence,
global circuit optimum, or proof-assistant formalization claim.

An independent proof/source audit rebuilt the full polynomial against the
original nineteen residuals on512 assignments across bases16,32,64,256,
including186 zero restored old quotients and four negative computed input
roots. It independently checked the degree276 leading coefficient at
B=64,d=6 and5,820 packing fixtures on the C=0 boundary. The generic
rank and signed-index hypotheses in Section4 were checked directly
against the retained half-binomial proof.

A second independent full proof/source/default review also passed without
findings. Its separate manual formulas checked512 grouped-polynomial
assignments across96,94,92,90, including four negative computed input roots
and64 deliberately zero restored quotients. Twelve weighted/offset
specializations checked all six leading forms and degrees84,96,138,276.
It also checked the C=0,Nt=-1 partial fixture and3,072 exact Pell
duplication/ratio cases independently of the supplied checker.

From the repository root with verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product90.py
