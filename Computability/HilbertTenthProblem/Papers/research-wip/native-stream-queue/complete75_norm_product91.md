# Four norms and an affine unit give a 91-operation universal polynomial

The fixed complete75 compiler has a single-polynomial representation with
**19 strictly positive existential witnesses**, exact degree **266**, and
evaluation cost **91=49M+42A**. Its comparison certificate has
**80=45M+35A operations and four equations**. Four Pell norms exclude the
negative integer unit, allowing their four unit equations and the first
index equation to be combined into one product equation.

Partitioning these factors gives further explicitly audited choices:
**97 operations at degree84**, **95 at degree96**, and **93 at degree136**,
all with19 positive witnesses. The best complete comparison-certificate
bound remains75. These are integer zero-set equivalences; they do not
identify the new polynomials with the old sum of squares away from zero.
No global optimality or proof-assistant formalization is claimed.

The [shifted transport successor](complete75_norm_product90.md) gives
90 operations and improves the degree84 and96 options to96 and94
operations. Its [eight-factor successor](complete75_norm_product89.md)
gives89 operations at degree166. The93/degree136 option below remains
a distinct degree/cost tradeoff.

## 1. Two elementary signed negative-unit obstructions

For every integer A>=2, the equation

    x^2-(A^2-1)y^2=-1                                 (1)

has no integer solution. This includes signed x,y. The case y=0 is
immediate. Otherwise choose a solution with the least positive |y| and
replace x,y by their absolute values. Put Delta=A^2-1. Since

    x^2-(A-1)^2*y^2=(2A-2)y^2-1>0,
    A^2*y^2-x^2=y^2+1>0,

we have `(A-1)y<x<Ay`. The integer transform

    x'=Ax-Delta*y, y'=Ay-x

satisfies `0<y'<y` and preserves the norm exactly:

    x'^2-Delta*y'^2=x^2-Delta*y^2=-1.

This contradicts minimality. The new root x' can be signed; no assertion
of its positivity is needed.

Similarly, for every integer V>=2 the equation

    x^2-V(V+1)y^2=-1                                  (2)

has no integer solution. Use absolute values and minimal positive y as
before. The identities

    x^2-V^2*y^2=V*y^2-1>0,
    (2V+1)^2*y^2-4x^2=y^2+4>0

give `Vy<x<(V+1/2)y`. This time use

    x'=(2V+1)x-2V(V+1)y,
    y'=(2V+1)y-2x.

Again `0<y'<y`, and the norm is unchanged because
`(2V+1)^2-4V(V+1)=1`. This is the same integer descent contradiction.
The restriction V>=2 matters: at V=1 the pair x=y=1 solves(2).

Neither lemma uses Pell-index classification, auxiliary rank recovery,
positivity of a supplied root, or any comparison from the universal
certificate. They are facts about all signed integer roots.

## 2. Four norms already computed by the99 source

Keep all fixed numerals, definitions and19 positive coordinates from
[bounded projection99](complete75_bounded_projection_elimination99.md):

    J,F,alpha,z,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,delta,rho,sigma.

The ordinary input x is also positive. Recall

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    D=X+ac+(rho+sigma)H,
    kappa=2d*x+b+delta*Delta, mu=W+a*kappa+rho*H,
    T=i*c^2, U=jc-R.

A is a proof abbreviation, not an extra gate. The source register named
`A` holds Delta. C,W,R retain exactly the polynomial definitions and
shared packing expression of99.

Form four integer values from existing circuit registers:

    N0=tau^2-(E^2+X)(kY)^2,
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3=T^2*(U^2-y^2)+y^2.                             (3)

They are all incapable of equaling-1 on every positive retained assignment,
independently of all source equations:

* `N0=tau^2-V(V+1)k^2`, where V=XY^2>=2, so use(2).
* N1 and N2 have the form(1) with parameter A=a+2>=2.
* `N3=(TU)^2-(T^2-1)y^2`. Since k>=2, Y>=1 and eta>=1,
  c>=3 and T=ic^2>=9>1. Use(1) with parameter T.

In particular the computed mu and U may have either sign here. Formula(3)
for N3 reuses the actual strong square T^2 and the existing y^2 register;
the norm interpretation adds no arithmetic. The full strong auxiliary
equation `T^2=Delta*(f^2-1)` remains a separate unchanged comparison.

Define one further integer, which need not itself exclude-1:

    Nk=k-R-hE.                                        (4)

The old first-index equation is exactly Nk=1. All five former equations
are replaced by

    N0*N1*N2*N3*Nk=1.                                 (5)

Every integer factor of a product1 is1 or-1. Section1 excludes-1 in
N0,N1,N2,N3, so(5) forces all four to be1 and then forces Nk=1.
The converse is immediate. This proves exact equivalence on the retained
positive integer domain before any kernel theorem or conditional
positivity restoration is used.

## 3. A complete four-equation representation

Use precisely these four residuals:

    Q0=(DC+B*DR+X)C-(F+z(q-1)),
    Q1=T^2-Delta*(f^2-1),
    Q2=(jc-R)-(of-c),
    Q3=N0*N1*N2*N3*Nk-1.                              (6)

All abbreviations in(6) are substituted paid polynomial expressions.
The final polynomial is `P=Q0^2+Q1^2+Q2^2+Q3^2`.

If positive retained witnesses make P=0, every residual vanishes.
Section2 restores all five unit equations from Q3=0, so all eight99
equations hold on exactly the same assignment. Its soundness theorem
then restores R>0 and the old raw slack, applies the101 theorem, and
recovers every original complete75 equation with positive witnesses.
This gives correct membership for the same ordinary input x.

Conversely every positive99 witness tuple has all five factors equal1
and hence makes P=0. Thus this transformation preserves the entire
positive solution set of99, including its canonical completeness and
actual packed-index alignment. It imposes no new restriction on the
fixed compiler numerals or canonical witnesses.

No assertion is made that the product alone gives such an equivalence
over real witnesses. Integer factors of a product1 are essential. Signed
intermediate registers remain permitted, and all19 supplied coordinates
retain their original strictly positive domains.

## 4. Exact source edits and91-operation evaluation

Four99 offset gates are replaced by four norm gates at equal cost:

| Old gate | New gate |
|---|---|
| `R9=tau_square-1` | `norm_first=tau_square-L9` |
| `R15=Ac2+1` | `norm_main=L15-Ac2` |
| `norm_rhs=scaled_kappa2+1` | `norm_input=mu2-scaled_kappa2` |
| `P17=1-aux_y2` | `norm_aux=L17+aux_y2` |

The two index additions

    r1=R+1, R11=r1+hE

become two subtractions

    index_difference=k-R, norm_index=index_difference-hE.

The product hE was already paid. All other70 certificate gates are
identical to99. Four binary multiplications combine the five factors.
Replacing their five comparisons by one leaves

    76+4=80 certificate operations =45M+35A,
    19 positive witnesses and four equations.

Four residual subtractions, four squares and three sums give

    80+4+4+3=91=49M+42A.                              (7)

The [checker](complete75_norm_product91.py) and
[receipt](complete75_norm_product91.json) expose the entire91-gate
polynomial DAG and its output register. No comparison remains external
to that final evaluation.

For a direct audit against the original nineteen-equation source, write
r_i for its literal DAG residual after99's coordinate substitutions.
Then

    N0=1-r5, N1=1+r11, N2=1+r17, N3=1+r13, Nk=1+r8.

The new polynomial is identically

    r2^2+r12^2+r14^2
      +((1-r5)(1+r11)(1+r17)(1+r13)(1+r8)-1)^2.        (8)

Formula(8) is checked on arbitrary assignments, including signed computed
C and R. The integer descent supplies the zero-set equivalence; the new
polynomial is not asserted to equal the old sum of squared residuals.

## 5. Exact degree and useful partitions

Give x and the19 witnesses degree one, and all fixed program numerals
degree zero. The five factors' highest homogeneous pieces are

    N0_top=-(B-1)^18*w^2*s^4*J^18*(eta+zeta)^2,
    N1_top=8*(B-1)^15*w^2*s^3*J^15*(eta+zeta)*(rho+sigma),
    N2_top=-4*(B-1)^30*delta^2*w^5*s^5*J^30,
    N3_top=(B-1)^18*i^2*j^2*s^6*J^18*(eta+zeta)^6,
    Nk_top=-(B-1)^6*h*w*s*J^6.

Their exact degrees are26,22,42,34,9. For N1 and N2 use the ordinary
polynomial cancellation

    (az+v)^2-(a^2+H)z^2=2azv+v^2-Hz^2.

For N3 the leading term is `T^2*(jc)^2=i^2*j^2*c^6`; degree-four R
is below degree-six jc. For Nk the degree-nine hE dominates k and R.
Thus Q3 has degree133, while Q0,Q1,Q2 have degree bounds5,22,6.
The highest homogeneous part of the91 polynomial is

    1024*(B-1)^174*h^2*delta^4*i^4*j^4*w^20*s^38*J^174
      *(eta+zeta)^18*(rho+sigma)^2.                   (9)

It is nonzero for every admissible fixed B>1, proving exact degree266.

There is a useful family between the original separate equations and(5).
Partition the five factors into g nonempty groups and require the product
within each group to be1. Each group contains at most one unrestricted
factor Nk; all other factors exclude-1. The same integer-unit argument
therefore restores every factor to1, giving both directions of equivalence
for **every** such partition.

Computing the five factors costs76 operations. A g-group partition uses
5-g products and leaves3+g equations. Therefore

    certificate operations=81-g, equations=3+g,
    polynomial operations=89+2g=49M+(40+2g)A.          (10)

For each group, its product degree is the sum of its factor degrees.
The final degree is twice the largest group degree; the remaining
residual degrees are smaller. Products of the displayed nonzero leading
forms are nonzero, and squares of such real polynomials cannot cancel
their highest-degree parts.

These explicit partitions give the following audited choices:

| Factor groups | Certificate operations | Equations | Polynomial operations | Exact degree |
|---|---:|---:|---:|---:|
| `{N0},{N1},{N2},{N3},{Nk}` |76|8|99|84|
| `{N0},{N1,Nk},{N2},{N3}` |77|7|97|84|
| `{N0,N1},{N2},{N3,Nk}` |78|6|95|96|
| `{N0,N2},{N1,N3,Nk}` |79|5|93|136|
| `{N0,N1,N2,N3,Nk}` |80|4|91|266|

Every row uses19 positive witnesses and49 multiplications in its final
polynomial. The first row recovers99's polynomial up to residual signs
and ordering. The97 row retains its degree84 with two fewer operations.
Their highest homogeneous terms, for97,95,93 respectively, are

    16*(B-1)^60*delta^4*w^10*s^10*J^60,
    64*(B-1)^66*w^8*s^14*J^66*(eta+zeta)^6*(rho+sigma)^2,
    16*(B-1)^96*delta^4*w^14*s^18*J^96*(eta+zeta)^4.

The checker enumerates all52 set partitions. Among partitions with
g=5,4,3,2,1 groups there are respectively1,10,25,15,1 choices; the
smallest possible largest group degrees are42,42,48,68,133. At g=4,
merging `{N0,Nk}` is a second optimum; the other displayed optima are
unique. This is an exact optimization only within this specified
partition construction, not among all equivalent polynomials or circuits.
The75-operation comparison certificate and its101 polynomial with20
witnesses remain a separate arithmetic tradeoff.

## 6. Evidence and limits

The checker audits the exact local rewiring, available registers, norm
identities and counts. It independently replays the original source on256
retained assignments across several bases, including negative computed C
and R, and verifies(8). It checks the signed auxiliary norm interpretation
and the original strong auxiliary comparison remains present. These are
identity tests, not full accepting compiler tuples.

Both descent transforms and their strict interval identities are verified
symbolically. Separate exact square-root searches cover30,000 cases for
each negative-unit lemma. The integer-unit audit considers all16 possible
sign patterns of a five-factor product1 and verifies that four negative-
unit exclusions leave only the all-positive case. These finite checks
corroborate the parametric proofs; they do not replace them.

Three univariate specializations, including unequal positive coordinate
weights and bases16,32,64, verify all five factor degrees and the leading
coefficient(9). Every displayed intermediate partition has its own full
polynomial DAG, availability/count audit,64 arbitrary-assignment formula
checks, and exact degree/leading-coefficient specialization in the receipt.
The actual canonical compiler-margin audit is inherited and replayed from99.
Default execution regenerates the deterministic result and compares the
entire receipt.

Two independent full proof/source/default reviews passed without findings.
One rebuilt the91 schedule from99 and checked512 original-source residual
identities plus an unequal degree266 specialization. The other checked512
manual grouped-factor evaluations across97,95,93,91, including four
deliberately negative computed input roots, independently enumerated all52
partitions, and verified the leading forms. These additional checks support
the signed-domain and partition arguments without replacing their proofs.

From the repository root with verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product91.py
