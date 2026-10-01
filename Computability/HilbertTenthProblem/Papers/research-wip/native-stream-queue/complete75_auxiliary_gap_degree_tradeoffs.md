# Positive auxiliary-gap coordinates reduce four degree bounds

The fixed complete75 universal compiler admits the following polynomials,
each with **19 strictly positive existential witnesses** and its unchanged
ordinary positive input x:

| Operations | Multiplications | Additions/subtractions | Exact degree |
|---:|---:|---:|---:|
| **90** |47|43|**131**|
| **91** |47|44|**128**|
| **98** |48|50|**54**|
| **99** |48|51|**52**|

The first two outputs are unsquared products of integer units minus one.
The last two are sums of squared residuals. The change replaces the old
positive auxiliary Pell ordinate y by its positive gap e=y−V, where
V=of−c is the auxiliary root already present in the circuit. One paid
addition reconstructs y=V+e. Its cancellation lowers the auxiliary norm
factor's degree from 28 to 24.

These are degree improvements with a nonlinear witness coordinate change.
They do not improve the separate 88-operation polynomial or 75-operation
comparison bound. The existing 89/135 and 92/114 through 97/56 tradeoffs
remain available. The positive solution sets below are in bijection with
the established compiler solution set; no restriction to canonical
compiler witnesses is introduced.

## 1. Fixed hypotheses, factors and exact coordinate change

Retain every hypothesis of the
[linear-input89 construction](complete75_linear_input_modulus89.md) and
its fixed compiler, including

    B=2^d, d>=4, 0<MC,MF<B−1,
    MC=2 modulo 4, MF=4 modulo 8,
    popcount(MC)+popcount(MF)=d,

and all synchronization, marker, transport and ordinary-input conditions.
In particular the fixed input suffix b is positive and odd, with b<B.
The new supplied positive witnesses are

    J,F,alpha,zplus,f,h,i,j,o,s,w,g,eta,zeta,e,Z,delta,rho,sigma.

The source calls J,g,e respectively `Jrep,tau_gap,aux_gap`.
All definitions from linear-input89 are retained, except that y is now
computed:

    q=(B−1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, Delta=A^2−1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    C=q−F−Z−alpha−2d*x, W=C−Z, u=2d*x+b,
    kappa=u+delta*(a+1), mu=W+a*kappa+rho*H,
    G=q^2−Z−qF,
    R=G*(q^2−1)+(MC+q*(MF+B−1))*J,
    T=ic^2, K=Delta*(f^2−1), V=of−c, y=V+e.       (1)

Mathematical A is an abbreviation; the source register named `A`
contains Delta, as in the parent. The fixed numerals B−1, 2d,
MF+B−1 and K0=DC+B*DR are free program constants, while their runtime
products are charged. Computed quantities, including V and y, may be
signed away from the zero set.

Use the eight factors

    N0=g^2+E*(kY)*(2g−k),
    N1=D^2−Delta*c^2,
    N2=mu^2−Delta*kappa^2,
    N3=K*(V^2−y^2)+y^2,
    Nk=k−R−hE,
    Nt=(K0+X)C+(q−F)−zplus*(q−1),
    N4=1+T^2−K,
    L=V−jc+k−hE.                                 (2)

Also put U=jc−R and L0=1+V−U, so L=L0+Nk−1.
Only the circuits that use U or L0 pay for them.

The product outputs are

    P90=N0*N1*N2*N3*Nk*Nt*N4*L−1,
    P91=N0*N1*N2*N3*Nk*Nt*N4*L0−1.               (3)

No additional side comparisons accompany either product.

## 2. Positivity is recovered before auxiliary Pell classification

The following dependency check is necessary: e>0 alone does not imply
y=V+e>0 on an arbitrary supplied assignment. Therefore one cannot apply
the parent positive-y theorem immediately after making the substitution.

At a positive zero of either product in (3), every factor is an integer
unit. The first norm N0 cannot be −1 by the retained negative-Pell
descent. Delta is 0 or 3 modulo 4, so N1 and N2 cannot be −1.
Furthermore K=(A^2−1)(f^2−1) is 0 or 1 modulo 4. Consequently N3 is
congruent to y^2 or V^2 modulo 4 **even when y and V are signed**, and
N4 also cannot be −1. Thus

    N0=N1=N2=N3=N4=1, K=T^2.                      (4)

None of these sign exclusions assumes y>0.

The weak transport unit Nt=±1 then gives C>=0 and F+Z<q. Exactly as in
[coupled88 Sections 2–3](complete75_coupled_index_linear88.md), this gives

    3q+1<R−2<R+2<q^4, E>2(R+2), a>R+2.

The index unit Nk=±1, the positive first root
`tau=XY^2*k+g`, the positive main root D, and the two retained positive
ratio slacks recover first and main Pell indices n and p. Their bounds
include

    p>=25, c=psi_A(p)>A*Delta^2, c>2p.

The unchanged strong equation T^2=Delta*(f^2−1) now invokes the same
generic strong-rank theorem as the parent, giving

    f=chi_A(m), c divides m, m>=c>2p,
    T=Delta*psi_A(m).                              (5)

Every step through (5) uses first/main norms, the strong equation,
weak transport and the index unit. It uses neither the auxiliary Pell
classification nor positivity of y. In particular,

    f>chi_A(2p)=1+2Delta*c^2>2c,
    V=of−c>=f−c>c>1.                              (6)

Now e>0 implies y=V+e>0. All nineteen coordinates of the corresponding
parent product are strictly positive: restore its y coordinate by (1)
and leave all other coordinates unchanged. The two products are
identical under this substitution. The established positive theorems
for linear-input89 and the uncoupled 90-operation product in
[linear-input degree tradeoffs, Section 2](complete75_linear_input_degree_tradeoffs.md)
therefore apply. They restore every unit to +1, recover the exact
ordinary-input relation and supply the full old compiler witness.
The strong auxiliary norm and both ratio slacks have remained intact.

For the inverse direction, start at any positive zero of either parent
product. It already satisfies (4)–(6), and T>1. Rewriting its auxiliary
norm N3=1 gives

    (K−1)*(y^2−V^2)=V^2−1>0.                     (7)

Since K=T^2>1 and y,V>0, equation (7) implies y>V. Hence

    e=y−V>0                                       (8)

is a strictly positive integer. Substitution (8) preserves all factor
values exactly and produces a positive zero of (3). The maps
`y=V+e` and `e=y−V` are inverse because V is independent of y and e.
Thus these are bijections of complete positive solution sets, with
unchanged ordinary input, fixed constants and eighteen other positive
coordinates.

## 3. The two grouped outputs

For the 98-operation polynomial, keep both comparisons

    T^2=K, U=V

and compare each of these four products with one:

    (N0*Nk), (N1*Nt), (N2), (N3).                 (9)

The output is the sum of the squares of the resulting six residuals.
Its zeros make N4=L0=1 and the product in P91 equal to one. Section 2
therefore applies, including its proof that computed y is positive.
Conversely a positive zero of P91 has every unit equal to +1, so all
six residuals vanish.

For the 99-operation polynomial, keep the strong comparison T^2=K and
compare each of these five products with one:

    (N0*Nk), (N1), (N2), (N3), (Nt*L).            (10)

Again there are six residuals. Their vanishing gives N4=1 and P90=0,
so Section 2 supplies soundness. Its converse gives each factor +1,
proving completeness. A group containing two factors of unknown sign
has not assumed their separate positivity: that is supplied by the
complete coupled sign proof after the positive y coordinate is restored.

These grouped polynomials consequently have positive solution sets in
the same bijection as (3). Their output is a literal sum of squares,
with no unpaid conjunction or separate positivity test.

## 4. Literal operation counts

The [checker](complete75_auxiliary_gap_degree_tradeoffs.py) constructs
each exact parent DAG with the chosen comparisons, then adds just

    y_aux = aux_u_rhs + aux_gap.

Every old node is unchanged. This is one extra addition; y is no longer
a supplied witness and e takes its place. The multiplication counts
are unchanged.

| Polynomial | Certificate operations | Certificate M/A | Equations | Polynomial M/A |
|---:|---:|---:|---:|---:|
|90|89|47/42|1|47/43|
|91|90|47/43|1|47/44|
|98|81|42/39|6|48/50|
|99|82|42/40|6|48/51|

For (9), the shared definitions cost 79=40M+39A. There are two group
products, giving the stated 81-operation certificate. For (10), the
shared definitions cost 80=40M+40A and there are again two group
products. Forming six residuals, squaring them and summing the six
squares adds 6M+11A to either certificate. The product outputs instead
add their one final subtraction. The receipt lists all instructions;
squares, fixed-coefficient multiplications and residual formation are
included in the counts.

An alternative exact expression is

    N3=V^2−(K−1)*e*(2V+e).

Sharing K−1 with N4=T^2−(K−1) does not improve these product counts:
it still adds one operation relative to the old two-square expression.
The actual audited schedules use the single y reconstruction above.

## 5. Exact degrees and the bounded partition search

Assign degree one to x and all supplied witnesses. Put
`Q=(B−1)J`, `k0=eta+zeta`, `gamma0=rho+sigma`,
`Ctop=Q−F−Z−alpha−2d*x` and `g0=2g−k0`.
The highest forms of K and V are

    Ktop=f^2*w^2*s^2*Q^12, Vtop=−k0*s*Q^3.

The cancellation in the alternative expression above gives

    H3=2e*f^2*k0*w^2*s^3*Q^15, degree 24.         (11)

Every other factor's highest form is unchanged from the parent:

| Factor | Degree | Highest form |
|---|---:|---|
|N0|14|`H0=w*s^2*k0*Q^9*g0`|
|N1|22|`H1=8gamma0*k0*w^2*s^3*Q^15`|
|N2|26|`H2=4delta*(2rho−delta)*w^3*s^3*Q^18`|
|Nk|9|`Hk=−h*w*s*Q^6`|
|Nt|5|`Ht=w*Q^3*Ctop`|
|N4|22|`H4=i^2*k0^4*s^4*Q^12`|
|L|9|`HL=−h*w*s*Q^6`|
|L0|6|`HL0=−j*k0*s*Q^3`|

The two unsquared products have degrees 131 and 128, with respective
highest forms

    64*Q^84*h^2*gamma0*delta*(2rho−delta)*i^2*f^2
      *e*k0^7*w^11*s^17*Ctop*g0,

    64*Q^81*h*gamma0*delta*(2rho−delta)*i^2*j*f^2
      *e*k0^8*w^10*s^17*Ctop*g0.                  (12)

The group degrees in (9) are 23,27,26,24. Its unique highest residual
square is `(H1*Ht)^2`, of degree 54. The group degrees in (10) are
23,22,26,24,14, giving the unique highest square `H2^2`, of degree 52.
The strong and linear residuals have degrees 22 and 6 and cannot
contribute at those highest degrees. Each displayed leading form is a
nonzero polynomial for every permitted fixed B, proving exact degrees.

To delimit the search, the checker enumerates all partitions in the
same five literal families used by the parent. The one added
reconstruction addition is included in every cost below. Entries are
the minimum possible largest residual degrees for g=1,2,... groups.

| Fixed-factor family | Polynomial cost | Minimum largest degrees |
|---|---|---|
|seven coupled factors, strong separate|`89+2g`|109,55,38,31,26,26,26|
|eight coupled units|`89+2g`|131,66,44,36,31,26,26,26|
|seven uncoupled factors, strong separate|`90+2g`|106,53,36,28,26,26,26|
|five factors, three comparisons separate|`91+2g`|95,48,36,26,26|
|six factors, two comparisons separate|`90+2g`|100,50,36,27,26,26|

The two unsquared products are considered separately. Relative to the
already established frontier, the four rows at the start are the useful
new points from this bounded search. The five-factor family ties 99/52;
the actual 99 circuit here uses the seven coupled factors. No global
arithmetic or degree lower bound is claimed. In particular, the six-factor
98-operation choice has degree 54, not 52: its four-group minimum is 27.

## 6. Verification and scope

Run the checker normally to compare its fresh deterministic results
against the [receipt](complete75_auxiliary_gap_degree_tradeoffs.json):

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_auxiliary_gap_degree_tradeoffs.py

For each of four variants, it verifies 512 direct whole-polynomial
identities and 512 exact coordinate-substitution identities with the
parent circuit. The cases include signed supplied assignments, negative
computed y and mu, and a zero restored transport quotient. The audit
also checks every old register value after substitution, acyclic source
dependencies, operation histograms and the nineteen positive coordinates.
Three weighted, offset univariate polynomial specializations per variant
verify every factor's degree and highest form and each final degree and
leading coefficient. The checker proves the gap expansion symbolically,
checks 276 local positive auxiliary Pell maps and all 256 relevant
modulo-four combinations, and exhaustively enumerates the five partition
families above.

Those arithmetic tests do not claim to construct complete accepting
compiler tuples. The parametric proof of positivity, soundness and
completeness is Sections 2–3, using the unchanged complete compiler
and its ordinary-input theorem.

Two independent full proof/source/default reviews passed without findings.
They checked the signed-y norm obstruction, the strong-rank dependency
order before auxiliary classification, the positive inverse coordinate,
both grouped equivalences, all operation counts and highest forms. One
review additionally checked 1,024 signed whole-source substitutions
across the four variants and 330 positive gap instances from an
independent Pell recurrence. The trio is frozen after those reviews.
