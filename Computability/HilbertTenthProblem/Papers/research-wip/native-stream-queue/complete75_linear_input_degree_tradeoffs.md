# Degree tradeoffs from the linear input modulus

The same fixed universal compiler admits the following additional
polynomials, each with **19 strictly positive existential witnesses**
and the original ordinary positive input x:

| Operations | Multiplications | Additions/subtractions | Exact degree |
|---:|---:|---:|---:|
| **90** |47|43|**132**|
| **92** |48|44|**114**|
| **94** |48|46|**80**|
| **95** |48|47|**72**|
| **96** |48|48|**62**|
| **97** |48|49|**56**|

They use the new input-index modulus from
[linear-input89](complete75_linear_input_modulus89.md), together with
previously proved ways of grouping unit factors and retaining auxiliary
equalities separately. The 90-operation output is an unsquared unit
product minus one. The other five outputs are literal sums of squared
residuals. The earlier points 88/151, 89/135, 91/130 and 93/90 remain
distinct tradeoffs; no smaller operation bound than 88 is claimed here.

## 1. Exact definitions and positive domains

Keep all fixed compiler assumptions of
[coupled88](complete75_coupled_index_linear88.md), in particular

    B=2^d, d>=4, 0<MC,MF<B-1,
    MC=2 mod4, MF=4 mod8,
    popcount(MC)+popcount(MF)=d,

and its synchronization, transport and ordinary-input layout. Use
exactly the nineteen positive coordinates of linear-input89. All its
definitions and factor names are retained:

    kappa=u+delta*(a+1), u=2d*x+b,
    Delta=(a+2)^2-1, H=4a+3,
    mu=W+a*kappa+rho*H,
    K=Delta*(f^2-1), T=ic^2, V=of-c,

    N0=g^2+E*(kY)*(2g-k),
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3=K*(V^2-y^2)+y^2,
    Nk=k-R-hE,
    Nt=(K0+X)C+(q-F)-zplus*(q-1),
    N4=1+T^2-K,
    L=V-jc+k-hE.                                  (1)

The remaining definitions of q, X, Y, E, k, c, a, D, C, W and R are
exactly those displayed in linear-input89. Define two further proof
abbreviations

    U=jc-R, L0=1+V-U.

Their relation is

    L=L0+Nk-1.                                   (2)

U and L0 are paid registers only in the variants that actually use
them. Intermediate registers may be signed off the zero set. No new
positivity assumption on a computed difference is introduced.

## 2. Uncoupled 90-operation product

Replace the final coupled factor L by L0 and use

    P90=N0*N1*N2*N3*Nk*Nt*N4*L0-1.               (3)

Every positive zero of (3) has all eight factors equal to +1. Here is
the dependency check allowing the earlier proof to be reused after
changing the input modulus.

The sign proof in
[reversed auxiliary89 Sections 2–5](complete75_reversed_auxiliary89.md)
uses the input norm only to exclude N2=-1 modulo 4. It never uses the
old congruence `kappa=u mod Delta`. The positive first-root change from
[positive-root89](complete75_positive_root89.md) also preserves its
argument. Thus that proof applies to (3) with the new kappa. Explicitly,
it first gives `N0=N1=N2=N3=N4=1`, then obtains C>=0 and all pre-kernel
bounds from Nt being an integer unit. Put `Nk=epsilon` and `L0=lambda`.
The unchanged strong norm and generic signed-index argument give

    c=psi_A(p), p=R+1-lambda,
    k=2psi_(2XY^2+1)(n), 2n=R+epsilon,
    p-2n=1-lambda-epsilon.                        (4)

The three sign pairs other than `epsilon=lambda=1` have p>=2n+1.
Pell duplication with `Q=2A^2-1>2XY^2+1` then implies

    c>=psi_A(2n+1)>A*k>k(Y+1),

contradicting the two retained positive ratio slacks. Hence
`Nk=L0=Nt=1`. The full strong auxiliary equation has remained in place
throughout this recovery.

Equation (2) now gives L=1, so the identical supplied tuple is a zero
of linear-input89. Its smaller-modulus proof establishes the exact
ordinary-input relation and restores all old positive witnesses.
Conversely each positive zero of linear-input89 has every coupled
factor equal to one. Equation (2) gives L0=1, so it is also a zero of
(3). This proves equality of their positive zero sets in the new
delta coordinates.

Relative to the actual linear-input89 source, introduce `U=jc-R` and
replace the two final linear gates by `V-U` and `1+(V-U)`. The index
base `k-hE` is unchanged. This adds precisely one subtraction. The
certificate costs 89=47M+42A with one comparison; the final subtraction
in (3) gives **90=47M+43A**.

## 3. Two families of sum-of-squares polynomials

For the coupled family, retain the full strong comparison

    T^2=K,

and partition the seven factors

    (N0,N1,N2,N3,Nk,Nt,L).                        (5)

For each group compare the product of its factors with one. The output
is the sum of the square of `T^2-K` and the squares of these group
residuals. Their simultaneous vanishing makes N4=1 and makes the
product of (5) equal to one. Therefore linear-input89 vanishes.
Conversely its positive zeros make all eight factors individually one,
so every group comparison and the strong comparison hold. This proves
exact equality of positive zero sets for every partition used here.

For the six-factor family, retain both full auxiliary comparisons

    T^2=K, U=V,

and partition only `(N0,N1,N2,N3,Nk,Nt)`. At a zero of the resulting
sum of squares, N4=L0=1 and the product of these six factors is one.
Thus (3) vanishes. Its proved positive equivalence supplies the converse
and ordinary-input theorem. In particular, a group containing Nk and Nt
does not silently assume that each has positive sign; that conclusion
is supplied by the uncoupled sign proof in Section 2.

The exact chosen partitions are as follows. Parentheses denote a group
whose product is compared with one.

| Cost/degree | Family | Groups | Group degrees |
|---|---|---|---|
|92/114|coupled|(N0,N3,Nk,Nt), (N1,N2,L)|56,57|
|94/80|coupled|(N0,N1), (N2,Nk,Nt), (N3,L)|36,40,37|
|95/72|six|(N0,N1), (N2,Nk), (N3,Nt)|36,35,33|
|96/62|coupled|(N0,Nk,Nt), (N1,L), (N2), (N3)|28,31,26,28|
|97/56|six|(N0,Nk,Nt), (N1), (N2), (N3)|28,22,26,28|

The maps to the earlier discriminant-modulus constructions remain the
proved positive maps `delta_new=(a+3)delta_old` and their inverse on
zeros. All other positive coordinates and fixed compiler numerals are
unchanged. No canonical-subfamily restriction is used.

## 4. Literal ledgers

The [checker](complete75_linear_input_degree_tradeoffs.py) constructs
every variant from the actual linear-input89 DAG. In the coupled
sum-of-squares family it omits the two strong-unit definitions and the
old product chain, visits all seven factor definitions and both strong
comparison terms, then adds exactly the chosen group products.
The common definitions cost **79=40M+39A**. With g groups there are
7-g additional products and g+1 equations. Forming and summing all
squared residuals gives

    certificate: (47-g)M+39A = 86-g,
    polynomial: 48M+(40+2g)A = 88+2g.             (6)

In the six-factor family, the two coupled linear-factor gates are also
omitted and the single gate `U=jc-R` is added. The definitions cost
**78=40M+38A**. There are 6-g products and g+2 equations, giving

    certificate: (46-g)M+38A = 84-g,
    polynomial: 48M+(41+2g)A = 89+2g.             (7)

| Polynomial | Certificate gates | Certificate M/A | Equations |
|---:|---:|---:|---:|
|90|89|47/42|1|
|92|84|45/39|3|
|94|83|44/39|4|
|95|81|43/38|5|
|96|82|43/39|5|
|97|80|42/38|6|

Every row has nineteen supplied positive witnesses. All products by
fixed numerals, squares, residual subtractions and binary additions
are charged. The receipt lists every actual instruction and comparison;
there is no runtime power, conjunction or unpaid state predicate hidden
in these schedules.

## 5. Exact degrees and partition scope

Write `Q=(B-1)J`, `k0=eta+zeta`, `gamma0=rho+sigma`,
`Ctop=Q-F-Z-alpha-2d*x`, and `g0=2g-k0`. For fixed numerals of degree
zero and all supplied variables of degree one, the highest forms are

| Factor | Degree | Highest form |
|---|---:|---|
|N0|14|`H0=w*s^2*k0*Q^9*g0`|
|N1|22|`H1=8gamma0*k0*w^2*s^3*Q^15`|
|N2|26|`H2=4delta*(2rho-delta)*w^3*s^3*Q^18`|
|N3|28|`H3=f^2*k0^2*w^2*s^4*Q^18`|
|Nk|9|`Hk=-h*w*s*Q^6`|
|Nt|5|`Ht=w*Q^3*Ctop`|
|N4|22|`H4=i^2*k0^4*s^4*Q^12`|
|L|9|`HL=-h*w*s*Q^6`|
|L0|6|`HL0=-j*k0*s*Q^3`|

The exact degree of (3) is therefore 132. Its highest form is

    32*(B-1)^84*h*(rho+sigma)*delta*(2rho-delta)
      *i^2*j*f^2*(eta+zeta)^9*w^10*s^18*J^84
      *Ctop*(2g-eta-zeta).                         (8)

The strong and linear residuals have degrees 22 and 6. They cannot
contribute at the highest degree of any chosen sum of squares. In the
order of the five rows of the partition table, the highest forms are

    (H1*H2*HL)^2,
    (H2*Hk*Ht)^2,
    (H0*H1)^2,
    (H1*HL)^2,
    (H0*Hk*Ht)^2+H3^2.                           (9)

All displayed factors are nonzero polynomials for every admissible B.
A sum of real polynomial squares cannot cancel identically, so (8)–(9)
establish the stated exact degrees, including the two equal-degree
contributions in the 97-operation case.

The checker exhaustively enumerates set partitions in five existing
literal families after the modulus change. The following entries are
the smallest possible largest residual degree for g=1,2,... groups:

| Fixed factors/family | Polynomial cost | Minimum largest degrees |
|---|---|---|
|seven coupled factors, strong separate|`88+2g`|113,57,40,31,28,28,28|
|eight coupled units|`88+2g`|135,68,46,36,31,28,28,28|
|seven uncoupled factors, strong separate|`89+2g`|110,55,37,28,28,28,28|
|five factors, three comparisons separate|`90+2g`|99,50,36,28,28|
|six factors, two comparisons separate|`89+2g`|104,53,36,28,28,28|

The five- and six-factor families are those of
[positive-root degree tradeoffs](complete75_positive_root_degree_tradeoffs.md),
with the same paid auxiliary and transport comparisons. Their literal
counts change only by the one new modulus addition. The eight-unit
row refers to squaring grouped residuals; it does not supplant the
cheaper unsquared product at 89 operations.

This enumeration proves optimality only within each stated partition
family with fixed factors and literal residual schedules. Combining
those rows with the already established 91/130 and 93/90 points gives
the six new undominated points at the start of this note. It does not
claim a global arithmetic or degree lower bound. In particular the
97/56 point improves on the coupled family's 98/56 option; a proposed
four-group 96/56 would be impossible in that family because its seven
factor weights sum to 113, exceeding four times 28.

## 6. Verification

Run the checker normally to compare its fresh deterministic result to
the [receipt](complete75_linear_input_degree_tradeoffs.json):

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_linear_input_degree_tradeoffs.py

For each of the six variants, it checks 512 direct full-polynomial
identities against independent factor formulas and 512 forward-coordinate
identities with the old modulus. These include signed supplied values,
deliberately negative computed input roots and zero restored transport
quotients. Three weighted, offset polynomial specializations per
variant check all factor degrees and highest forms, retained residual
degrees, exact output degrees and leading coefficients. It audits
acyclic instruction dependencies, operation histograms, equations and
positive witness counts. The partition enumeration includes all 4,140
partitions of eight factors, both sets of 877 seven-factor partitions,
203 six-factor partitions and 52 five-factor partitions.

Those finite arithmetic checks do not purport to materialize accepting
compiler tuples. The complete positive equivalence follows from
Sections 2–3 and the inherited ordinary-input theorem.

Two independent full proof/source/default reviews passed without findings.
They checked the uncoupled sign recovery before input decoding, identity
(2), both grouped positive equivalences, every literal ledger and all
highest forms, including the two noncancelling squares at 97/56. One
review independently reproduced every listed partition minimum by
subset dynamic programming and checked 1,536 additional signed
full-polynomial identities across the six variants. The trio is frozen
after those reviews.
