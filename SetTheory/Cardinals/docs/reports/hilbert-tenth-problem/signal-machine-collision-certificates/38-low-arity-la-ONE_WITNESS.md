# A one-positive-witness alternative, and exact zero-witness classification

4 October 2026. A separate mathematical alternative to `PROOF.md`. This note
does not alter the two-witness construction, its degree bound, or any earlier
packet. The native finite-table theorem below is elementary and independent of
POWER. The later gap composition explicitly imports the accepted twelve-leaf
POWER theorem. This is a static proof and cost analysis, not an execution of a
counter interpreter, source checker, or upstream theorem prover.

## 1. Domain, clipping, and statement

Write Z_{>0} for the positive integers. Fix T>=0, put K=T+1, and let

    c_K(x)=min(x,K),
    S subset {1,...,K}^2.

The table S is fixed coefficient data, not an input or a witness. Its associated
set of positive inputs is

    U_S={(A,B) in Z_{>0}^2 : (c_K(A),c_K(B)) in S}.

There is an explicit integer polynomial Q_S(A,B,w) such that

    (A,B) in U_S iff there exists w in Z_{>0} with Q_S(A,B,w)=0.

Every accepted input has exactly one positive w. Moreover Q_S is nonnegative
on all of R^3. For K>=2 its exact total degree is

    D_S=2 n_I+4T n_E+8T n_C <=10T^2+8T,                    (1)

where n_I counts accepted cells (i,j) with i,j<K, n_E counts accepted cells
with exactly one coordinate K, and n_C is 1 or 0 according as (K,K) is
accepted or rejected. For S empty use Q_S=1 and D_S=0.

For a fixed deterministic two-counter program and horizon T, S can be the
by-T table or the first-exactly-T table on native representatives (i-1,j-1).
The usual clipping lemma applies to both: after t<T common transitions, a
counter clipped initially to T is at least T-t>0, and the original counter
has its unchanged nonnegative initial offset. Thus both runs make the same
next zero/nonzero decision. An initially smaller counter is identical in the
two runs. Induction gives the same state/branch prefix through transition T.
No test after that prefix is needed. Making the halt state absorbing for
prefix bookkeeping handles by-T acceptance, while the common prefix also
preserves the first arrival time. Consequently this table describes the actual
bounded predicate for every positive A,B, including arbitrarily large ones.

T indexes a family of polynomials. This is not one fixed polynomial with T
as a free variable, and computing the table remains separate paid work.

## 2. Cell factors and the unique positive witness

Assume K>=2. Define the integer polynomial

    p_K(x)=product_(h=1)^T (x-h)^2.                          (2)

For a positive integer x,

    p_K(x)=0 iff x<K,
    p_K(x)>0 iff x>=K.                                      (3)

It is nonnegative for every real x. Define a cell factor f_(i,j) as follows:

    i<K, j<K:
      f_(i,j)=(A-i)^2+(B-j)^2+(w-1)^2;

    i<K, j=K:
      f_(i,K)=(A-i)^2+(w-p_K(B))^2;

    i=K, j<K:
      f_(K,j)=(B-j)^2+(w-p_K(A))^2;

    i=j=K:
      f_(K,K)=(w-p_K(A)p_K(B))^2.                         (4)

Now put

    Q_S=product_((i,j) in S) f_(i,j),                       (5)

with empty product 1. All coefficients are integers, and each factor, hence
their product, is nonnegative over the reals.

For positive A,B,w, each factor vanishes exactly on its claimed clipped cell:

- An interior factor forces A=i, B=j, w=1
- The factor f_(i,K) forces A=i and w=p_K(B)>0, hence B>=K
- The factor f_(K,j) forces B=j and w=p_K(A)>0, hence A>=K
- The corner factor forces w=p_K(A)p_K(B)>0; nonnegativity
  of the two factors in (2) and (3) force A,B>=K

The converses hold with the displayed values of w. A product of real numbers
is zero exactly when a factor is zero. Therefore a positive zero of Q_S
selects an accepted clipped cell. The clipped cells partition Z_{>0}^2, so
for a given positive input at most one cell factor can vanish at a positive
w. On an accepted cell its unique value is

    w=1                              if A,B<K,
    w=p_K(B)                         if A<K<=B,
    w=p_K(A)                         if B<K<=A,
    w=p_K(A)p_K(B)                    if A,B>=K.             (6)

These values are positive integers. This proves soundness, completeness,
uniqueness, and all domain obligations without inequalities hidden in the
equation. Strict positivity is essential: allowing w=0 in an edge factor
would let a below-threshold value with p_K=0 masquerade as a tail value.

### Horizon zero

For K=1 there is only one clipped cell. If S={(1,1)}, use Q_S=(w-1)^2;
if S is empty, use Q_S=1. The respective degrees are 2 and 0. Thus the literal
one-witness presentation remains available at T=0, with unique witness 1 in
the accepted case. In the rejected case w is an unused formal variable and
there are no solutions. Formula (1) is only for T>=1.

## 3. Exact degree and what the square count means

The exact factor degrees in (4) are 2, 4T, 4T, 8T. For example, the leading
term of p_K is x^(2T); consequently the edge square has leading term B^(4T)
or A^(4T), and the corner square has leading term A^(4T)B^(4T).
All factors are nonzero polynomials. Degree is additive under products in
R[A,B,w], proving the equality in (1). The ceiling follows from

    n_I<=T^2, n_E<=2T, n_C<=1.

The full table attains 10T^2+8T for this displayed formula, although that
predicate itself is a tautology and admits much simpler formulas. This is
not a lower bound on the degree of another representation. If S is nonempty,
the coefficient of w^(2|S|) in Q_S is 1, so w genuinely occurs in this native
polynomial; rejected empty tables are the explicitly noted exception.

Each interior factor is a sum of three residual squares, each edge factor a
sum of two, and the corner a single square. Fully distributing the product
as a sum of squares gives

    3^(n_I) 2^(n_E)                                         (7)

literal square slots: choose one squared residual from every factor and
square the product of the chosen residuals. Corner factors offer one choice.
For the empty product the same convention is the single square 1^2.
Coincident or zero terms could sometimes be simplified, but (7) describes
the uncompressed distributive presentation, not a minimal SOS length.

Thus Q_S is a compact product of sums of squares. It is not in general one
literal residual square. One may instead use Q_S^2=0, with identical zeros
and degree 2D_S. The distinction matters in the composition ledger below.
An exponentially large distributed SOS expression does not imply
exponentially many monomials in its collected polynomial: degree and the
fixed number of variables give a polynomial support bound.

## 4. Coefficients, support, storage, and arithmetic costs

These are uniform upper bounds for the displayed presentation, not claims
of optimality or comparisons of every individual instance. Let ||f||_1 be
the sum of the absolute values of its integer coefficients, and put

    P_K=(K!)^2,
    M_I=2K^2+4,
    M_E=K^2+(1+P_K)^2,
    M_C=(1+P_K^2)^2,
    C_S=M_I^(n_I) M_E^(n_E) M_C^(n_C).                      (8)

The coefficients of p_K alternate in sign because every root is positive,
with its multiplicity counted. Hence

    ||p_K||_1=product_(h=1)^T (1+h)^2=P_K.

Subadditivity and submultiplicativity of coefficient norm give

    ||f_(i,j)||_1 <= M_I                   for interior cells,
    ||f_(i,K)||_1, ||f_(K,j)||_1 <= M_E     for edge cells,
    ||f_(K,K)||_1 <= M_C,
    ||Q_S||_1 <= C_S.                                      (9)

For example ||(A-i)^2||_1=(i+1)^2<=K^2, and
||(w-p_K(B))^2||_1<=(1+P_K)^2. These bounds include constants and all
positive/negative terms; nonnegative values of a polynomial do not mean its
coefficients are nonnegative.

Every coefficient magnitude needs at most ceil(log2(C_S+1)) bits; add a sign
bit if desired. Uniformly in S this is O(K^2 log(K+1)), since

    log C_S <= T^2 log M_I+2T log M_E+log M_C.

The sharper cell-type count is used here. Applying the corner bound to all
K^2 factors would give an unnecessarily worse coefficient estimate.

### Expanded polynomial storage

There are three variables and total degree D_S. The support therefore has at
most

    binom(D_S+3,3)=O(K^6)                                  (10)

monomials. For Q_S^2 replace D_S by 2D_S and C_S by C_S^2; the same
asymptotic support and coefficient-bit bounds hold. A sparse list storing
three binary exponents and one signed coefficient per monomial consequently
uses O(K^8 log(K+1)) bits. This is a bound, not a claim that all monomials
occur. The K=1 formulas are constant-size exceptions. These expanded bounds
are worse than the two-witness compiler's bounds in `PROOF.md`; the witness
saving here is not a simultaneous degree/support/storage improvement.

### Factored arithmetic circuit

A direct shared circuit has only O(K^2) ordinary integer arithmetic gates.
Here is an explicit upper bound for T>=1, including preparations that can be
omitted when unused. Form the 2T differences A-h,B-h, square each, and form
p_K(A),p_K(B) from the corresponding T squares. This costs 2T
additions/subtractions and 4T-2 multiplications. Also prepare

    (w-1)^2, (w-p_K(A))^2, (w-p_K(B))^2,
    (w-p_K(A)p_K(B))^2.

This adds four subtractions and five multiplications. Interior factors take
two additions apiece; edge factors take one; the corner is already prepared.
Multiplying the N=|S| factors takes max(N-1,0) multiplications. Thus

    multiplications <=4T+3+max(N-1,0),
    additions/subtractions <=2T+4+2n_I+n_E.                 (11)

For N>=1 the combined bound is at most 3T^2+10T+7. For S empty simply return
1 with no arithmetic. Squaring the result for the alternative Q_S^2 costs
one extra multiplication. This gate count treats additions, subtractions,
and multiplications as unit-cost integer operations; it is not bit
complexity. Large positive inputs and the values p_K(A),p_K(B) require their
full integer precision.

The table needs K^2 bits, and the small constants 1,...,T and circuit indices
fit in an O(K^2 log(K+1))-bit straightforward factored encoding. For an
arbitrary program's table, determining its K^2 entries still requires in
principle up to K^2 T representative transitions, with counters at most
2T in those runs. No such interpreter execution is used in this note.

### One conservative expansion bound

Expanded factors have at most 7 monomials for an interior factor, 6T+5 for
an edge factor, and

    1+(2T+1)^2+(4T+1)^2

for the corner. These counts follow directly from w^2-2wp+p^2 and its
two-coordinate counterpart. Construct p_K by successive linear
multiplications in O(K^2) integer operations, and form the displayed factors.
Every intermediate partial product has at most binom(D_S+3,3) monomials.
Straight pairwise monomial convolution, collecting equal exponents at each
step, therefore takes O(K^8) coefficient additions/multiplications: the sum
of the above factor-support bounds over S is O(K^2). Indexing/bookkeeping is
separate from this coefficient-operation count. Coefficient intermediates
have O(K^2 log(K+1)) bits by the same product-of-norms bounds. A further
naive self-convolution to form Q_S^2 uses at most O(K^12) coefficient
operations; no sharper claim is needed here.

## 5. Composition with the accepted twelve-leaf POWER module

Only this section uses the accepted POWER theorem. We repeat its complete
base-two residuals so that the composed polynomial is unambiguous. For a
positive index C, use six direct positive leaves

    o,g,q_b,q_v,J,q_alpha,

and six distinct positive adapter leaves for the natural aliases

    d_wb,d_wC,d_yC,q_sigma,q_tau,q_r.

Each natural alias is its own positive adapter minus one. Define expressions,
not new variables,

    omega=2+d_wb, y=C+d_yC, beta=1+4y q_b,
    v=y^2 q_v, t=C+4y q_tau, M=2o+J, Z=2o+J+5,
    X=y(Z-8)+8o+4M q_r,
    U=4beta-Z, V=q_alpha X+U q_sigma.

The five residuals are

    H1=X^2-16-(Z^2-16)y^2,
    H2=U^2-16q_alpha^2-(Z^2-16)q_alpha^2 v^2,
    H3=V^2-16q_alpha^2-16q_alpha^2(beta^2-1)t^2,
    H4=omega-C-d_wC,
    H5=Z^2-16-16((omega+1)^2-1)(omega g)^2.                (12)

The imported theorem says that, for positive C,o, these equations have
eleven positive auxiliary leaves beyond o exactly when o=2^(C-1). Their
sum of squares has exact total degree 20. Every accepted C,o has infinitely
many full module tuples. This includes exponent zero C=1.

The precise accepted proof is
`/workspace/shared/positive-power12-continuation-20261004/PROOF.md`, also
retained in this packet's dependencies as identified by `SOURCE_PINS.json`.
Its constructive Pell dependency is mathlib4 commit
`ac77769fabe23cb237559e7f56578dbead91499f`, declarations
`Pell.matiyasevic` and `Pell.eq_pow_of_pell` in
`Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256
`993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`.
This note imports that all-exponent result, including its integer/sign
recoveries and constructive strict-positive-quotient argument; it does not
replace it with finite evidence or claim new theorem-prover execution.

Let g1,g2,g3 be arbitrary positive integer external inputs and let
D=g1+g2+g3 be an expression. Take positive shifted-counter witnesses A,B,
two copies of (12) with (C,o)=(A,p) and (B,q), all module leaves distinct,
and the single native witness w. Put

    G1=(20g1-D)p-2D,
    G3=(20g3-D)q-2D,
    E=G1^2+G3^2+sum_(i=1)^5 (H_i^A)^2
                    +sum_(i=1)^5 (H_i^B)^2.               (13)

There are two useful complete polynomials:

    F_S=E+Q_S(A,B,w),
    F_S,sq=E+Q_S(A,B,w)^2.                                 (14)

In either case all summands are globally nonnegative. A zero is equivalent
to the simultaneous vanishing of every decoding residual and Q_S. It
therefore gives p=2^(A-1),q=2^(B-1) and exactly

    g1/D=1/20+(1/10)2^(-(A-1)),
    g3/D=1/20+(1/10)2^(-(B-1)),                             (15)

with (A,B) in U_S. Conversely every positive triple with the encoding (15)
and accepted counters provides module witnesses and the unique w from (6),
or w=1 at K=1. No promise that an arbitrary input triple is encoded is
assumed; unencoded triples have no solution.

### Literal ledger and fibers

Both presentations have exactly

    external positive inputs: 3,
    positive witnesses: 2+2*12+1=27,
    total variables including inputs: 30,
    final equations: 1.                                    (16)

The twelve decoding residual-square slots in E are 2 gap slots plus 10
POWER slots. F_S adds one product-of-SOS block, not one literal residual
square. Its fully distributed SOS has 12+3^(n_I)2^(n_E) literal slots for
K>=2, with the empty-product convention above. F_S,sq has exactly 13 literal
residual-square slots. Both K=1 choices for Q_S are squares, so the
unsquared-block presentation has 13 literal square slots there as well.
The counts retain formal slots and variables even in degenerate cases.

The input fixes p=2D/(20g1-D) and q=2D/(20g3-D) whenever a zero exists; the
equations and positivity force both denominators positive. Injectivity of
positive powers of two then fixes A,B, and the native theorem fixes w.
Hence the projection (A,B,p,q,w) is unique. Nevertheless the full 27-witness
fiber is infinite whenever nonempty, by varying either POWER module's
accepted infinite family while keeping its index/output and all other
variables fixed. The one-witness native result does not make this
composition finite-fold.

### Exact degrees without a cancellation assumption

The accepted module's degree-twenty coefficient-one monomial

    J^4 q_alpha^4 d_yC_plus^8 q_v^4

is absent from every other block and the other independent module. Thus
deg E=20; the gap squares have degree four. More generally, a nonzero
globally nonnegative real polynomial has nonnegative top homogeneous part:
scale its arguments by a positive real parameter and take the leading
limit. Such top parts cannot cancel in a sum, because a sum of nonnegative
functions is identically zero only when every summand is identically zero.
Apply this to E and Q_S, or to their explicit distributed sums of squares.
Consequently

    deg F_S=max(20,D_S),
    deg F_S,sq=max(20,2D_S).                               (17)

For T>=1 the respective uniform ceilings are
max(20,10T^2+8T) and max(20,20T^2+16T); for T=0 both degrees are 20.
The native block uses only A,B,w, so its support/coefficients satisfy
Section 4. Each decoding block has a fixed finite support and coefficient
list independent of T after renaming its variables. Adding these blocks
therefore adds only a T-independent number of monomials and does not
invalidate the O(K^6) support and O(K^8 log(K+1)) storage bounds, despite
the final polynomial having 30 total variables. No generic 30-variable
dense bound is needed.

## 6. Exact criterion for eliminating the native witness entirely

This theorem concerns a fixed clipping table and one polynomial equality,
with unrestricted degree and table-dependent coefficients. It is not a
global MRDP minimality statement.

The following are equivalent:

1. There is a polynomial R(A,B) with integer coefficients such that, on all
   positive integer inputs, R(A,B)=0 exactly for U_S
2. Whenever (i,K) is accepted, (i,j) is accepted for every j in {1,...,K};
   whenever (K,j) is accepted, (i,j) is accepted for every i in {1,...,K};
   and an accepted corner (K,K) forces the full table
3. For every accepted cell, replacing any or all of its tail coordinates K
   by arbitrary indices in {1,...,K} preserves acceptance

The joint replacement clause includes the corner. It is not a requirement
to replace a fixed coordinate i<K, and it is not the usual order-ideal
condition on all coordinates.

### Necessity: infinite grids force the coordinate-flat closure

The argument works in d dimensions and even for real-coefficient
polynomials. Suppose a polynomial R is zero at every positive integer point
of an accepted cell. Fix its non-tail coordinates at their cell values.
The remaining tail variables range independently over {K,K+1,...}.
The resulting polynomial is zero on this entire infinite Cartesian grid.

A polynomial zero on a product of infinite subsets of R is the zero
polynomial. For one variable this is the finite-root theorem. Induct on the
number of variables: view the polynomial as a polynomial in the last
variable; fixing all earlier variables in their infinite sets forces all
its coefficients to vanish there, and apply induction to those coefficient
polynomials. Hence the restriction of R to this coordinate flat vanishes
identically. In particular it vanishes when each formerly tail coordinate
is any positive integer below K as well. Exact representation therefore
requires acceptance of every jointly replaced clipped cell. This proves
necessity without any positivity or SOS assumption on R.

### Sufficiency: an explicit zero-witness polynomial

For each accepted cell a=(a1,a2), let J(a) be the set of its tail
coordinates. With X1=A,X2=B define

    Z_a(X)=sum_(l not in J(a)) (X_l-a_l)^2,
    R_S(X)=product_(a in S) Z_a(X).                         (18)

An empty sum is 0 and an empty product is 1. Thus S empty gives R_S=1.
If an all-tail cell is accepted, closure forces S full and the corresponding
factor is 0, so R_S is the zero polynomial, as required.

Otherwise each factor is a nonzero sum of squares. At positive X the factor
Z_a vanishes exactly when all its fixed coordinates equal a's fixed
coordinates, with no restriction on the former tails. Its clipped cell is
obtained from a by the jointly allowed replacements. The closure condition
therefore gives R_S=0 only on accepted inputs. Conversely an accepted input
makes the factor of its own clipped cell vanish. This proves sufficiency.
When S is nonempty and contains no all-tail cell, the displayed polynomial
has exact degree 2|S|; this degree is not asserted minimal.

Combining necessity, sufficiency, and Sections 1-2 proves the exact minimum
number of positive existential auxiliary variables for this fixed table,
within a single polynomial equality and without a degree bound:

    minimum=0 if the closure condition holds,
    minimum=1 otherwise.                                   (19)

At K=1 both possible tables have minimum zero, represented by 0 or 1.
Empty, full, and finite interior-only tables also illustrate why a uniform
one-witness construction need not be minimal for every particular table.
This does not classify the minimum arity of the POWER/gap composition, nor
does it claim novelty or compare with arbitrary unbounded computations.

## 7. Optional d-input extension

Fix d>=1 and S subset {1,...,K}^d, with K>=2 and T=K-1. For a cell a let
J(a)={l:a_l=K}, t(a)=|J(a)|, and set

    f_a(X,w)=sum_(l not in J(a)) (X_l-a_l)^2
                  +(w-product_(l in J(a)) p_K(X_l))^2,
    Q_S(X,w)=product_(a in S) f_a(X,w).                     (20)

The empty inner product is 1. For positive integer inputs, p_K is zero
exactly off the tail and positive exactly on it. Therefore (20) again
represents the table with one unique positive witness, equal to the
product of p_K over the actual tail coordinates, or 1 with no tails.
Every factor is globally nonnegative and is a nonzero polynomial.

If t(a)=0 its degree is 2. If t(a)>=1 its degree is 4T t(a). Thus the exact
degree is the sum of those cell degrees, with empty table degree zero.
There are T^d cells with no tails, and across all K^d cells the total tail
coordinate count is d K^(d-1). This yields

    deg Q_S <=2T^d+4dT(T+1)^(d-1).                         (21)

For fixed d, this is O(T^d), and the support is at most
binom(deg Q_S+d+1,d+1), polynomial in T for fixed dimension. Distributing
the product into SOS slots may still be exponential in |S|. All these
bounds allow dependence on d; no dimension-uniform polynomial claim is
made. The K=1 alternative is again (w-1)^2 or 1.

The zero-witness theorem and construction (18) hold verbatim with d
coordinates: every accepted cell must contain its full coordinate-flat
closure in the clipped table. Therefore the same exact zero-versus-one
classification (19) holds for every fixed finite d-dimensional clipping
table. All claims remain scoped to the finite table, positive integer
domains, a single polynomial equation, and no imposed degree bound.

## 8. Verification boundary

The native proofs above are all-input symbolic arguments. They do not
depend on finite enumeration, numerical fitting, or execution of a machine
interpreter. The accepted POWER proof and the main two-witness proof were
read as static text to check the ledger and imported theorem boundary.
No scripts, interpreters, upstream checks, or source theorem provers were
run in preparing this note. Any subsequently recorded fresh static algebra
checks are corroborating evidence and must be identified by their actual
completed results, not treated as the proof of the infinite-domain claims.

The precise minimum in (19) is a narrow fixed-table theorem proved here;
there is no claim of global arity minimality, smallest degree, smallest
coefficients, universal-polynomial records, novelty, priority, or finite-fold
behavior of the composed 27-witness representation.
