# Support-sensitive quadratic source theorem

This note proves the new source reduction. It is conditional only on the
stated positive quadratic parent interface; it does not establish the
inherited native-window compiler-to-K215 theorem.

## 1. Keep the parent unshifted

Let the 22 original residuals be r_j(p_1,...,p_31), with positive integer
witnesses p_i. Leave these polynomials unshifted. Their union of ordinary
monomial supports has 62 members: the constant, 22 linear monomials, and
39 quadratic monomials. In contrast, substituting p_i=n_i+1 before packing
creates 71 supported monomials and 136 coefficient records. The unshifted
source has 94 records and 9 distinct nontrivial coefficient recipes.

Use original rows 1,2,3,4,5,6,7,9,...,22,8, negating original row 8.
The final row is P(P-k)+1-tau^2, so its constant is +1. Under the weighted
coefficient convention below its constant is +2.

The independently checked data are raw_recipes.json and
weights175_certificate.json. No consistency assumption enters their
construction.

The final root layout orders these normalized rows by the zero-based
permutation

    14,15,16,19,5,1,17,6,2,7,0,11,12,10,3,20,9,18,4,13,8,21

and assigns targets

    246,429,657,868,1058,1358,1550,1734,2058,2248,2545,
    2721,3063,3312,3506,3798,3989,4179,4367,4623,4817,5148.

The candidate was initially built with every target 104 larger. Since
the smallest kernel exponent was 104, translating every target down 104
preserves all differences and removes all unnecessary leading zero
positions. The final kernel exponent range is exactly 0 through 5148.
Its support contains 94 terms, all distinct. The full product degree is
at most M=5148+2*175=5498. This is the frozen released layout.

## 2. Only source-supported monomials need unique positions

Write w_0=0. The explicit weights w_1,...,w_31 are positive and distinct,
and at most t=175. For each alpha in the union S of parent supports, pad
alpha to degree two with the dummy coordinate 0. Require that its sum
e(alpha)=sum_i alpha_i w_i occurs for exactly that padded pair among *all*
528 unordered pairs of the 32 coordinates. Do not require the other pairs
to have distinct sums.

The supplied weights have only 278 distinct pair sums, so they are
deliberately not a Sidon set. Nevertheless all 62 supported pair sums are
isolated. This exact finite property is checked without assertions in
verify_support.py, both normally and under Python optimization.

For independent indeterminates p_i, put

    C_p(Z) = (1 + sum_i p_i Z^{w_i})^2.

At a supported exponent e(alpha), the coefficient is

    2! p^alpha / ((2-|alpha|)! product_i alpha_i!).

This follows from the isolated-pair property. Collisions among other
pair sums do not affect the assertion. If r_j=sum a_{j,alpha} p^alpha,
let c_{j,alpha}=(2-|alpha|)! product_i alpha_i! a_{j,alpha}.

## 3. Nonuniform targets

Choose integer targets E_j, all at least the maximum e(alpha) in their
respective row. For every distinct i,j require

    E_j-E_i != q-e(alpha)

for every source monomial alpha of row i and every unordered-pair sum q.
Define

    D(Z)=sum_{j,alpha} c_{j,alpha} Z^{E_j-e(alpha)}.

The coefficient at E_j in C_p D is exactly 2r_j(p): the same-row terms
use supported-pair isolation, and cross-row terms are excluded by the
displayed finite difference condition.

The condition also implies that different source terms in D do not
overlap. Within a row this follows from isolated pair sums. Between rows,
an overlap E_i-e(alpha)=E_j-e(beta) would give the prohibited difference
E_j-E_i=e(beta)-e(alpha), since e(beta) is itself a pair sum. Therefore if
|a_{j,alpha}|<=H, every coefficient of D has absolute value at most 2H.
No factor 22 is required in this bound.

Assume the final, negated row 8 has strictly greatest target E_*. Its
constant is 2, so D has leading coefficient 2 at exponent E_*. The other
terms of that row have positive e(alpha), and every earlier target is
smaller. Let M=E_*+2t. Then deg(C_p D)<=M, regardless of the collisions
among unsupported pair sums.

## 4. Positivity is a shift of the packed word, not of every residual

Use the inherited source variables f,g and put

    b=1+3f, B=beta_S b^2, ell=sum_i B^{w_i},
    N0=B^{t+1}, N1=4B^{M+1}, N=N0 N1.

The low mask still forces g=sum n_i B^{w_i}, with 0<=n_i<b. In the high
word use (1+ell+g)^2 D(B), because

    1+ell+g = 1+sum_i (n_i+1) B^{w_i}.

Thus the recovered parent witnesses are p_i=n_i+1, automatically positive.
Every positive parent solution is obtained for all sufficiently large b.
The residual polynomials themselves never need successor expansion.

Let beta_S be the same even power of two satisfying beta_S>4*33^2*H.
When b is a square and f!=0, b>=4 and B>2b. Distinct positive weights give
ell<2B^t. For every integer 0<=g<2bB^t, before digit recovery,

    1+ell+g < 3bB^t.

As before D(B)>0, because its leading coefficient is 2 and B-1>H.
Consequently the high word

    Jcode = 2(1+ell+g)^2 D(B) + sum_{i=0}^M B^{i+1}

obeys

    0<Jcode <= (36 H b^2+B) sum_{i=0}^M B^i < 2 B^{M+1}<N1.

The strict inequality follows from 36Hb^2<=B-2, which is much weaker
than the chosen beta_S bound. Thus all inherited arbitrary-g range
bounds continue to hold. This check is necessary before the finalizer
has recovered that b is a power of two.

After digit recovery p_i=n_i+1<=b, hence 1+sum p_i<=1+31b<33b. Every
coefficient of C_p D has absolute value below B/2. Adding B/2 to each
coefficient therefore gives an ordinary carry-free base-B word. At
target E_j its digit is B/2+2r_j(p), exactly as in the old source proof.
The target mask (B-2)sum_j B^{E_j}, acting on twice this word, forces all
those digits to their middle value. Hence it tests all parent equations.

The low and high words occupy separate blocks. The inherited no-carry
to-binomial-divisibility gadget can therefore be reused without changing
its statement. The remaining Sun finalizer is an inherited dependency.

For the forward lower bound g>=b, note that the all-one parent tuple is
not a solution (original residual 5 equals 1). Therefore some p_i>1,
so some n_i>0. Since all variable weights are positive, g>=B>b.
For sufficiently large b, digits n_i<=b-1 imply g<bB^t. This supplies
the exact old source interval b<=g<Ccap with Ccap=bB^t.

## 5. Degree caveat

Changing 1+g to 1+ell+g increases the degree of its squared factor.
Nevertheless the old offset B*sum_{i=0}^M B^i has degree 2(M+1), whereas
D(B)(1+ell+g)^2 has degree at most 2E_*+4t=2M. Hence the offset still
strictly dominates. The final polynomial's degree must be checked from
its actual DAG; this local observation prevents a false degree increase
from being inferred just from the new square.

For the frozen layout, the independent degree audit gives
deg(X)=34050, deg(Y)=22700, deg(Ccap)=351. The retained finalizer's degree
formula is 456 deg(X)+896 deg(Y)+24 deg(Ccap)+1760=35,876,184.
The coefficient at this upper bound after all ten variables are set
equal to T is 996362474 modulo the prime 1000000007, proving the bound
is attained. All 640 arithmetic operations are live: 422 multiplications,
138 additions, and 80 subtractions.

## Source provenance

The original parent data are 40-packing10/upstream/parent_sparse.json,
Git blob 3130e825d48df316c0e240838a92201329950ed6, at ProveIt commit
124c07c0b77a9e20e84676514d8b1ff78536ea3f. The inherited source construction
is 40-packing10/report.tex, blob 704d8d53ddc09fda0eae5890ab5eb899535a29f4.
The finite support search, support-specific condition, word-shift
construction, coefficient audit and proof in this note are new work
for the current request. No global optimality claim is made.
