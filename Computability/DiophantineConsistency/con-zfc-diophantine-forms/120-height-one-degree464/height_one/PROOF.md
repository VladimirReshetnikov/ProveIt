# A height-one quartic compiler over the integers

## Result and scope

The supplied ordinary polynomial `output/polynomial.json` has **7,431
unrestricted integer variables**, total degree **4**, **34,086** nonzero
monomials, and every nonzero coefficient in **{-1,+1}**. Its constant
coefficient is 1. Its degree in each individual variable is at most 2.
The polynomial is nonnegative at every real tuple.

Its integer zeros are in explicit bijection with the integer zeros of the
supplied 519-variable system of 321 quadratic residuals. More precisely,
there is an explicitly specified polynomial map L with integer coefficients
such that, for every integer x,

    P(L(x)) = sum_j R_j(x)^2.

At zeros, a coordinate projection recovers x and is inverse to L. The
519-variable source is the centered direct C222 construction in the
Round14 incoming package, with exact source provenance in
`source/PROVENANCE.json`. It uses neither K215 execution nor Jones's
universal polynomial. Its ordinary source calibration is inherited;
this compiler does not replace that proof or establish Con(ZFC).

Combining the source's ordinary ZFC-formalizable proof with the theorem
below gives

    ZFC proves: [P has no integer zero] iff Con(ZFC).

Coefficient height 1 is the absolute minimum for a nonzero polynomial
with integer coefficients. This optimizes that metric, at a cost in the
number of variables. It does not claim globally minimal degree, variable
count, number of monomials, or description length. No worldwide-priority
claim or new Lean/Rocq proof is made.

## 1. Exact normalization to signed unit occurrences

Start with a finite system R_j(x)=0 over the integers, each residual of
degree at most 2. A polynomial is given by its collected nonzero terms
c*x_{i_1}...x_{i_d}, with d<=2. Normalize it to a quadratic system whose
terms are *occurrences* with signs +1 or -1. Occurrences need not be
distinct: in particular, 2x is represented by x+x at this intermediate
stage. The final polynomial is fully collected.

To avoid a unary expansion of large coefficients, introduce a variable
C_c for each required integer c>1 and its repeated binary halves. Define
them in increasing order by

    C_c - H_c - H_c - (c mod 2) = 0,

where H_c=1 if floor(c/2)=1 and H_c=C_floor(c/2) otherwise. The final
constant term is omitted for even c. Every constructor is monic in its
new variable, and its other variables precede it. Induction gives C_c=c
over the integers, without any positivity assumption.

For each needed pair (c,x_i), introduce a shared variable S_(c,i) and the
quadratic equation

    S_(c,i) - C_c*x_i = 0.

An original term with coefficient of absolute value c>1 is replaced as
follows, retaining its original sign:

| Original unsigned term | Replacement |
| --- | --- |
| c | C_c |
| c*x_i | C_c*x_i |
| c*x_i*x_j | S_(c,i)*x_j |

Coefficients of absolute value 1 require no change. Every old solution
extends uniquely to the new coordinates. Conversely, the topological
monic constructor equations force the displayed constants and scales;
substitution recovers every original residual exactly.

Write the normalized residuals as

    A_r(v) = sum_(i=1..s_r) epsilon_(r,i) t_(r,i)(v),

where epsilon is +1 or -1 and each t is a monomial of degree 0,1, or 2.

## 2. Disjoint occurrence copies

For every term occurrence t_(r,i), create two completely fresh alias
coordinates a_(r,i), b_(r,i), and a fresh product coordinate w_(r,i).
If t has degree 2, a and b are aliases of its respective old factors.
If it has degree 1, a aliases that factor and b is an alias of the fixed
unit 1. If it has degree 0, both a and b alias 1.

Put m_(r,i)=a_(r,i)*b_(r,i). This is always a homogeneous quadratic
monomial. Distinct m occurrences have disjoint supports, even when they
represent the same original monomial or factor. All w variables are
distinct from all aliases and from one another.

The distinction is essential. The later consistency constraints identify
aliases only on the zero set; they are separate indeterminates in the
expanded polynomial. That prevents coefficient collisions.

## 3. A nonnegative coefficient-one row energy

For one normalized residual suppress r and write s=s_r, signs epsilon_i,
products m_i, and independent product coordinates w_i. Define

    E = sum_i (m_i^2+w_i^2)
        + sum_(i<j) epsilon_i*epsilon_j*(m_i*m_j+w_i*w_j)
        - sum_i m_i*w_i.

This is an ordinary integral polynomial. The identity

    2E = (sum_i epsilon_i*m_i)^2
         + (sum_i epsilon_i*w_i)^2
         + sum_i (m_i-w_i)^2

proves E>=0 over the reals. It also proves that E=0 exactly when every
w_i=m_i and the original signed sum of the m_i vanishes. There is no
sign assumption on any variable.

Each nonzero coefficient of E is +1 or -1. Its quartic monomials are
m_i^2 and m_i*m_j; distinct occurrences use disjoint pairs of aliases,
so all these monomials are distinct. Its cubic monomials are m_i*w_i,
all distinct. Its quadratic monomials involve only the independent w
variables and are again distinct. Thus one row with s occurrences
contributes exactly s^2+2s nonzero terms.

The factor 1/2 occurs only in the positivity identity, not in the
coefficients of the delivered polynomial.

## 4. Equality cycles without a coefficient 2

Collect all aliases of a given normalized variable into a group
a_1,...,a_k. A singleton needs no constraint. If k=2, append one new
dummy alias of the same value, making k=3. For k>=3 use

    C(a_1,...,a_k) = sum_i a_i^2 - sum_i a_i*a_(i+1),

with cyclic indices. Then

    2C = sum_i (a_i-a_(i+1))^2.

Consequently C>=0 and C=0 exactly when all aliases have the same value.
Every coefficient is +1 or -1 because a cycle with k>=3 has distinct
unordered edges. The k=2 exception is necessary: the two directed edges
of a two-cycle would collect to the forbidden coefficient -2.

These terms use only aliases; the quadratic terms in the row energies
use only w variables. Therefore their coefficients do not accumulate.

## 5. One common unit path

Collect all unit aliases into u_1,...,u_k. Add dummy unit variables if
necessary so that k>=2. Define

    U = 1 + sum_i u_i^2 - u_1 - u_k
        - sum_(i=1..k-1) u_i*u_(i+1).

The identity

    2U = (u_1-1)^2
         + sum_(i=1..k-1) (u_i-u_(i+1))^2
         + (u_k-1)^2

shows that U>=0 and its zeros force every u_i=1. The two endpoints are
distinct, so the two linear terms do not collect into coefficient -2.
Every nonzero coefficient is +1 or -1, with constant coefficient 1.

Unit aliases occur in no ordinary-variable equality group. Their square
and edge monomials therefore collide with neither those groups nor the
row energies' quadratic monomials.

## 6. The complete polynomial and proof of equivalence

Define

    P = sum_r E_r + sum_(nontrivial alias groups) C_group + U.

All summands are nonnegative over the reals. Hence P=0 forces every
summand to vanish. U=0 fixes the unit aliases to 1. Each C=0 identifies
all copies of its original normalized variable. Each E_r=0 then gives
the corresponding normalized residual A_r=0. The topological monic
definitions of Section 1 recover the original source system R_j=0.

Conversely, given a solution x of the original system, compute the unique
constants and scale coordinates; assign every alias its corresponding
normalized value, every unit alias the value 1, and every w_i the
product m_i. Assign a two-cycle dummy the common value of its class.
Then every row energy, equality cycle, and unit path vanishes, so P=0.

The same substitution works even when x is not a source solution. The
constructor residuals vanish, each converted source residual equals its
old value R_j(x), and each row energy equals that residual squared.
Thus the exact polynomial-map identity P(L(x))=sum_j R_j(x)^2 follows.

Coefficient collisions are impossible: different row energies use
disjoint aliases and w variables; their quartic and cubic supports are
unique; their quadratic supports lie in the w namespace; all remaining
quadratic supports lie in disjoint alias groups; the unit path supplies
the only constant and linear terms. Therefore every nonzero coefficient
of P is +1 or -1. If there is at least one row term, its m_i^2 occurs
uniquely, so the total degree is exactly 4. Every individual variable
has degree at most 2.

All 770 normalized variables occur in the concrete instance, including
all 519 original variables. Choose one alias representative of each
original variable for the reverse coordinate projection. The preceding
argument makes that projection and L inverse on integer zero sets.

## 7. Exact dimensions of the supplied instance

The centered integer source has 519 variables and 321 quadratic rows.
It has 1,748 collected row terms and row coefficient height 324. Its
ordinary sum-of-squares quartic has 6,253 terms and height 411,060.

The normalization introduces 96 binary constants and 155 shared scales.
It yields 770 normalized variables, 572 rows, and L=2,378 signed unit
term occurrences. The occurrence construction uses 3L=7,134 variables;
297 alias classes have size two and each needs a cycle dummy. There
are 1,208 unit aliases, so no extra unit dummy is required. The final
dimension is 7,134+297=7,431.

Of the 770 normalized-variable alias classes, 52 are singletons. They
need no equality constraints. The polynomial's degree distribution is:

| Degree | Nonzero monomials |
| --- | ---: |
| 0 | 1 |
| 1 | 2 |
| 2 | 20,853 |
| 3 | 2,378 |
| 4 | 10,852 |
| Total | 34,086 |

There are 21,934 coefficients +1 and 12,152 coefficients -1. These
numbers are properties of the fully collected explicit polynomial,
not operation counts or upper bounds.

## 8. Finite verification and logical scope

`build.py` emits the complete polynomial and occurrence certificate.
`verify.py` imports no builder. It independently checks:

1. The exact source SHA-256 and the 519 original coordinate bindings.
2. Every topological monic constant/scale definition and all 321 exact
   symbolic source-row pullbacks.
3. Every disjoint occurrence, product coordinate, alias cycle and unit
   path, with all 7,431 coordinates accounted for.
4. The complete sparse polynomial, by separately expanding the displayed
   identity for 2P as a sum of integer squares, then dividing each even
   coefficient by two.
5. The exact height, degree, individual-variable degree, constant,
   dimension, and 34,086 terms; every original, normalized and final
   variable is required to occur.
6. The complete plaintext equation against every sparse JSON term.

Five deterministic signed assignments additionally check the forward
value identity; these are diagnostics, not substitutes for the general
proof. The entire verifier is called on two genuinely corrupted
artifacts (a coefficient sign flip and deletion of the constant term);
both calls must reject at the exact expanded-polynomial check. Both
ordinary Python and optimized Python runs pass; the
verifier uses explicit error conditions rather than assert statements.

The generic theorem is elementary finite algebra formalizable in ZFC.
The Con(ZFC) interpretation of the source remains the ordinary proof in
the immutable Round14 package, via C222/ZF-refutation and ZF/ZFC-refutation
calibration. The package's source proof and its transitive arithmetic
arguments must accompany any claimed end-to-end result. Neither the
finite checks nor this compiler constitute an independent formal-kernel
verification of those inherited number-theoretic arguments.

## Further research

1. Reduce the number of aliases without allowing different monomials to
   collect into coefficients outside {-1,0,1}. The present separation is
   deliberately uniform and gives a transparent proof.
2. Choose an arithmetic presentation that minimizes signed term
   occurrences before cloning. Minimal original-variable count need not
   minimize the eventual height-one dimension.
3. Split the longest normalized residuals to trade a few variables for
   fewer monomials; one present residual has 63 occurrences, so its row
   energy is relatively expensive.
4. Formalize the generic compiler and its occurrence-support invariants
   in Lean. Its elementary proof is independent of the number-theoretic
   proof checker being compiled.
5. Investigate prior literature before making any global novelty claim.
   A targeted web search for height-one quartics and unit coefficient
   Diophantine equations did not locate a direct primary treatment, but
   absence from those searches is not a priority result.
