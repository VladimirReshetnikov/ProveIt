# Independent audit of the finite Newton–Puiseux architecture

This audit aligns with the parent proof plan and reads the current
`algebraic_notes.md` and `analytic_notes.md`. It is an argument audit,
not a Lean build.

## 1. Recommended precise conventions

Let the translated input be P(X,Y), with Y-degree d>=1 and leading
coefficient a_d(X). In K(X)[Y], write

    P/a_d = product_m Q_m^m,

where the nonconstant Q_m are monic, squarefree, pairwise coprime, and have
degrees n_m, with sum_m m*n_m=d.

Choose one nonzero polynomial C divisible by all denominators of the
coefficients of all Q_m, and set

    F_m(X,Z)=C(X)^(n_m) Q_m(X,Z/C(X)),
    F=product_m F_m,    D=sum_m n_m<=d.

Each F_m is monic and polynomial in X,Z. F is squarefree in K(X)[Z].
Its discriminant is a nonzero polynomial in X. Put

    delta = ord_X Disc_Z(F),
    N=(d!)^d,    Delta=N*delta,
    h=Delta+1,    M=2h+1,
    B=d*N*(delta+1),    J=M+d^2*B.

For clarity, “jet modulo T^k” means coefficients indexed 0,...,k-1.
“Prefix through degree h” means coefficients indexed 0,...,h.
Do not alternate these conventions without explicitly adding/subtracting 1.

Run Newton–Hensel separately on each F_m, keeping the label m on its leaves,
but use the one global discriminant budget delta and ramification N.
Equivalently a combined run is possible, but then labeling leaves requires
an extra finite argument. Separate runs avoid it.

## 2. All relevant bounds are finite and primitive recursive

At a node of degree n<=d and cumulative ramification e, maintain

    ord Disc(node) <= e*delta,    e divides N,    e<=d!.

Do not repeatedly replace the exact node budget by N*delta and then
multiply that coarse budget by q: the maintained bound e*delta is what
justifies refreshing the same global bound after each step.

Tschirnhausen centering forces the Y^(n-1) coefficient to zero.
The discriminant bound supplies a nonzero lower coefficient at an index
<=e*delta. To find the MINIMUM valuation/(n-i), all coefficients must be
scanned through n*e*delta, not merely e*delta. The common B is sufficient.

For a slope p/q in lowest terms, p<=B and q<=n. A Newton transform through
output precision k needs input precision at most k+p*n<=k+d*B.
Ramification never increases this coarse bound; its exact index relation is

    q*r + p*i - p*n = k,
    r = (k+p*(n-i))/q <= k+p*n.

Centering and Hensel coefficient lifting through k require only input
coefficients through k. There are at most d-1 nonterminal levels. The
reserve d^2*B therefore covers every transform and every later slope scan.

Use finite arrays of length at most J+1, a bounded stack or d rounds of
splitting, and no more than 2d-1 total nodes. Hensel corrections are bounded
loops over coefficient order, node degree, and factor count. Rational and
algebraic arithmetic routines are the one fixed backend implementation.

This gives an ordinary uniform PR algorithm. It does not evaluate a code
for an arbitrary PR function. It does not recursively evaluate an
unevaluated “series function” at ever larger precision.

## 3. The packet is computed once

The finite Newton–Hensel stage only needs M=2h+1 digits, with input
lookahead J. It yields b_{m,j}(T), modulo T^M, satisfying

    F_m(T^N,Z) = product_j (Z-b_{m,j}(T)) modulo T^M,

coefficientwise in Z. The list of all b's has D entries.

All future coefficients are generated from FINITE simple polynomial
equations derived below. This substantially simplifies the PR proof:
the Newton tree is not rerun separately for every later precision.

Finite splitting can be ordered deterministically by canonical algebraic
codes/isolating data. The algorithm must not use requested final precision
to alter any earlier ordering. Exact prefixes and Hensel correction
recurrences then ensure coherence.

## 4. Discriminant congruence gives explicit finite separations

The discriminant is a polynomial in the coefficient list, hence it
respects congruence modulo T^M. Therefore

    Disc F(T^N) = product_{i<j}(b_i-b_j)^2 modulo T^M.

The left side has valuation Delta<M. If any difference had no nonzero
coefficient through Delta, the product would vanish through Delta,
contradiction. Thus every pair has a bounded, computable first differing
index w_{ij}<=Delta. Since the coefficient field has no zero divisors,
the first nonzero coefficient in the product is the product of the
first nonzero coefficients, and

    2*sum_{i<j} w_{ij}=Delta.

This proof concerns finite coefficient arrays. It does not decide
equality of arbitrary infinite series.

For a root with label m, the derivative product identity gives

    ord F_{m,Z}(T^N,b_{m,j}) =
         sum_{k!=j, same m} w_{jk} <= Delta.

It is enough to use <=Delta; the sharper <=Delta/2 is unnecessary.

## 5. Finite desingularization

Let

    a_i(T)=sum_{k=0}^h [T^k]b_i(T)*T^k.

Then b_i-a_i is divisible by T^(h+1). Set

    s_i=ord F_{m,Z}(T^N,a_i).

This is a bounded scan through Delta, and s_i<=Delta<h, since replacing
b_i by a_i changes the derivative only in degree at least h+1.

Write b_i=a_i+T^(h+1)v. Taylor expansion, with Hasse derivative
coefficients (so no unnecessary factorial denominators), gives

    F_m(T^N,b_i)
      = F_m(T^N,a_i)
        +T^(h+1)v F_{m,Z}(T^N,a_i)
        +terms divisible by T^(2h+2).

The first expression vanishes modulo T^M, M=2h+1. Since h+s_i+1<=2h<M,
this proves

    T^(h+s_i+1) divides F_m(T^N,a_i).

Now define the FINITE polynomial

    H_i(T,U)=T^(-(h+s_i)) F_m(T^N,a_i(T)+T^h U).

The constant-in-U term is divisible by T. The coefficient of U has
constant coefficient [T^s_i]F_{m,Z}(T^N,a_i), which is nonzero.
Every coefficient of U^r, r>=2, is divisible by T^(h-s_i), hence by T.
Consequently

    H_i(0,0)=0,
    H_{i,U}(0,0) != 0.

No implicit-function theorem is used at this step. The defining equality
is a finite polynomial identity and can be checked exactly.

## 6. Simple recurrence and final factorization

Use the analytic agent's normalization

    Phi_i(T,U)=U-H_{i,U}(0,0)^(-1)H_i(T,U).

Its (0,0) and (0,1) coefficients vanish. Define u_{i,0}=0 and

    u_{i,k}=[T^k]Phi_i(T,sum_{ell<k}u_{i,ell}T^ell).

This is one fixed primitive recursion on k. At any finite cutoff the
recurrence establishes H_i(T,U_i)=0 through that cutoff. The root

    z_i(T)=a_i(T)+T^h U_i(T)

agrees with a_i through degree h and is an exact formal root of F_m(T^N,Z).
It therefore retains every first-difference witness w_{ij}<=Delta.

Synthetic division first factors out one Y-z_i. For every later root,
evaluation of that factorization gives a product of already extracted
differences times the remaining polynomial value. Each difference has a
certified leading nonzero coefficient, so multiplication by it is
injective coefficientwise. This proves that all D distinct roots factor F,
and that the n_m roots with label m factor F_m. No zero-product
disjunction for undecidable series equality is invoked.

At the FINITE object-theory level cancellation by a factor of order w
loses w digits. To establish factorization through precision L, use
simple-root residual identities through L+Delta (or a slightly larger
fixed reserve). The sum of all relevant first-difference orders is
<=Delta, so this reserve is sufficient. The final displayed L-jet itself
still only needs coefficients through L.

## 7. Returning to the original polynomial

Let v=ord C and

    E(T)=T^(-N*v) C(T^N),  so E(0)!=0.

Define W_i(T)=z_i(T)/E(T) by the reciprocal-unit coefficient recurrence.
Then the original Laurent root is

    y_i(T)=T^(-N*v) W_i(T),

repeated m times according to its label. The finite nonnegative-exponent
identity to verify is

    T^(d*N*v) P(T^N,T^(-N*v)Z)
       = a_d(T^N) product_i (Z-W_i(T))^(label_i).

On the left, the coefficient of Z^r is exactly

    T^((d-r)*N*v) a_r(T^N),

so no negative powers remain. This formula is a particularly clean
`factorJet` specification for the Lean endpoint.

## 8. Explicit convergence data to include in the packet

For each simple H_i choose rational beta_{pq} bounding its normalized
Phi coefficients, S_i>=max(1,sum (q+1)*beta_{pq}), and set

    r_i=1/(4*S_i),   rho_i=1/(16*S_i^2).

For every cutoff L the proved finite inequality is

    sum_{k=1}^L |u_{i,k}| rho_i^k <= r_i.

The proof is the finite Picard-majorant argument in analytic_notes.md.
It supplies a tail r_i*2^(-(L+1)) on |T|<=rho_i/2.

For the reciprocal E(T)^(-1), either apply the same simple polynomial
lemma to E(T)V-1 at V=E(0)^(-1), or give the direct rational majorant:
choose R_C<=1 with sum_{k>=1}|E_k/E_0|R_C^k<=1/2.
The finite weighted coefficient norm of the reciprocal is then <=2/|E_0|.

Take one positive rational R<=min(rho_i,R_C,1), and rational M_i bounding
the R-weighted coefficient norm of W_i. Finite convolutions prove

    sum_{k=0}^L |[T^k]W_i| R^k <= M_i

for every L. For eta<=|T|<=R/2 the Laurent tail after L satisfies

    |tail| <= eta^(-N*v)*M_i*2^(-(L+1)).

This is the precise numerical convergence claim the first-order theorem
represents. For evaluation at a Cauchy complex argument, eta is supplied
positive apartness, and a fixed PR coefficient/argument name supplies
rational approximations. No arbitrary Cauchy sequence is quantified over
inside first-order iPRA.

## 9. Remaining material dependencies

The architecture is coherent under a proved PR exact-algebraic backend.
That backend remains the separate substantive obligation already assigned
to the other agent. Do not claim that the FTA draft by itself supplies it.

The Lean file remains an outline. Completion needs actual PR syntax,
checker semantics, and an object derivation assembled using PRA.qfInd.
Do not replace that obligation by a theorem about mathlib Complex.

