# Heisenberg submonoids: a paid two-generator certificate and an order obstruction

For any two fixed generators in a finite direct power H^r of the integer
Heisenberg group, membership has an exact certificate with **four positive
witnesses**, `3r+1` equations and **18r+10** arithmetic gates. Its
sum-of-squares polynomial costs **27r+12** gates and has degree at most four.
This certificate handles arbitrary word lengths; it does not unroll a
chosen word. However, every such two-generator membership problem is
decidable. Universality in this substrate therefore requires at least
three generators, regardless of the number of factors.

The two-generator certificate works because every allowable binary
pair-order count is realizable. For three generators, we give an explicit
H^3 false positive, followed by an infinite family of false positives
strictly inside both the pair bounds and the weighted triangle bounds.
Global word realizability remains an essential unpaid relation for a
larger alphabet.

## 1. Primary-source contract and its limitation

[Roman'kov, arXiv:2209.14786](https://arxiv.org/pdf/2209.14786), Sections 2,4
and Theorems 5.1--5.2, compiles a nonnegative Skolem system with `e`
multiplications, `d` additions and `q` variable equalities into
`H^(8e+4d+q+1)` with `14e+7d` generators. Its block-matrix dimension is
`3(8e+4d+q+1)`. The fixed undecidable monoid inherits a fixed Diophantine
polynomial; no numerical universal alphabet or factor count is instantiated.

Equation (18) varies one central coordinate through `c^|nu|`. Since
`c=t13^-1`, positive `nu` loads as `-nu` in one subtraction. Membership
certification remains unpaid.

The signed statement needs care: equation (1) allows integer `nu`,
Theorem 5.1 fixes the monoid from D, but (18) uses `|nu|`. These contracts
cannot jointly hold: `D(z)=z^2` has a solution at1 and none at-1, while
the displayed targets coincide. Section 2.1.2 changes the final Skolem
orientation with the sign. A fixed positive slice avoids this issue;
we do not use the unrestricted signed contract.

The following results are direct arithmetic proofs. They do not
implement that universal construction or rule out improving its
membership certificate.

## 2. Exact collection of a two-letter word

Use matrix coordinates

    H(a,b,c)=[[1,a,c],[0,1,b],[0,0,1]].

Then

    (a,b,c)(d,e,f)=(a+d,b+e,c+f+ae).                              (1)

Fix two generators `g=(a,b,c)` and `h=(d,e,f)` in one factor. In a word,
let `n` count g, `m` count h, and let `k` count ordered pairs of positions
in which a g occurs before an h. The opposite order has `nm-k` pairs.
Every pair of g positions contributes `ab`; every pair of h positions
contributes `de`. Repeated application of (1) therefore gives

    A=an+dm,       B=bn+em,
    C=cn+fm+ab*n(n-1)/2+de*m(m-1)/2+ae*k+db*(nm-k).              (2)

For H^r the same three counts apply in every factor, with the respective
fixed coordinate coefficients. Formula (2) follows directly from
matrix multiplication and does not assume an ordering normal form.

**Realizability lemma.** A triple `(n,m,k)` occurs for a binary word if
and only if `n,m>=0` and `0<=k<=nm`.

Necessity is immediate from counting pairs. For sufficiency, if `n=0`
then `k=0` and the word `h^m` works. Otherwise write `k=qn+s`, with
`0<=s<n`. The upper bound gives `q<=m`. If `q=m`, then `s=0` and
`g^n h^m` works. If `q<m`, use

    h^(m-q-1) g^s h g^(n-s) h^q.                                 (3)

This word has exactly n and m occurrences, and its ordered pair count
is `s(q+1)+(n-s)q=qn+s`. Empty powers are permitted. Thus (2), together
with the single interval constraint, is both necessary and sufficient
for monoid membership. The empty word is included.

## 3. Positive witnesses and exact arithmetic ledger

Supply positive integers `N,M,K,W`, and compute

    n=N-1, m=M-1, k=K-1,
    p=n(n-1), q=m(m-1), t=nm.

Require

    K+W=t+2.                                                     (4)

Positivity implies `n,m,k>=0`, and (4) is exactly `W=nm-k+1>0`.
Conversely every realizable triple has the positive witnesses
`(n+1,m+1,k+1,nm-k+1)`. No zero witness or division is hidden.

For each factor require the following three equations, where the target
coordinates `(A,B,C)` are relation arguments:

    A=an+dm,
    B=bn+em,
    2C=(2c)n+(2f)m+(ab)p+(de)q+(2db)t+2(ae-db)k.                 (5)

The coefficients depend only on the fixed generators and are compiled
signed integer numerals. Target coordinates and intermediate values may be
signed; the four supplied witnesses are strictly positive. Equations
(4)--(5) imply (2) over the integers, so the realizability lemma proves
the full converse. In particular the certificate needs neither a
supplied word nor a bound on its length.

The adjacent source charges every product by a fixed coefficient,
including zero or one coefficients in this generic schedule:

| Component | Multiplications | Additions/subtractions | Equations |
|---|---:|---:|---:|
| Decode n,m,k, form p,q,t, and (4) | 3 | 7 | 1 |
| Each factor's three equations (5) | 10 | 8 | 3 |
| Total graph | 10r+3 | 8r+7 | 3r+1 |

Doubling C uses `C+C`, one addition. The central right side has six
products and five additions. The arithmetic used to form the fixed
generator coefficients is part of compiling the fixed relation; all
runtime multiplication by those numerals is charged in the table.

Squaring and summing `E=3r+1` residuals adds E multiplications and `2E-1`
additions/subtractions. The resulting single polynomial costs

    (13r+4)M+(14r+8)A = 27r+12,

has four positive witnesses, and degree at most four in its relation
arguments and witnesses. This is a literal generic ledger, not a
minimality assertion. Supplying target coordinates through an input
loader incurs that loader's additional cost.

## 4. Why two generators cannot be universal

Let `Delta_i=a_i e_i-d_i b_i` for the two generators' horizontal
coordinates in factor i.

If some Delta_i is nonzero, that factor's two horizontal target
equations uniquely determine the rational values

    n=(A_i e_i-d_i B_i)/Delta_i,
    m=(a_i B_i-A_i b_i)/Delta_i.

Reject if either is not a nonnegative integer. Formula (2) in the same
factor then determines the unique rational k because its coefficient
is Delta_i. Check that k is an integer in `[0,nm]`, and verify (2) in
every factor. This finite procedure decides membership exactly.

If every Delta_i is zero, the two generators commute. For a factor use
the injective coordinates

    ell(a,b,c)=(2a,2b,2c-ab).

One has `ell(g^n)=n ell(g)`. In a product, the difference between the
last coordinate of `ell(gh)` and that of `ell(g)+ell(h)` is `ae-db`.
Thus ell is additive on the subgroup generated by these commuting g,h.
Concatenating these triples over all factors reduces membership to

    n ell(g)+m ell(h)=ell(target),       n,m>=0 integers.           (6)

This fixed two-column linear system is decidable directly. In rank two,
two independent rows determine n,m; check integrality, nonnegativity and
the other rows. In rank zero, accept exactly the zero target. In rank
one, choose a nonzero row `alpha n+beta m=gamma`. The extended Euclidean
algorithm either rejects divisibility by `gcd(alpha,beta)` or gives one
integer solution. All solutions are

    n=n0+(beta/gcd)z,    m=m0-(alpha/gcd)z.

Nonnegativity gives an explicitly computable interval of integer z,
possibly unbounded. Test whether it is nonempty, then check the remaining
rows. If the target is not in the common rational column span those
rows reject every solution; otherwise all solutions of the chosen row
satisfy them. Zero coefficients and the empty word are included.

This proves decidability for every two-generator submonoid of H^r,
uniformly in finite r. No bound on the target coordinates is used.
Three or more generators are necessary for undecidable membership in
this substrate; this statement does not claim that three suffice.

## 5. Pair-count constraints already fail for three generators

For an arbitrary alphabet with occurrence counts n_i, let K_ij count
positions of i before positions of j. Every word satisfies

    K_ii=n_i(n_i-1)/2,
    K_ij+K_ji=n_i n_j,       0<=K_ij<=n_i n_j.                   (7)

Its Heisenberg central coordinate is

    sum_i n_i c_i + sum_(i,j) K_ij a_i b_j.                      (8)

Unlike the binary case, (7) does not guarantee a word realizing the
counts. This becomes an actual monoid-membership false positive in H^3.
Let `u=(1,0,0)`, `v=(0,1,0)`, `1=(0,0,0)` and fix

    A=(u,1,v),       B=(v,u,1),       C=(1,v,u).                  (9)

The three central coordinates measure `K_AB,K_BC,K_CA` respectively.
The target `((1,1,1),(1,1,1),(1,1,1))` forces one occurrence of each
letter by its horizontal coordinates. Its requested central values
require A before B, B before C, and C before A, an impossibility.
Nevertheless all counts in (7) exist and (8) gives exactly that target.
The six possible words exhaust the actual membership question here.

There is a stronger infinite family even if one adds the natural
weighted triangle constraints. Selecting one occurrence of each letter
gives a total of either one or two true indicators among
`[A<B],[B<C],[C<A]`. Summing over all selected triples proves

    n_A n_B n_C <= n_C K_AB+n_A K_BC+n_B K_CA <= 2n_A n_B n_C.   (10)

For any integer m>=3, prescribe

    (n_A,n_B,n_C)=(m,2,2),
    (K_AB,K_BC,K_CA)=(1,1,2m-2).                                (11)

Every directed pair count is strictly between zero and its maximum.
Moreover the middle expression in (10) equals `5m-2`, strictly between
`4m` and `8m`. Yet (11) is impossible:

* `K_AB=1` forces the A/B projection to be `B A B A^(m-1)`.
* `K_BC=1` forces the B/C projection to be `C B C B`.
* Hence the first C precedes all m As, and the second C precedes at least
  the final m-1 As. Thus `K_CA>=2m-1`, contradicting (11).

In fact the exact conditional spectrum is `{2m-1,2m}`. Both possibilities
are realized by

    C B A C B A^(m-1),       C B C A B A^(m-1),

respectively. In the monoid (9), the impossible target is

    ((m,2,1),(2,2,1),(2,m,2m-2)).                               (12)

The horizontal coordinates force precisely the counts used above, so
no longer word can evade this argument. At m=3 there are 127 realizable
central triples, versus 155 passing just the boxes and (10).

This excludes the indicated relaxations, not every possible compact
certificate for word realizability. Given complete counts, realizability
itself can be decided by a finite enumeration of words of that length;
the unbounded existential count search is the membership problem.

## 6. Checks, scope and remaining bridge

The [source](heisenberg_two_generator_membership.py) and
[receipt](heisenberg_two_generator_membership.json) use exact integers
and the Python standard library. Default receipt replay is

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/heisenberg_two_generator_membership.py

The checker exhausts short binary words, constructs every bounded
admissible triple, compares the certificate with direct matrix products,
and audits every literal operation count and arbitrary positive residual
assignment. It implements the decision procedure independently of the
certificate and tests both commuting and noncommuting cases. It also
enumerates every word with counts `(m,2,2)` for m=3 through 10, checking
the strict interior false family and its exact conditional spectrum.

Roman'kov's alphabet has substantially more than two generators once
it represents a nontrivial arithmetic system. Compressing its products
merely to unrestricted pair counts loses soundness. Preserving the
required global ordering either returns to the original Skolem system
or needs an independently paid word-realizability mechanism. This
packet supplies neither a smaller certificate for that full alphabet
nor a new proof of computational universality. The constructive
two-generator certificate and the order obstruction therefore do not
improve the current complete universal Diophantine bound.
