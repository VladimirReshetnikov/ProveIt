# Independent audit of clipping table counts and asymptotic inverses

4 October 2026, UTC. Audited packet: `arity-table-asymptotics-20261004`.

## Verdict

**PASS. No mathematical correction is required.** The closure-table count,
identification with A196460, all fixed-order sector and logarithm expansions,
sharp signed remainders, connected named-color graph interpretation, Laurent
inverse recurrence, sequence-point error proof, and exact threshold inverses
are valid with the source's stated domains and qualifications.

This is a fresh proof review and independently authored exact-arithmetic
audit. It is not a replay of the prior endorsement. Its checks derive the
inverse coefficients from a different, exponentiated equation, then verify
both that equation and the source's logarithmic equation through order eight.
Finite computations corroborate, rather than replace, the all-orders proof.

The assertions are for each fixed truncation order as n tends to infinity.
There is no uniformity in a growing truncation order, convergence of an
infinite inverse series, or exact flooring rule for a truncated real inverse.
There is no new formal verification, physical claim, priority claim, report
number, repository publication, or external submission.

## 1 Exact object and dependency boundary

The incoming packet has the exact supplied pins:

- Manifest SHA-256: `6ae30398c52b6fe1d07a91346791ed3355e7104c55b19a4103de257299293de1`
- PROOF.md SHA-256: `638e524d058deb926919d15b7df2dafc17f7a44dc2688b33e06ee24f476b7c41`
- ZIP SHA-256: `11d45c3cf884e722b72d1032e8879f75070a69ec844efe89a919858b8200d345`

All 20 manifest payloads authenticate. The packet file set is exactly the
20 payloads plus its manifest, and all 21 ZIP members have the same bytes and
file modes as those files. No unmanifested file or duplicate archive member
was accepted. The adjacent receipt is also included in the preservation set.

Both local dependency packets were authenticated independently:

| Packet | Manifest SHA-256 | Payloads | ZIP members |
| --- | --- | ---: | ---: |
| two-witness-tensor-compiler-20261004 | b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82 | 31 | 32 |
| independent-low-arity-audit-20261004 | 6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3 | 20 | 21 |

Their exact file sets and all archived bytes and file modes match too. The
two dependency ZIP hashes are respectively
`897a7bee8ab8f0758b8c3b035b7be0d06d9521a9769919266ab30057a6702c8c`
and `3f8811f2217d292ca3d895712e8e7d17465ac51e328ed94eeee80fbc22cfe1a7`.
The dependency proof and audit pins are:

- ONE_WITNESS.md: `9135dd0e829adb3190e99ed1b62f8d419f9f7540cfd92a1acd1635726fa7172c`
- AUDIT.md: `6bf14006170df1e126fb98d8e06ee97cfb51786f9ce11bcc0a37370a896d5afe`

The complete target proof, README, source boundary, and all five target Python
files were read as inert text. The complete ONE_WITNESS.md and accepted
AUDIT.md were read, with particular attention to the native one-positive-
witness construction and the zero-witness classification. Their unrelated
POWER/Pell composition sections are not mathematical dependencies of the
present asymptotic theorem. The retained dependency payloads, including code
and compressed evidence, were byte-authenticated; this audit does not claim
to reprove every unrelated theorem in that recursive scientific history.

No target or upstream program was run or imported. In particular no source
interpreter, physical or trajectory simulator, saved schedule, Lean file, or
scientific checker was executed. The only new executable files used are the
three fresh checkers and the fresh sealing utility in this dossier, each
fully inspected before its first run. They use the Python standard library.

## 2 Closure and the exact zero versus one classification

Fix K=n+1, positive integer inputs, a fixed Boolean K by K clipping table,
and one integer-coefficient polynomial equality with unrestricted degree.
For a tail cell, fix its non-tail coordinates. The restricted polynomial
then vanishes on a Cartesian product of infinite sets of positive integers.
Induction in the number of remaining variables, applying the finite-root
theorem to the last variable and then to its coefficient polynomials, makes
the restriction identically zero. Hence acceptance of (i,K) forces row i;
acceptance of (K,j) forces column j; acceptance of (K,K) forces everything.
This necessity holds even with arbitrary real coefficients and no SOS
assumption.

Conversely, multiply, over accepted cells, the sums of squared deviations in
their non-tail coordinates. Each factor vanishes exactly on its coordinate
flat. Closure prevents that flat from including a rejected positive input.
Each accepted input makes its own cell's factor vanish. The empty table is
represented by the empty product 1. The full table is represented by 0,
because the all-tail factor is the empty sum 0. This also resolves K=1:
the only two tables both have minimum zero.

For clarity, the imported one-witness upper bound does not need POWER.
For K>=2 let p_K(x)=product_(h=1)^(K-1)(x-h)^2. On positive integers p_K is
zero exactly below K and strictly positive exactly on the tail. For each
accepted cell take the sum of squares fixing its finite coordinates and
add (w-product_(tail coordinates) p_K(X_l))^2; the empty tail product is 1.
The product of these cell factors has a positive zero exactly on the
accepted cells. Positivity of w excludes all below-threshold impostors,
and the clipped cells are disjoint. At K=1 use (w-1)^2 or 1. Thus every
nonclosed table has minimum exactly one, while every closed table has
minimum zero in precisely the stated representation class.

The fresh enumeration constructs the union of all accepted coordinate
flats, rather than testing the source's boundary predicates directly. For
all 66,066 tables with K=1,2,3,4 it obtains closed counts 2,6,48,1194.
Every other table has an explicit missing point of that union. The actual
zero-witness product is evaluated on 44,298 positive input/table assignments
through coordinate K+2, including values beyond the clipping threshold.
These finite checks do not replace the infinite-grid argument.

## 3 Boundary counts and graph models

An accepted corner gives exactly the full table. With the corner rejected,
let R and T be the finite row and column labels whose boundary cells are
accepted. These are marked by boundary data, not by whether an interior row
or column happens to be full. If |R|=r and |T|=c, closure fixes the interior
entries in their union to one and leaves exactly (n-r)(n-c) free entries.
Every such choice is valid and uniquely recoverable. Therefore

    C_n = 1 + sum_(r,c=0)^n binom(n,r)binom(n,c)2^((n-r)(n-c)).

Putting j=n-r and applying the binomial theorem in c gives exactly the
single sum in A196460. There is no lost or duplicated rejected-corner
all-interior-one table: its different boundary markings are different
tables. The fresh enumeration verifies every individual (r,c) count, not
just the totals, for n=0,1,2,3.

Put an edge at each rejected interior entry. Accepted boundary labels then
mark isolated vertices of a graph on two distinguished labeled parts of
size n. Conversely a graph and any subset of its isolated vertices recover
the table. Consequently a_n=sum_G 2^i(G), and division by 2^(n^2) is the
expectation in the uniform labeled bipartite graph model. Exhaustive
enumeration of all 66,067 graphs for n=0 through 4 verifies both the weighted
totals and the entire isolated-vertex histogram.

The first-order sentence cited in the source is interpreted correctly:
the truth sets of U and U_1 choose active row and column copies; B can be
false only at a pair whose two copies are active. Nonisolated vertices
must be active, whereas each isolated vertex can independently be active
or inactive. Although the relational language uses one domain, the left
and right graph parts are two distinguished copies of it. In particular
the atom B(x,x) corresponds to an ordinary edge between copies, not a loop
in the bipartite graph. This distinction preserves all n^2 choices.

## 4 Exact sectors and the uniform fixed order error

The normalized summand is binom(n,r)binom(n,c)2^(-n(r+c)+rc). Regrouping by
k=r+c yields a finite exact identity with

    P_k(x)=sum_(r=0)^k binom(x,r)binom(x,k-r)2^(r(k-r)).

At nonnegative integer n, falling-factorial binomials vanish for r>n,
so P_k(n)=0 for k>2n. Each P_k has degree k with strictly positive leading
coefficient alpha_k. Thus the finite regrouping is exact but by itself
would not control a tail whose number of sectors grows with n.

The source supplies the needed uniform-in-n estimate. Since rc<=k^2/4,
Vandermonde gives

    0 <= P_k(n)2^(-nk) <= binom(2n,k)2^(-nk+k^2/4)=B_(n,k).

For 0<=k<n the exact quotient of successive B terms is

    ((2n-k)/(k+1))2^(-n+k/2+1/4)
       <= 2n 2^(-n/2+1/4)=rho_n.

The deliberately loose bound is valid at the endpoints too. For every
fixed M and all sufficiently large n>=M+1, rho_n<1 and the portion
M+1<=k<=n is bounded by a geometric series starting at B_(n,M+1).
For n<k<=2n, the exponent -nk+k^2/4 is decreasing, so every exponent is
at most -3n^2/4. The binomial sum there is at most 2^(2n).

For example, a concrete consequence for n>=max(M+1,16) is

    tail after M <=
      [2(2n)^(M+1)/(M+1)!]2^(-(M+1)n+(M+1)^2/4)
      + 2^(2n-3n^2/4).

Here rho_16<1/2 and rho_n decreases thereafter. This proves the claimed
O_M(n^(M+1)2^(-(M+1)n)) without assuming independence of isolation events.
The large-k part is superexponentially smaller for fixed M. Applying the
proved estimate at M+1 and using P_(M+1)(n)~alpha_(M+1)n^(M+1) proves the
positive sharp remainder equivalent. It is important that M is fixed.

For a specified set of r left and k-r right vertices, isolation prohibits
nk-r(k-r) distinct edges. Summing the exact probability therefore gives
E[binom(i(G),k)]=P_k(n)2^(-nk). The checker confirms every factorial moment
for the exhaustively enumerated bipartite graphs. It also verifies the
single sum, double sum, and complete regrouping at all 65 indices n=0..64,
585 coefficient values, and 4,225 exact majorant inequalities. Those
inequalities are raised to the fourth power so every comparison is between
rationals; no numerical fourth root is used.

The fraction of zero-auxiliary tables divides by 2^((n+1)^2), yielding
2^(-2n-1)(a_n/2^(n^2)+2^(-n^2)) exactly. The isolated extra full table is
beyond every fixed exponential sector as n tends to infinity. The
complement has minimum one by Section 2, including the empty complement
when K=1. The leading fraction is consequently (1/2)4^(-n).

## 5 Logarithms and connected named color graphs

Formal differentiation of log(1+sum P_k z^k) gives the source recurrence
for L_k. Its coefficients lie in Q[x], with degree at most k. For fixed M,
the already proved u=a_n/2^(n^2)-1=O(n2^(-n)) tends to zero. The logarithm
has bounded derivative near 1, so the forward tail retains its order under
the logarithm. Taylor truncation at degree M has error O(u^(M+1)). In the
finite retained products, a term of total z-degree r has x-degree at most
r; every r>=M+1 term is bounded by the claimed error because n2^(-n)->0.
This supplies the full analytic justification of the logarithmic expansion,
not merely a formal identity.

The number b_k=k!alpha_k counts a graph on k labeled vertices together
with a proper coloring by two named colors. It is not the balanced
n-plus-n vertex graph count a_n. Component decomposition preserves the
coloring and labels, so the exponential formula gives top coefficient
[x^k]L_k=c_k/k!, where c_k counts connected colored graphs. The rooted
component recurrence in the source is correct; choosing the component of
label 1 gives its binomial factor. Every nonempty connected bipartite
graph has exactly two named proper colorings, including the singleton.
Stars prove c_k>0 for all k.

The independent checker obtains L by the alternating logarithm series
instead of the recurrence, and then checks that recurrence. It derives
the leading identities through k=8, obtaining

    b_0,...,b_8 = 1,2,6,26,162,1442,18306,330626,8488962,
    c_1,...,c_8 = 2,2,6,38,390,6062,134526,4172198.

To test the combinatorial meaning independently, it enumerates all 33,868
ordinary simple labeled graphs on 0..6 vertices, tests bipartiteness by
color propagation, and weights each valid graph by two per connected
component. This reproduces b_k and c_k through six without using the
component recurrence to classify the enumerated graphs.

## 6 Laurent inversion and leading coefficient

Write lambda=ln 2 and t=2^(-s), formally treating s and t as independent.
Substitute n=s+delta into the finite normal-form equation. In coefficient
t^m the new D_m appears only in 2s delta: the delta square has no constant
term, and every logarithmic term already carries at least one t. Division
by 2s therefore proves both existence and uniqueness in the Laurent ring
specified by the source. No division by a polynomial with uncertain roots
or by an asymptotically vanishing numerical derivative is used formally.

Assume D_j has largest s exponent at most j-1. In a term involving a
product of p prior D factors whose indices sum to m-k, that product has
largest exponent at most m-k-p. Derivatives of L_k only lower its degree
from k, and the exponential supplies lambda powers but no s degree.
Consequently the pre-division exponent is at most m, with equality only
for the direct L_m(s). The delta-square contribution has exponent at most
m-2. After dividing by s this proves the degree bound and

    D_m(s) ~ -c_m s^(m-1)/(2 lambda m!).

Negative powers of s cause no difficulty for s>=1, which is the asymptotic
region. There is no claim that these Laurent formulas can be evaluated at
s=0. The source's three displayed D coefficients agree exactly with the
independently reconstructed coefficients.

For additional independence, this audit constructs D from

    sum_(k>=0) P_k(s+delta)t^k
       exp(lambda((2s-k)delta+delta^2)) = 1,

the exponentiated forward equation, whose new linear coefficient is
2 lambda s. After each new coefficient is solved, the checker verifies
identical cancellation in both this equation and the logarithmic equation.
Both residuals vanish through order eight. It checks the leading
coefficient and largest Laurent exponent at every order. A separate
data-only comparison verifies every retained P,L,D coefficient through
six against the target evidence, after converting h=1/lambda, and all 33
retained sequence values.

## 7 Rigorous sequence point error and its sign

The formal inverse is converted to an actual sequence-point statement by
the finite function H_M(x)=x^2+lambda^(-1)sum_(k=1)^M L_k(x)2^(-kx).
This step is legitimate: H_M is explicitly defined and smooth; it is not
an assumed interpolation of a_n. At the actual integer n, the forward
logarithm estimate supplies

    H_M(n)-s_n^2=O_M(n^(M+1)2^(-(M+1)n)).

It also gives s_n-n=O(2^(-n)), hence n~s_n and 2^(-n)/t_n->1. The finite
inverse approximation has displacement delta_M=O(t_n), since each fixed
D_j(s)t^j is O(t(st)^(j-1)). Both n and the approximation lie within one
of s_n for sufficiently large n.

The claimed residual estimate at that approximation can be made explicit
as follows. Expand the finite polynomials exactly and each exponential
through enough powers of delta_M to retain all t-degrees through M.
Every finite residual coefficient of degree r has largest s exponent at
most r. The coefficients through M vanish. Every remaining finite term
s^r t^r with r>=M+1 is O(s^(M+1)t^(M+1)), because st->0. In a term with
prefactor t^k and polynomial degree at most k, the exponential remainder
after degree M-k is O(delta_M^(M-k+1)); multiplication bounds it by
O(s^k t^(M+1)), which is no larger than the claimed residual error.
The finite delta-square and polynomial-substitution terms obey the same
bound. This verifies the source's Taylor justification in detail.

Uniformly on [s_n-1,s_n+1], H'_M(x)=2x+O_M(x^M2^(-x))>=s_n eventually.
Subtracting the two residual estimates and applying the mean-value
theorem thus divides by a quantity at least s_n and yields exactly

    n - [s_n+sum_(k=1)^M D_k(s_n)t_n^k]
          =O_M(s_n^M t_n^(M+1)).

There is no unjustified differentiation of an infinite series. Applying
this already proved result one order further isolates D_(M+1)t^(M+1).
Its negative, nonzero leading coefficient dominates the next error because
st->0. Hence the sharp negative remainder is proved, and every fixed
inverse truncation eventually overestimates n. This is an eventual claim,
not a uniform sign statement for every small n and every order.

Replacing a_n by C_n=a_n+1 changes log_2 by O(2^(-n^2)) and s by
O(2^(-n^2)/n). The same proof and the same coefficients therefore apply;
these changes are smaller than every fixed error sector.

As independent finite corroboration, `check_enclosures.py` constructs
rigorous rational enclosures for s, t, and each inverse error, using no
floating-point assertions. It uses the positive atanh series with a
geometric tail for logarithms, integer square roots for square roots,
alternating Taylor bounds for exp(-x), and outward 1024-bit dyadic rounding
after arithmetic. All 36 cases n=16,32,64, M=1..6, for both a and C have
a strictly negative upper bound for the remainder. Exact rational
endpoints are retained. Ratios to the claimed sharp leading term move
toward one as expected; for example the a-sequence M=6 ratios are enclosed
by [0.532599538158,0.532599538159],
[0.741284482732,0.741284482733], and
[0.864003938458,0.864003938459]. These finite facts are not used to prove
the eventual sign or the all-orders equivalence.

## 8 Exact inverse thresholds and the small endpoints

The lower bound a_n>=2^(n^2) is a single summand. Bounding every exponent
by n^2 and summing binomial factors gives a_n<=2^(n^2+2n), strictly below
2^((n+1)^2). Thus floor(sqrt(log_2 a_n))=n for every n>=0, including
a_0=1. Strict increase follows, for instance, because the old j<=n terms
in the single sum for a_(n+1) each are at least twice their counterparts,
and there is one additional positive term.

For real y>=1 let m=floor(sqrt(log_2 y)). If n<m then
a_n<2^((n+1)^2)<=2^(m^2)<=y. If n>m then
a_n>=2^(n^2)>=2^((m+1)^2)>y. Only the comparison with a_m is undecided,
so the source's exact maximum-index formula follows. At m=0 the branch
m-1 cannot occur because y>=1=a_0. Below 1 the defining set is empty.

For C_n and n>=1, adding one still leaves the upper bound strictly below
2^((n+1)^2), since 2^(n^2+2n)+1<2^(n^2+2n+1). At n=0, however,
C_0=2 is exactly 2^(1^2), so its floor is 1, not 0. For y>=2 we have
m>=1 and C_(m-1)<=2^(m^2)<=y; equality is possible at m=1. Indices
above m still fail, and comparison with C_m gives the same two-branch
formula. In particular N_C(2)=0, not 1. Below 2 the set is empty.

The forward square-root expansion of the logarithm gives the stated
boundary shift. Its first correction is q/lambda. Its q^2 coefficient
is (m-1)/(2lambda)-1/(2lambda^2 m): the first part comes from L_2/(2m
lambda), and the second from the quadratic Taylor term of the square
root applied to L_1. The stated O(m^2q^3) is valid for m tending to
infinity and does not purport to evaluate the singular-looking formula
at m=0. An approximate threshold only classifies a point whose distance
from the boundary exceeds the error bound; exact comparison is needed
inside that uncertainty interval.

The checker tests 1,012 rational thresholds against direct maximum-index
enumeration for both sequences. Probes include half-integers on both
sides of every tested a_n, C_n, and perfect-square logarithmic boundary,
plus 0,1,3/2,2,5/2. It computes the floor using integer bit lengths,
exact rational comparison, and integer square root, with no floating log
that could round an endpoint incorrectly.

## 9 Public attribution and limits of retrieval

The [primary OEIS entry](https://oeis.org/A196460) was independently
retrieved on 4 October 2026. It gives the identical single sum, offset
zero, and displayed initial values. It credits Paul D. Hanna on
2 October 2011 and the leading asymptotic to Vaclav Kotesovec on
25 June 2013. Its displayed links do not provide a proof of that leading
equivalence. No Mathematica or PARI program on the page was run.

The [versioned arXiv record](https://arxiv.org/abs/2302.04606v1) verifies
the 2023 authorship and version. Extracted text of the
[versioned PDF](https://arxiv.org/pdf/2302.04606v1), printed page 32,
Table 3 in Appendix A.1, places the specified two-unary/one-binary sentence
beside A196460. The active-subset graph interpretation in Section 3 is
an independently checked mathematical reading of that formula. A fresh
PDF screenshot attempt failed, so this citation was checked from the
extracted text, not a visual inspection. No local raw-PDF byte pin or
independent authentication of arXiv's remote file history is claimed.

The source's bounded overlap-search disclosure is appropriately narrow.
This audit did not repeat or expand it into a comprehensive literature
search. An empty bounded search cannot prove originality. No absence of
prior all-orders treatment is asserted here. Both the ordinary and
exponential generating functions must be interpreted formally: the
lower bound a_n>=2^(n^2) makes both analytic radii of convergence zero.

## 10 Preservation and historical changes

The fresh audit preservation boundary comprises 87 filesystem objects:
all three packet directories, their descendants, their three adjacent
ZIPs, and the target's adjacent receipt. The initial snapshot was captured
at 2026-10-04T15:23:38.280628+00:00, after initial inert-text reading and
before new algebra/enumeration execution. The final snapshot and sealing
receipt establish equality of bytes/hashes, object sets, sizes, modes,
nanosecond mtimes, and directory metadata over that explicit interval.
Access times are excluded because reads can update them. Neither initial
reads nor the audit wrote, chmodded, retimestamped, or restored any input.

The source's authentic historical snapshots were recomputed as data,
not accepted merely because a log said PASS. The 249-entry before and
376-entry current inventories have exactly 132 differences: 44 in the
Report69 tree and 88 in the Report70 tree. The recomputed dictionary
matches the retained change file exactly. The 62 core entries outside
those release trees are identical in the historical before, historical
current, source's final core snapshot, and this audit's current snapshot.

All six historical preservation files are retained byte-for-byte under
`original-history/`; the source originals remain untouched. The audit does
not overwrite the original history with a cleaner snapshot. It does not
claim whole-interval preservation of Reports69/70 or infer that any
particular actor made the historical changes. Their active release trees
are outside this audit's fresh equality boundary. The only inputs relevant
to the asymptotic mathematics are preserved without that qualification.

## 11 Evidence inventory and reproducibility

The successful fresh runs are recorded in `evidence/mathematics.json`,
`evidence/mathematics.log`, `evidence/enclosures.json`, and
`evidence/enclosures.log`. They establish:

- 66,066 Boolean table classifications and 44,298 zero-polynomial checks
- 66,067 bipartite graphs with every isolation factorial moment checked
- 33,868 ordinary graphs independently testing colored connected counts
- 65 sequence indices, 585 P-polynomial values, and 4,225 exact majorants
- 1,012 exact rational inverse-threshold comparisons
- Formal exponentiated and logarithmic inverse cancellation through order 8
- All displayed P,L,D coefficients and all three leading identities
- 21 retained coefficient families and 33 retained sequence entries matched
- 36 rigorous signed sequence-point inverse remainder enclosures

The algebra checker reads no source file or coefficient fixture. A portable
replay can put that single checker in a new directory with an `evidence`
subdirectory and run it with Python 3.10 or newer; it refuses to overwrite
the JSON result. The enclosure checker additionally reads the newly produced
mathematics JSON and the specifically named source JSON as inert data. Its
source path is deliberately local, as is the preservation checker; these
are not presented as source-free portable interfaces.

No new source-free replay was performed merely to produce duplicate evidence.
Every claimed result here corresponds to a completed successful fresh run.
The final manifest, read-only permissions, archive-member check and adjacent
receipt make this a separately sealed, hash-pinned dossier. File mode 0444
is a read-only delivery convention, not a claim of operating-system WORM
storage or an unforgeable external timestamp.
