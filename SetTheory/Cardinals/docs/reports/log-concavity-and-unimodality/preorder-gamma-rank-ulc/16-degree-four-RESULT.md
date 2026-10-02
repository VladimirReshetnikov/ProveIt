# Actual gamma degree four: exact bounded checks and pendant-family certificate

This directory addresses the ordered **disjoint same-ground-set** support coefficients
`gamma_k = #{(A,B): A∩B=∅, |A|=|B|=k, a directed perfect matching A→B exists}`.
Each support is counted once, regardless of its number of matchings. Reflexive loops
cannot occur in such a matching. All calculations here use integer arithmetic.

The degree-four ULC gaps are

- `3 gamma_1^2 - 8 gamma_2`
- `4 gamma_2^2 - 9 gamma_1 gamma_3`
- `3 gamma_3^2 - 8 gamma_2 gamma_4`

## Complete eight-element scan

`exhaust8.cpp` enumerates every naturally labeled quotient poset on m=1,...,8,
and every positive composition of 8 into m equivalence-class sizes. Every
preorder is represented because every finite quotient poset has a linear extension.
The enumeration intentionally includes isomorphic repetitions.

The naturally labeled quotient counts are
`1, 2, 7, 40, 357, 4824, 96428, 2800472`.

Across **3,590,829 cases**, **2,293,631 have actual gamma degree four**.
Every one satisfies all three inequalities. Minimum gaps are zero, with equality
at four disjoint two-element equivalence classes:
`gamma=(1,8,24,32,16)`, or `(1+2z)^4`.

Degree equals the undirected comparability-graph matching number: orient every
matching edge in an available relation direction; its two endpoint sets are disjoint.
Conversely a feasible support supplies such an ordinary matching.
Thus the perfect-matching prefilter at n=8 is exact.

`exhaust8.log` is the full run output. `verify_supports.py` independently reconstructs
logged supports by enumerating ordinary matchings and deduplicating endpoint pairs,
and checks a second implementation using endpoint combinations and permutations.
The final audit passed 178 logged witnesses and 200 deterministic random preorders.

## Complete nine- and ten-element scans

Exact canonical quotient enumeration makes the larger bounds inexpensive.
`exhaust9_canonical.cpp` checked 399,754 weighted quotient cases, of which 384,395
have actual degree four. `exhaust10_canonical.cpp` checked 5,049,656 weighted
quotient cases, of which 686,481 have actual degree four. **No ULC failure occurs.**
The quotient counts through sizes 9 and 10 are respectively 183,231 and 2,567,284.

Consequently **every preorder on at most ten elements of actual gamma degree four
is ULC**, and any counterexample has at least eleven elements. Smaller preorders
are included by adjoining isolated elements, which preserve every coefficient.

The generator constructs every poset by adjoining a maximal element to a poset
of one fewer element, trying every order ideal as its predecessor set. It merges
only keys that encode literally equal adjacency matrices after a permutation.
Therefore every such merge is between isomorphic posets. Canonical keys use
in/out color refinement followed by exhaustive permutations within color classes;
only exact equal-open-row/column twins are suppressed. `audit_canonical.cpp` additionally checked
key invariance on 50,000 deterministic random relabelings of sizes 1 through 10.

At n=10 the graph prefilter rejects a perfect matching (degree five), and requires
an eight-vertex induced subgraph with a perfect matching (degree at least four).
It therefore retains exactly actual degree four.

## Infinite pendant-clone family

Let K be any preorder with at most eight elements. Let v be a singleton source
(no distinct element points to v), or dually a singleton sink. Suppose K−v has
actual gamma degree three. Attach M new independent sink leaves to a source v,
or M independent source leaves to a sink v. Each new leaf is adjacent only to v.
This remains a preorder: source/sink extremality excludes additional transitive
relations. The resulting comparability graph has matching number at most four,
and at least four for every integer M≥1.

Writing `a_k=gamma_k(K)` and `b_k=gamma_k(K−v)`, the exact identity is

`gamma_k(K_M)=a_k+M b_{k−1}`.

Indeed at most one new leaf can belong to a matching support, and if present its
only possible partner is v. Deleting that forced pair leaves exactly a support in
K−v. For each such support there are M choices of the new leaf.

Each degree-four ULC gap is therefore a quadratic `C+B M+A M^2`.
`pendant8.cpp` exhaustively visits all eight-element cores and eligible source/sink
vertices (smaller cores are included by adjoining isolated elements). It certifies
all **17,044,008 core/vertex cases**, including isomorphic repetitions, using
`A≥0`, `C≥0`, and either `B≥0` or `B^2≤4AC`.
The latter condition certifies nonnegativity for every real M≥0 of the interpolated
coefficient polynomial; actual finite preorders correspond only to integer M.

There are 12,660,508 negative linear coefficients across these quadratics, but
**zero negative quadratics on the nonnegative real axis**. This is a finite exact
certificate for the stated infinite family, not a proof for all rank-four preorders.
`verify_pendant.py` independently checks all logged coefficient witnesses at
M=1,2,3 by direct matching-support enumeration, including transitivity and absence
of higher coefficients.

The all-population pendant calculation was subsequently extended to every core
of size at most nine using `pendant9_canonical.cpp`: 487,632 eligible marked-core
cases, 317,586 negative linear coefficients, and zero quadratics negative on the
nonnegative real axis. The source/sink condition and deletion degree are unchanged.

### Full marked-core bound ten and the GE a=1 branch

`pendant10_canonical.cpp` completes the calculation for **every core of size at
most ten**. It first computes exact undirected matching numbers by subset dynamic
programming, retaining source/sink vertices v precisely when `nu(K−v)=3`.

Results: 5,049,656 weighted core cases; **1,231,416 admissible marked-core cases**;
727,924 negative linear coefficients; **zero failed nonnegative-axis quadratic
certificates**. There are 412,622 distinct coefficient pairs `(gamma(K),gamma(K−v))`,
exported as `pendant10_coefficients.csv`.

`verify_pendant_certificate.py` is a separate, standard-library-only verifier. It
reconstructs the three gap polynomials by polynomial multiplication rather than
using the enumeration program's hard-coded quadratic formulas. It verified all
**1,237,866 quadratic instances**, including 180,706 with negative linear term.
The minimum `4AC−B²` among those negative-linear quadratics is zero. The exact
integer certificate passes. `verify_pendant.py` also checks the logged extremal
relations and M=1,2,3 expansions by direct matching-support enumeration.

Under the previously established Gallai–Edmonds core reduction for matching rank
four, the a=1 branch has a core of at most ten vertices and all exterior nonisolated
vertices are pendant clones on the sole attachment vertex. Transitivity forces a
uniform orientation and forces that attachment vertex to be a singleton source
or sink. Thus this finite certificate **settles the full a=1 branch**. Cases with
no exterior leaves are already in the complete finite bound; cases with deletion
rank below three fall under the previously proved degree-at-most-three theorem.

The a=0 branch also reduces to components of at most nine vertices, covered by the
finite degree-four test together with the established lower-degree result and ULC
closure under products of independent-component polynomials. The a=2 sector was subsequently settled by the independent certificates described below; the remaining general rank-four sectors are a=3 and a=4. The GE reduction and product-closure facts
are external inputs here; this directory supplies the finite and quadratic
certificates rather than reproving those inputs.

## Complete a=2 sector

The full two-attachment branch is now proved and independently audited. See
`two-attachment/README.md` for its exact support kernel, coverage argument, and
certificate schema. Every core of at most eight vertices with deletion matching
rank at most two, every legal exterior orientation/type, and every nonnegative
integer population are covered.

The producer found 89,863 distinct gamma polynomials. Its standalone verifier
checked all 179,726 remaining-gap instances. Separate independent audits regenerated
the entire support-polynomial set using Hall tests and checked every exact positivity
identity and all population faces without importing the producer or its verifier.
The positivity audit includes 29,215 normalized SOS targets, 334 general-square
targets, and 39,959 face aliases. Every rational weight is strictly positive.

Independent coverage/kernel files are in the sibling
`preorder-gamma-degree4-independent-audit/two-attachment/`; independent positivity
files are in `audit-positivity-independent/` within this directory.

The theorem status is therefore: a=0, a=1 and a=2 proved under the established GE
reduction; a=3 was subsequently settled; only a=4 remains under investigation. This is not yet a proof of the
full actual-degree-four conjecture.

## Complete a=3 sector

The three-attachment branch is now fully proved and separately independently
audited. Exact enumeration reduced 90,042 legal specifications on all six-element
cores to 6,213 canonical nonbipartite templates and 3,437 distinct gamma polynomials.
Every support coefficient and the complete structural coverage were independently
recomputed using Hall tests and a separate enumerator/canonicalizer.

Exact positivity covers all 204,388 population faces. The ledger contains 63,917
nontrivial face aliases and 53,722 normalized targets, certified by 53,477
binomial-square certificates and 245 general-square certificates. Independent replay
checked all rational weights, identities, normalizations, and face coverage. See
`three-attachment/README.md` and its authoritative replay files for details.

**Final theorem: every finite preorder of actual gamma degree at most four has
rank-ultra-log-concave gamma coefficients.** The a=0,1,2,3 branches and all 76
canonical four-attachment templates have independently checked proofs. Every
remaining template/population face is covered; no bounded-population inference
is used.

## Final four-attachment result

Both inequalities 4γ₂²≥9γ₁γ₃ and 3γ₃²≥8γ₂γ₄ are proved for every one of the
76 canonical templates and every nonnegative integer population. Together with
the rank-sensitive universal first inequality and the earlier branches, this
settles the original actual-degree-four question affirmatively.

The independent coverage ledger has 39,367 original outstanding face tasks,
39,367 approved tasks and zero remaining tasks. The approved global ledger has
50 exact identities: 24 middle-gap identities, 23 whole last-gap identities,
and three last-gap core-correction identities used with the exterior Lorentzian
lemma. The small and medium face batches and separately audited ordinary proofs
supply the other cases. The final template 26 identity contains 2,273 positive
rational square orbits and 8,652 nonnegative binomial remainder terms.

The definitive portable package is under
`/workspace/shared/preorder-degree-four-result/reproducibility/`.
Its `verify.py --mode fast` command replays fixed exact algebra and coverage;
`--mode full` additionally regenerates every independent bounded-core kernel.
The earlier exploratory logs below are historical evidence, not premises of the
final theorem. No claim of proof-assistant formalization or novelty priority is
made.

## Non-pendant exploration

`search_a2.cpp` evaluates exact binomial-basis support polynomials for independent
clone populations attached only to two distinguished vertices of a six-element
core. Removing those attachment vertices leaves four vertices, proving matching
number at most four for every population. The initial deterministic random run
checked 119,360 actual-degree-four evaluations with populations up to 1,000,000;
there was no failure.

`search_attachments.cpp` generalizes this to a attachment vertices in an (8−a)-vertex
core. It keeps only nonbipartite template graphs. The a=3 initial run checked 251,126
actual-degree-four evaluations (populations up to 1000), with no failure.

`search_unique_attachments.cpp` uses an enlarged (9−a)-vertex core, so the remaining
core can have an odd component. It deduplicates labeled templates and exports
small-population audit cases. `verify_grouped.py` checks those cases independently
by expanding the graph and enumerating ordinary matching supports.

Completed larger exact-integer sample runs:

- Seven-vertex core, two attachment vertices: 84,712 distinct core/sign specifications with nonbipartite
  template graphs and 4,055,790 actual-degree-four population evaluations
- Six-vertex core, three attachment vertices: 163,678 distinct core/sign specifications with nonbipartite
  template graphs and 4,614,428 actual-degree-four population evaluations
- Four-vertex core, four attachment vertices: 5,243,495 actual-degree-four population
  evaluations across 99,527 template draws (with repetitions)

There were no failures. The larger grouped runs sample populations through 1000.
These random-population searches are evidence only, with no exhaustiveness or
all-population theorem claimed.

## Reproduction

Compile C++ sources with `g++ -O3 -std=c++17 FILE.cpp -o FILE`, run each binary,
and run each `verify_*.py` with Python 3. The attachment search accepts number of
random core draws and attachment count, e.g. `search_unique_attachments 100000 3`.

The slower naturally labeled `exhaust9.cpp` was stopped after completing quotient
sizes through eight (25,401,347 cases; 23,753,186 actual degree four; no failures).
Its incomplete log is retained for audit, but the complete n=9 result comes from
`exhaust9_canonical.cpp`, not from that unfinished naturally labeled run.

## Status

The actual-degree-four ULC question is now proved affirmatively by the structural reduction and independently verified all-population certificates. The same-ground-set disjoint-support convention is essential. General actual degree five and beyond is not settled by this package.
