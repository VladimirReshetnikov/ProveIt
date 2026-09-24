# Source review and mathematical status

Review date: **20 September 2026**.

## Selected published problem

The chosen problem is the conjectured exact deterministic state complexity of
the shuffle of two regular languages. The common finite alphabet is not fixed
in advance. The upper-bound formula and the known parameter ranges are taken
from the sources below, not presented as discoveries of this manuscript.

### Brzozowski, Jirásková, Liu, Rajasekaran, and Szykuła (2016)

*On the State Complexity of the Shuffle of Regular Languages.*
DCFS 2016, LNCS 9777, pages 73–86.

- DOI: https://doi.org/10.1007/978-3-319-41114-9_6
- Accessible version actually reviewed: https://arxiv.org/abs/1512.01187v3
- PDF: https://arxiv.org/pdf/1512.01187
- The arXiv version is dated 15 July 2016.

This paper gives the upper bound, attainment for one operand with at most five
states and arbitrary size of the other operand, and attainment for the 6-by-6
case. Its abstract explicitly identifies general reachability and tightness as
open. The full accessible paper was consulted, including its containment and
degree-one reductions and its antichain-width argument. The current manuscript
reproves the reductions with explicit root handling and uses them as prior work.
Three of the manuscript's four distinguishability arguments use a much larger
alphabet than the source's three-letter-alphabet theorem and are not advertised
as alphabet-size improvements. The fourth reproduces the source's three-letter
construction, with closed-form distinguishing words, so that no
distinguishability step is imported unproved; the construction itself is the
source's and is credited as such.

Specific locations used in the accessible version: the abstract; Table 1 on
PDF page 6, which marks the 6-by-7 and larger six-row cases as unresolved;
Lemmas 8-9 on pages 7-8; Theorem 10 on page 8; and Lemma 12 with Corollary 13
on pages 9-10.

### Caron, Luque, and Patrou (2019 preprint; 2020 journal article)

*A Combinatorial Approach for the State Complexity of the Shuffle Product.*
Journal of Automata, Languages and Combinatorics 25(4), pages 291–320 (2020).

- DOI: https://doi.org/10.25596/jalc-2020-291
- Accessible preprint actually reviewed: https://arxiv.org/abs/1905.08120
- PDF: https://arxiv.org/pdf/1905.08120
- Preprint date: 20 May 2019.

The accessible preprint recasts reachability using partitions, retains the
shuffle conjecture, and gives a further antichain formulation. The journal's
bibliographic record was checked, but the access-restricted journal full text
was not used as though it had been read. Mathematical comparisons are with the
accessible preprint. Note that its term "dense" states refers to incomparable
row and column supports, not to graph density.

### Sperner (1928)

*Ein Satz über Untermengen einer endlichen Menge.*
Mathematische Zeitschrift 27, pages 544–548.

- DOI: https://doi.org/10.1007/BF01171114

The manuscript supplies a self-contained permutation-counting proof of the
antichain bound and attributes the underlying theorem to Sperner. A one-line
probabilistic phrasing of the same proof is recorded as a remark; it is the
same mathematics, not a second theorem. Publisher metadata were checked; no
claim is made to a new antichain theorem. The manuscript also notes that the
finite search space is already bounded without Sperner's theorem, by the crude
count of admissible columns.

### Z3 documentation

- Official C API: https://z3prover.github.io/api/html/group__capi.html

The local shared library reported version 4.13.3.0. This local version and the
run environment are recorded in `audit/environment.json` and `logs/environment.json`.
The documentation supports the API usage; it does not validate the mathematical
certificates. Verification does not invoke Z3 on any of the four routes, and
the discovery path for database C does not invoke it either.

## Provenance of this merged package

This package merges four independently prepared research packages on the same
conjecture: `shuffle-six-state-certificates` (the spine, and certificate
database A), `shuffle-six-state-strip` (the same database A by the same proof,
plus the support-form word bound and a second checker architecture),
`shuffle-six-state-theorem` (an independent finite computation, database B),
and `shuffle-six-state-complexity` (a materially different proof adding a
balanced-triple reduction, database C). Each proved the shared theorem. The
merged manuscript proves the shared theorem once and keeps all four routes to
its finite premise. Where the four packages disagreed about a source's status
or about what the literature already establishes, the most cautious statement
has been kept.

## Contribution claimed by the supplied proof

The manuscript claims a computer-assisted proof for the complete six-state
strip: `m,n >= 2` and `min(m,n) <= 6`. The portion beyond the ranges explicitly
proved in the located sources is 6-by-n for n >= 7 and its transpose.

The key stronger finite property is the existence of a strictly smaller
predecessor with full row and column support for every irreducible matrix with
at most six rows. Full support makes the predecessor valid at every root, so
unrooted row/column classification is compatible with a rooted induction.

The archive contains three independent certificate databases — 10,642, 10,619
and 453 positive certificates — with executed independent local and coverage
checks for each. Their completeness is not inferred from any search program's
statement that it finished. Database A's coverage is audited by a direct
traversal of all labeled column antichains, compared against row-permutation
orbits of locally validated certificates; database B's verifier regenerates
its own canonical representative set and compares target-key sets; database C's
pure-Python checker reruns its residual enumeration and checks orbit
disjointness. Of the 10,619 target keys shared by databases A and B, none
carries the same witness in both.

The manuscript also proves and implements three forms of the access-word
bound: `|S| + min(m,n) - 2`, the support form `E + min(r,c) - 2` with its
corollary `|w| <= 2E - 2`, and the dual bound
`min{2(|S|-1), |S| + min(m,n) - 2}`. The support form and the `2(|S|-1)`
branch are strictly stronger statements than the dimension form.

## Explicit limitations

This is not a proof of the entire unrestricted shuffle conjecture, not a
fixed-small-alphabet reachability construction, and not a general
state-complexity theorem for one-state operands. The stronger auxiliary
predecessor conjecture is only verified through six rows. Failure of that
stronger property in a later search would not automatically disprove the
original shuffle conjecture; nor would failure of every one-step strict
predecessor, since a reaching path may pass through a subset of equal or
larger cardinality.

It is also not proved that every valid target has a strictly smaller one-letter
predecessor: an isolated-cell seed may need two letters and may pass through a
subset of equal cardinality. The verified one-letter property concerns only the
irreducible class, and there only with full-support predecessors.

The three databases were prepared in the same environment. Separately
implemented searches and checkers reduce correlated implementation risk; they
do not eliminate it. "Independent checker" throughout means independent of the
search and canonicalization algorithms, and of the other databases'
representative sets and witnesses — not independent human authorship or
independently maintained third-party software.

This archive ships no checksum manifest, and none should be added. The three
certificate-file digests are quoted in the manuscript and the README; a digest
identifies exact data and is not a substitute for checking them.

The source search did not locate a later resolution of the six-state strip or
of the full conjecture. That search was limited by the query formulations used
and by indexing coverage, and it did not reach unpublished or unindexed work.
A finite web/literature review cannot certify the absence of every relevant
publication, thesis, preprint, private result, or parallel discovery. Novelty
and priority therefore remain provisional even though the mathematical claim is
supported by the supplied proof and artifacts. A standalone record of the
positioning audit, with the exact locations consulted, is in
`logs/literature_search.md`.

No independent human review, journal peer review, Lean/Coq/Isabelle verification,
or other formal kernel certification has been performed. The correct present
label is **reproducible computer-assisted research proof**. The article clearly
separates established prior work, analytic reductions, executed finite checks,
supplementary tests, and unsolved extensions.
