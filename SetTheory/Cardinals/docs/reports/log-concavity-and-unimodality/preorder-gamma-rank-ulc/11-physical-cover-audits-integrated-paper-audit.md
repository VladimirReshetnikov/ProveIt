# Independent mathematical audit of the integrated physical-cover-three supplement

Date: October 1, 2026. Verdict: **APPROVED**.

The integrated manuscript `article/physical-cover-three.tex`, with its final five-page
PDF, faithfully incorporates the approved arbitrary-internal-core assembly and
two additional bipartite-only strictness statements. The complete mathematical
source was reviewed independently. No mathematical correction was required.
This approval covers the mathematics and integration; final archive integrity,
fresh-extraction replay, and all-page visual QA are separate release gates.

## 1. Main theorem and actual-degree normalization

The definitions distinguish physical vertices from independent tail/head roles
and count each feasible ordered disjoint endpoint support once. The displayed
general rank-ULC inequality has the correct binomial normalization. Retaining
arcs of positive product weight gives exactly the positive support relation,
so the actual degree is its physical matching number. Positive submatchings
supply every lower coefficient and preclude internal zeros.

The universal first-gap lemma is correct for arbitrary loopless directed
relations. The weighted compatibility graph counts matching witnesses, so its
weighted edge sum bounds the Boolean rank-two coefficient from above. Merging
nonadjacent positive masses gives the stated clique bound with actual degree
`d`. The first cubic gap and the stronger surviving quadratic condition follow.
Degrees zero and one impose no Newton inequalities. No zero activity is divided
out, and no degree drop is silently left under cubic normalization.

A physical cover of size at most three bounds the matching degree by three.
For a size-three cover, the manuscript's rank-two decomposition separates
supports by whether they use two or three core vertices; a cubic support cannot
contain an internal edge. These are support-level statements despite possible
multiple matching witnesses. Opposite arcs and every internal core pattern
remain allowed. The role-cover corollary is valid because `P subset Q` makes
`Q` itself a physical cover of size at most three.

## 2. Boundary dependency and internal assembly

The integrated boundary statement preserves independent role variables and
matches the independently audited all-size theorem. The cited accompanying
manuscript title is exact; its Theorem 1.1 is the boundary result and Theorem 3.1
is the full nonnegative core-monomer Rayleigh result used later. The bundled
dependency ZIP is byte-identical to the previously approved release, with
SHA-256 `718fcbed392be1520ad2fe09313ff18b10b38a5338f5a704cbad2cf7b7b8c488`.
The manuscript clearly retains the finite-certificate dependency instead of
claiming that the complete proof is nonenumerative.

The new ordinary steps agree with `assembly-audit.md`:

- Removing the edge at a prescribed core of any cubic witness proves
  `a_k b_ij >= c` coefficientwise; Boolean counting and multiple deletion choices
  have the correct direction
- For a fixed internal unordered pair, roles force its orientation and the
  remaining cross edge, so each resulting support occurs at most once in
  `w_ij=h_ij a_k`
- A mixed rank-two support has two tails and two heads, three of them in the
  core. Its exterior vertex has at most two available opposite-role core
  partners, so total internal-witness multiplicity is at most two
- The numerical ordering of the three `b` values carries the corresponding
  `w` values, and the stated linear slack is an exact nonnegative expression
- The two-square lower bound and full exact remainder identity expand to
  `gamma_2²-3 gamma_1 gamma_3` with precisely the displayed coefficients

The three kinds of remainders in the exact identity total

    3[(xy+xz+yz)-Ac],
    3[sum w_ij b_ij-Ec],
    3[H(x+y)-sum w_ij b_ij],

respectively. Their telescoping verifies the identity without relying on
numerical tests. The manuscript correctly calls it a scalar certificate after
nonnegative specialization, rather than coefficientwise positivity of the
whole Newton gap.

## 3. Strict covariance characterization, bipartite case only

The section explicitly excludes all internal core arcs and assumes positive
core monomers. These hypotheses are retained by both propositions and are not
silently carried over to the more general main theorem.

Different active physical components give a unique product decomposition of
endpoint supports and weights, hence independence. Two connected core vertices
admit a simple alternating path of length two or four because the physical
shore contains only three core vertices.

For a two-edge path, positive available arc directions produce a monomial of
`a_j a_k` with the exterior vertex repeated. It cannot occur in `b_jk`, so the
quadratic Rayleigh coefficient is strictly positive. For a four-edge path,
the two stated size-two supports are individually physically disjoint and
produce a positive boundary monomial with only two exterior vertices. Such a
monomial cannot occur in `a_i c`, which requires three distinct exterior
vertices. Reusing a physical vertex, possibly in different roles, across the
two factors is valid; no individual support reuses a physical endpoint.

The coefficientwise Rayleigh result prevents negative coefficients elsewhere
from canceling either positive monomial. Positive monomers, the positive empty
support contribution to `F`, and the exact covariance identity then give strict
negative covariance. Replacing both indicators by their complements preserves
covariance. The proof uses active arcs, so nominal edges killed by a zero role
activity cause no false strictness claim.

## 4. Cubic equality characterization, bipartite case only

For `c>0`, the three-square identity shows that equality requires equal positive
`b` values and vanishing boundary gaps. A shared exterior neighbor `x` of two
cores gives a strictly positive two-exterior boundary monomial whenever the
third core has a different neighbor `y`. The two constructed supports have
physically disjoint endpoints in each factor and use only `x,y` in the product,
while the negative `a_i c` term cannot do so.

In the remaining case, actual degree three ensures that the third core has a
neighbor and a saturating matching exists. Since it has no neighbor other than
`x`, its edge in every saturating matching uses `x`; another core must therefore
use some `y != x`. Relabeling that core as the doubled one gives the same strict
boundary obstruction. Thus equality prohibits all shared exterior neighbors.

The resulting active physical graph, after discarding isolates, is exactly
three separate core-centered stars. On a star, only one edge may be used; each
available directed orientation contributes its own singleton support weight.
Support factorization gives `b_ij=a_i a_j`, `c=a_0 a_1 a_2`, and
`Gamma=product(1+a_i t)`. All three `a_i` are positive because `c>0`, so equality
of the three pair products forces the three totals to coincide. The converse
and `(1+at)^3` conclusion are immediate. This proof establishes precisely the
claimed top cubic equality, not an assertion at a lower surviving degree.

## 5. Computational statements and scope

The independent assembly checker and its frozen receipt match the originally
approved files. Its reported 4,096 local witness graph cases, 1,600 deletion
cases, and 10,080 integer/zero-activity evaluations are accurate. The producer
checker was inspected: it independently verifies the full exact remainder
identity using exact integer arithmetic and checks rank-ULC at the measured
actual degree. Its frozen receipt supports the manuscript's 10,496 total cases,
64 internal core patterns with 100 larger cases each, 6,478 zero-activity cases,
and 504 larger activity-induced degree drops.

These bounded tests are accurately presented as corroboration for ordinary
all-size assembly arguments. The boundary dependency remains the only finite
classification used as a premise. The manuscript makes no unsupported claim
of real-rootedness, signed-monomer stability, proof-assistant formalization,
literature-wide priority, or a theorem for physical covers of size four or five.

The historical source notes were preserved byte-for-byte with their original
status wording. Their included approval receipts establish the current status;
changing a source note solely to rewrite that history is unnecessary.

## 6. Final layout condensation

The final abstract and proof-status section were shortened to avoid a
references-only sixth page. The condensed prose was rechecked against the
approved mathematical source and frozen receipts. The theorem hypotheses,
proofs, exact remainder identity, strictness scopes, numerical counts, and
explicit computer-assisted dependency remain correct. This audit and its
approval receipt bind the final five-page TeX/PDF hashes.
