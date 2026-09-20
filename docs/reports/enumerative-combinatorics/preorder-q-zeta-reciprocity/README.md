# Support reciprocity and the q-zeta polynomial of preorder lattice-point posets

**Merged research draft, 20 September 2026.** Prepared for Vladimir Reshetnikov
with AI assistance.

The package contains a complete proposed proof of the full q-refinement of
Athanasiadis–Chapoton Conjecture 4.9 (arXiv:2605.26916v1, equation (21)),
strengthened to an identity for each exact support of a maximal lattice point.
The supplied manifest explicitly excluded this refinement from its existing
ordinary q=1 reciprocity result.

The strengthened statement is proved **twice**, by two arguments that share
nothing beyond two classical imports and the elementary structure of the
poset, and one of the two proofs carries a second, interchangeable geometric
engine inside it. Only one proof reaches every negative q-integer; only the
other reaches arbitrary height functions. Both are kept in full.

The draft has not been independently refereed or checked in a proof assistant.
It imports established Postnikov theorems, Hall's theorem and
Ehrhart–Macdonald reciprocity; all additional steps are proved in the article.
Finite checks are supporting evidence, not a proof or a priority certificate.

## Provenance

This package merges three separate research drafts of 20 September 2026, each
of which independently proved both the q-identity and the exact-support
strengthening:

| Original directory | What it contributed |
| --- | --- |
| `preorder-q-zeta-support-reciprocity` | The spine. Proof A, Engine 1 (cumulative supports, capacities `1+1_T`, Postnikov's bipartite duality, two-value interpolation), the Tutte evaluation, the product rule, the nontransitive and capacity-two obstructions, most of the infrastructure. |
| `preorder-q-zeta-supportwise` | Proof A, Engine 2 (exact supports, residual and privatization Hall lemmas, a standalone bipartite Euler identity from Postnikov's Theorem 11.3 alone), the arbitrary-height theorem, the `[t^(n-2)]` coefficient formula, the Hall appendix, the standalone bipartite test suite. |
| `preorder-q-reciprocity-weighted` | Proof B (independent-capacity reciprocity, the `v=0` pivot, the transfer involution), the evaluation at every `[-r]_q`, the Gaussian endpoint formula, the colored-composition model, the sharp extreme degrees. |

The donor directories are left untouched; nothing here supersedes the separate,
earlier package `enumerative-combinatorics/preorder-polytope-reciprocity`,
which proved the ordinary q=1 case and is cited as prior work in three places
(Section 1.5 of the article).

## Main files

- `article.pdf`: the 45-page article, with both proposed proofs, both
  geometric engines, consequences, examples, three obstructions, the
  computational report and a merged proof audit.
- `article.tex`: standalone LaTeX source; no external figures or bibliography
  build are required. `references.bib` is supplied for reuse elsewhere.
- `code/verify.py`: support/interior/transport suite.
- `code/verify_transfer.py`: `[-r]_q`, transfer and capacity suite.
- `code/verify_supportwise.py`: inverse-matrix, nonlinear-height and
  standalone bipartite-lemma suite.
- `code/test_unit.py`: ten fast normalization and boundary tests.
- `data/verification*.json`, `data/verification*.log`: actual full-run results
  of the three verifiers, including all random-test relations and a
  deterministic witness digest.
- `data/unit_tests.log`, `data/latex_build.log`: actual test and build
  transcripts.
- `data/examples.csv`: a seven-row exact example table.
- `data/build_report.txt`: PDF rendering and document-quality record of the
  supportwise draft's build, retained as a document check (not a mathematical
  certificate).
- `STATUS.md`: proof scope, dependencies, and verification limits.
- `notes/source_audit.md`: merged source/version ledger and search limits.
- `notes/proof_audit.md`: logical dependency map and delicate transitions.
- `notes/manifest_provenance.txt`: the supplied manifest's relevant entry,
  verbatim, with its hash and source line numbers.
- `manifest_entry.tex`: proposed entry for the user's catalogue.
- `build.py`, `Makefile`: PDF rebuild and check helpers.

No checksum manifest is shipped, and none should be added.

## The results

For the preorder polytope

    Q_tau = {x >= 0 : sum_{i in I} x_i <= |I| for every ideal I},
    P_tau = Q_tau intersect Z^E,

write `H_tau(z)` for the sum, over maximal points a, of the squarefree
monomial whose support is `supp(a)`. The strengthened identity is

    H_tau(z) = (-1)^n * sum_{B,S subset E, 1_B+1_S in P_tau}
                         (-1)^(|B|+|S|) * product_{i in B} z_i,

equivalently, for every B,

    #{a maximal : supp(a) = B}
      = (-1)^(n-|B|) * sum_{S : 1_B + 1_S in P_tau} (-1)^|S|.

Since the number of lower covers of a equals its support size, the diagonal
`z_i = q^(-1)` yields the requested conjecture exactly. Beyond it:

- **Every negative q-integer.** With `C_{r,0}(t)=1` and
  `C_{r,a}(t) = sum_{s=1..min(r,a)} binom(a-1,s-1) e_s(t,t^2,...,t^r)`,

      (-1)^n Z_q(P_tau, [-r]_q) = sum_{b maximal} product_i C_{r,b_i}(q^-1),

  with nonnegative integer coefficients, monic of degree rn, lowest exponent
  equal to the number of maximal equivalence classes.
- **Arbitrary normalized heights.** For h strictly increasing on comparable
  distinct elements with h(0)=0,

      Z_{q,h}(P_tau, [-1]_q) = (-1)^n sum_{b maximal} q^(-h(1_supp(b))).

  The exponent uses the Boolean support vector, not h(b).

The key intermediate theorem of Engine 1 counts maximal points with support
contained in T by the interior lattice points of `Q_{tau*}(1+1_T)`; its graph
has left part T and right part E plus one universal auxiliary vertex. Engine 2
instead reduces the signed Boolean sum at the exact support to an alternating
count over the independent sets of a private-element bipartite graph, and
evaluates that count by an Euler identity valid for every bipartite graph.
Proof B uses none of this: it keeps an auxiliary capacity alive through
multivariate Ehrhart reciprocity, sets it to zero to annihilate every
non-maximal layer, and transfers local coefficients by the involution
`T f(z) = (1-z) f(-z/(1-z))`.

## Exact verification

Run the three recorded profiles from this directory:

    python code/verify.py --exhaustive 5 --random-per-size 16 --seed 20260920 --output data/verification.json
    python code/verify_transfer.py --output data/verification_transfer.json
    python code/verify_supportwise.py --output data/verification_supportwise.json

Run the ten fast tests:

    python -m unittest discover -s code -v

A small smoke profile:

    python code/verify.py --exhaustive 3 --random-per-size 4 --output data/smoke.json

`make check` runs all four. The three verifiers test three different theorems
and none subsumes the others:

- `verify.py` passed all 7,332 labelled preorders of sizes 0 through 5:
  228,075 separate support coefficients and 228,075 interior-capacity counts,
  plus the transport/assignment model for every one of them. It also checked
  48 additional cases of sizes 6 through 8 (interior and assignment checks
  through size 7 only), the weighted lattice polynomial in 156 evaluations at
  both nonnegative and negative capacities, the nontransitive counterexample
  checked to *fail*, and five named examples by positive-multichain
  interpolation at q = 1, 2, 3, 5.
- `verify_transfer.py` passed 390 labelled preorders of sizes 0 through 4:
  390 multivariate support identities, 390 signed local-polynomial transfer
  tests, 1,560 negative-evaluation polynomial identities at r = 1..4, 1,250
  direct capacity and reciprocity checks, 410 positive/negative interpolation
  comparisons, and 24 extra deterministic random preorders of sizes 5 to 8
  including relations with genuine cycles. It accepts `--max-n 5`.
- `verify_supportwise.py` passed all 7,332 labelled preorders of sizes 0
  through 5 independently (228,075 support identities), plus 64 seeded
  preorders at each of sizes 6, 7, 8 (28,672 more; 256,747 in total), 1,170
  direct inverse-matrix evaluations, eight exact interpolations from positive
  multichains including one with the nonlinear height `h = rho^2`, and — found
  nowhere else — the bipartite Euler lemma tested standalone on all 5,058
  labelled bipartite graphs with 0 <= r <= 3 and 0 <= s <= 4, plus 300 seeded
  graphs, comparing three independently computed counts.

The seeds and sampling depths differ on purpose and have been preserved:
`verify.py` and `verify_transfer.py` use seed 20260920 and sample 16 relations
per size at n = 6, 7, 8; `verify_supportwise.py` uses seed 26092049 and samples
64 per size. The sampled populations are therefore genuinely different, and
that independence is part of the evidentiary value.

The source paper already reported univariate verification through size 6;
these are independent tests of the stronger identities, not a claim to improve
its exhaustive size bound. All arithmetic is integer or exact rational; the
only floating-point quantity recorded anywhere is elapsed wall-clock time, and
a failed equality raises rather than recording approximate agreement.

The three verifiers need Python 3.10 or newer and use only the standard
library; no other package, service or dataset is required. The recorded runs
used Python 3.14.4 and took about 20, 6 and 1 seconds respectively. Do not use
Python's `-O` option, since some test assertions use `assert`.

## Reuse with another preorder

A relation is a tuple of row masks. Bit j of row i means i <= j; labels start
at zero. For example, `(21, 26, 21, 8, 16)` is the article's five-coordinate
example in the coordinate order a,b,c,d,e.

    import sys
    sys.path.insert(0, "code")
    from verify import is_preorder, boolean_coefficients, direct_qzeta_negative
    rows = (21, 26, 21, 8, 16)
    assert is_preorder(rows)
    coefficients = boolean_coefficients(rows)
    print(coefficients[24])              # exact support {d,e}: 2
    print(direct_qzeta_negative(rows, 2))  # -65/32, using positive chains

`boolean_coefficients` returns coefficients indexed by support bit mask.
`closure` is available as an explicit operation; do not confuse a nontransitive
relation with its transitive closure. The other two verifiers use the same row
mask convention and can be imported the same way.

## Rebuild the PDF

The prebuilt PDF needs no software installation. To rebuild with an existing
TeX distribution, run:

    python build.py

To rerun all checks first:

    python build.py --check

Alternatively run `make pdf`, or `pdflatex article.tex` twice, or
`latexmk -pdf article.tex`. The source uses ordinary AMS/LaTeX packages and
Latin Modern fonts. The recorded build was clean: 45 pages, no overfull or
underfull boxes, no unresolved references, no LaTeX warnings. No font files or
third-party research papers are distributed in this archive.

## Scope and reuse

Three obstructions bound the result in three different directions, and they
carry four distinct failure statements between them: the pure downset
`down(1,1,1) ∪ down(3,0,0)` in N^3 refutes both the supportwise identity and
the far more general transfer identity; the reflexive nontransitive
three-source system `A_1={1,2}, A_2={2,3}, A_3={1,3}` shows that reflexivity,
purity, unit supplies, box intervals and a transport representation together
are not enough; and a single coordinate of capacity two shows that unit
capacities are essential. Neither the proofs nor the tests establish other
real-rootedness or gamma-positivity conjectures for preorder polytopes, and
`H_tau` is not the preorder h-polynomial of Section 5 of the source, which
counts support sizes over all lattice points.

Original exposition and code in this package are offered under MIT-0; the
material merged in from the two donor drafts was released by them under
CC0-1.0. The supplied manifest excerpt and cited external works retain their
own provenance and rights; no external paper is included.
