# Smooth Everywhere, Universal on the Integers

**Canonical quartic certificates with five extra variables, no local
obstruction, and explicit Jacobian identities**

This is a research report dated 2 October 2026, built from one manuscript of
batch 79 of ProveIt's incoming reports (cluster J1). The manuscript is
AI-assisted: its title page reads "Prepared for Vladimir Reshetnikov /
Developed with ChatGPT", and its PDF metadata name "Research prepared for
Vladimir Reshetnikov with ChatGPT". It is called *manuscript 13* after its
batch-79 manuscript number, which is also the file prefix of its shipped
programs and data.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 13 (sole source) | batch 79, manuscript 13 | `Smooth_Quartic_Diophantine_Certificates.zip` (`ef2fc7990`); inner directory `smooth_diophantine/`, main file `article.tex` (1,733 lines), 28-page PDF | `a845ab5d0` (the commit at which it read `canonical-diophantine-certificates/01-causal-traces-RESEARCH_STATUS.md`, blob `e768b2284c67`; its source audit also names the root `README.md` blob `bc4c514b61e3`) | `224ca41df` | the whole report: Sections 1–16 and Appendices A–C, with its own numbering |

**The result.** For integer polynomials `f_i(x)` of degree at most two, with
homogeneous quadratic lifts `q_i(x,t)`, the finalizer

    F = Σ q_i(x,t)² + (tu − 1)² + g(z1) + g(z2) + 2 g(z3),   g(z) = 2z² − z,

is a quartic in five more variables whose natural zeros are in bijection with
the source's natural zeros and whose integer zeros are exactly two
sign-related copies of the source's integer zeros, while its *affine* scheme
is smooth over `Z` with geometrically integral fibres, certified by an
explicit integral Bézout identity of product degree at most seven; it always
has a nonnegative point over `Z[1/2]`, points over every `Z_p` and modulo
every integer, rational points dense in its real locus, and exactly two real
path components.

**Status: AI-assisted, unrefereed, not formalized.** Conventional proofs and
finite exact-arithmetic checks (21,128 recorded assertions). Nothing in the
report is formalized in Lean or Rocq, and no priority is certified.

**Already reviewed.** After placement, the Hilbert-tenth-problem research tree
reviewed the archive: `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_smooth_quartic_aebfa386e.md`,
with its replay helper `review_smooth_quartic_aebfa386e.py` and receipt
`review_smooth_quartic_aebfa386e.json` (commit `fd4a2e8d3`), indexed in
`incoming_substrate_review_aebfa386e.md` of the same directory. Verdict:
"PASS within the stated mathematical and implementation scope". It replayed
all 21,128 author assertions and reproduced both example exports byte for
byte, checked the integral Jacobian identity in every characteristic, the
fibre bijections, geometric integrality, the local and dyadic constructions
and the restricted guard-weight optimality, and ran independent checks
(12,636 integer and 640 natural fibre tuples, 120 counter runs against a
separate interpreter). No theorem defect and no required repair; no patch
exists, and the shipped programs are the delivered ones. The report's
editorial preface summarizes the review's five scope points.

```
README.md                                     this guide
article.tex                                   the report, standalone LaTeX with an internal bibliography
article.pdf                                   the compiled report, 34 pages (unnumbered title page, then pages 1–33)
13-smooth-quartic-RESEARCH_STATUS.md          manuscript 13's research and verification status, as delivered
13-smooth-quartic-SOURCE_AUDIT.md             manuscript 13's repository and literature provenance audit, as delivered
code/13-smooth-quartic-Makefile               delivered make targets: test (python code/verify.py), pdf (three pdflatex passes), clean
code/13-smooth-quartic-counter_frontend.py    bounded natural-number counter-program frontend (Section 10)
code/13-smooth-quartic-smooth_compiler.py     validated quadratic finalizer, Jacobian certificate, dyadic point, 2-adic residues
code/13-smooth-quartic-verify.py              the 21,128-assertion suite; rewrites examples/*.json and verification/results.json
data/13-smooth-quartic-countdown_T3.json      the countdown export: 29 variables, 97 monomials, input 2, horizon 3 (Section 10.3, Appendix A)
data/13-smooth-quartic-document_qa.json       delivered layout record of the delivered 28-page PDF (not of this report's PDF)
data/13-smooth-quartic-inconsistent.json      the export of the constant residual 1 with one unused variable (Appendix B)
data/13-smooth-quartic-requirements.txt       sympy==1.14.0
data/13-smooth-quartic-results.json           the recorded run: PASS, 21,128 assertions in 40 groups, Python 3.13.5, SymPy 1.14.0
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md` is
byte-identical to the delivery. Delivered name (in `smooth_diophantine/`) →
shipped name:

- `code/smooth_compiler.py`, `code/counter_frontend.py`, `code/verify.py`,
  `Makefile` → `code/13-smooth-quartic-*`;
- `examples/countdown_T3.json`, `examples/inconsistent.json`,
  `verification/results.json`, `verification/document_qa.json`,
  `requirements.txt` → `data/13-smooth-quartic-*`;
- `RESEARCH_STATUS.md`, `SOURCE_AUDIT.md` → `13-smooth-quartic-*` at the
  report root;
- `article.tex` → `article.tex` (the report);
- `README.md` → replaced by this README (its contracts are listed under
  "Status" below).

Not shipped: the delivered `article.pdf`; the delivered `README.md`;
`verification/run.log`, which is `verification/results.json` plus one final
newline (the suite's standard output); and the checksum file `SHA256SUMS`
(15 of 15 entries verified at placement). They survive in the archive of the
arrival commit:

```sh
git show ef2fc7990:docs/incoming/Smooth_Quartic_Diophantine_Certificates.zip > sq.zip
```

No regenerable data were excluded from this report; there is nothing to
reconstruct beyond the run log, which `verify.py` prints.

## Labels and numbering

Every label carries the prefix `sdf:`. The manuscript's 64 labels are `sdf:`
plus their delivered names; none was dropped or renamed apart from the prefix.
The write added 21 labels, 85 in all: `sdf:sec:preface` (the editorial
preface), `sdf:sec:intro`, `sdf:sec:repo`, `sdf:sec:novelty`,
`sdf:sec:conclusion`; `sdf:thm:weights`, `sdf:cor:five` and `sdf:cor:nobound`
on the three numbered results that had no label (Theorem 9.1, Corollaries 9.4
and 11.2); ten `sdf:q:*` on the research questions (15.1–15.10);
`sdf:app:export` and `sdf:app:sourcereview` on Appendices B and C; and
`sdf:app:provenance` on the new Appendix D.

The editorial preface is unnumbered, so the manuscript's section, statement,
equation and table numbers are unchanged. Text written at the write is marked
`[write]`; text without a marker is the manuscript's own.

## Setting and notation

`N = {0, 1, 2, …}`; residuals are integer polynomials evaluated in `Z`. The
manuscript reuses letters between its algebraic sections and its counter
frontend (Section 10): `g` is the guard and also the number of guarded edges,
`E` the Euler combination `4H` and also the number of edges, `H` the sum of
squares and also the halt self-loop edge, `p`, `d`, `h`, `t`, `q`, `c`, `B`,
`w` have second meanings there or elsewhere. The preface's notation table
lists every reused letter. The terms most likely to be misread:

- **smooth / good reduction** — the affine scheme `X → Spec Z` is smooth; no
  smooth projective closure and no smooth proper model is claimed;
- **dyadic point** — existence of a point over `Z[1/2]`, not density;
- **degree four** — witness degree; a loader parameter treated as a coordinate
  gives total degree six (Section 11.3);
- **canonical** — witness-preserving over `N`; not single-fold or finite-fold
  MRDP;
- **finalizer** — a geometric normal form; it costs more arithmetic
  operations than a plain sum of squares, unlike the operation-count
  "finalizers" of the Hilbert-tenth-problem research tree.

No symbol was renamed and no normalization changed.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by manuscript 13, for:

- the finalizer (Theorem 3.1): exact degree four; the natural-zero bijection
  `a ↦ (a,1,1,0,0,0)`; integer zeros as two signed copies; smoothness over `Z`
  of relative dimension `n+4` with geometrically integral fibres
  (characteristic-two fibre an affine space); the explicit identity
  `AF + Σ B_v F_v = 1` with `deg A ≤ 3`, `deg B_v ≤ 4`; a nonnegative
  `Z[1/2]`-point of height `O(√(c+1))`, points over every `Z_p` and modulo
  every integer; rational density (Euclidean and Zariski); two real path
  components;
- size bounds for the expanded polynomial (Proposition 3.2) and exact height
  and box-count transfer (Corollary 4.2);
- the weighted-guard classification (Theorem 9.1: with first weight one,
  universal smoothness exactly for total weight 4 or 16), the `(1,3)` dyadic
  obstruction (Lemma 9.2, Proposition 9.3) and the restricted optimality of
  three guards, i.e. five auxiliaries, within positive weight-four guard
  families (Corollary 9.4);
- a bounded counter-program frontend with a unique natural witness and exact
  counts `n_T`, `m_T` (Theorem 10.1);
- computably enumerable completeness of integer and natural solvability on
  the compiled class with the geometric package (a)–(e) (Theorem 11.1), and
  no computable bound on the least integer witness (Corollary 11.2);
- the power-of-two padding to higher degree with the same five variables
  (Theorem 12.1; proved, not implemented).

**Credits (preface and `[write]` notes).** Three pieces re-present results of
the collection's report `canonical-diophantine-certificates`, with no novelty
claimed: Lemma 2.2 (natural version) is its
`cdc:wf:lem:quadratization`; Theorem 10.1 is a second presentation of its
counter adapter (`cdc:eq:zero-guard`, Section `cdc:pt:sec:boundary`, the halt
self-loop caveat of `cdc:ct:sec:substrates`), new only in the exact counts and
the positive-edge slack form; the computability core of Theorem 11.1 is its
quartic normalization `cdc:of:prop:quartic`, with Poonen's smooth-variety
undecidability (credited by the manuscript). The form `x²+y²+2z²+2w²` of
Lemma 7.1 is credited to Ramanujan (1917), two-counter universality to Minsky
(1967), and Poonen's lemma is compared by variable count.

The report does **not** claim (from the manuscript's status box, Sections 6,
9, 11, 13 and 14, `RESEARCH_STATUS.md` and the delivered README):

- priority: general smooth-variety undecidability is Poonen's; the combined
  normal form is proposed as new, and its publication priority was not
  established (the source search was targeted, not exhaustive);
- any finite-fold or single-fold MRDP theorem, or a fixed-arity unique
  encoding from the bounded counter frontend (fixed arity comes only from an
  existing MRDP relation, which keeps its multiplicities);
- a decision procedure for integer, rational or dyadic equations, or
  anything about Hilbert's tenth problem over `Q`;
- a smooth proper model, smoothness of the naive projective closure, or
  density of dyadic points;
- a lower bound of five auxiliaries outside the positive weight-four guard
  architecture;
- a total-degree-four master polynomial with every input fibre relatively
  smooth (the parameter-as-coefficient presentation has total degree six);
- one source-independent diffeomorphism type of the real locus;
- semantics of the counter frontend over unrestricted integers (natural
  selectors summing to one are one-hot only over `N`; a separate domain
  encoding is required);
- that the four-square search is polynomial-time (the reference routine caps
  it at one million by default; a supplied decomposition is checked exactly);
- that the finite checks prove the general theorems, or that the code is an
  authenticated checker for edited certificates or hostile JSON;
- any improvement of the repository's 75- and 87-operation records;
- any Lean or Coq verification, repository-wide build or axiom audit.

`RESEARCH_STATUS.md` also records that an intermediate construction with
four identical guards used six additional variables; the delivered compiler
uses the weighting `(1,1,2)`.

## Relation to neighbouring reports and to the formal project

This report is in the collection's `hilbert-tenth-problem` category. It is
the only report there about the arithmetic geometry of the final equation
(smoothness over `Z`, local and dyadic points, real topology) rather than a
computational substrate. Collection labels below are cited by name; they do
not resolve in this report's PDF.

- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  the three credits above. Its Part XI classifies representations by
  polynomials nonnegative on the real orthant (`cdc:of:thm:classification`);
  the finalized `F` is never in those classes (preface: at the dyadic point
  a positive coordinate with nonzero derivative can be decreased to make `F`
  negative), and its integer-lattice positivity is a setting that report's
  README excludes from that Part's scope. Batch-79 manuscripts 02 and 03 were
  placed in the same commit for its Part XVII; 03's bounded-bit quartic is an
  ordinary sum of squares of quadratic residuals, an admissible input of the
  finalizer, while 02's exports keep power atoms.
- **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**:
  its remark "Nondegenerate minimum versus smooth hypersurface", after
  `pqc:ql:thm:hessian`, does not claim that the hypersurface of its quartic
  energy `E_C` is nonsingular. Its residuals have degree at most two, so this
  report's finalizer, with five more variables, gives a hypersurface smooth
  over `Z` with the same natural (Boolean) zeros; the price is that the
  finalized polynomial takes negative values, so its zeros are no longer
  energy minima. The two reports' statements concern different polynomials.
  (A dated note in that report is left to a separate commit.)
- **[`polynomial-witness-histories`](../polynomial-witness-histories)**
  (batch 79J1, placed in the same commit): the bounded ordinary exports of
  its manuscripts 06 and 15 are sums of squares of integer residuals of degree
  at most two, admissible inputs of the finalizer; their unbounded exports
  have polynomial-valued unknowns and are outside its setting. Manuscript 15's
  question whether one equation can have degree two or three is not answered
  here.
- **`quadratic-orthant-certificates`, `liveness-beyond-halting`,
  `group-theoretic-substrates`, `signal-machine-collision-certificates`,
  `stochastic-and-thermal-exactness`**: no shared theorem.
- **The Hilbert-tenth-problem research programme** (read-only for this
  report): the review above. The programme's "finalizer" vocabulary is about
  arithmetic-operation cost; the review found no reduction of the
  87-operation universal polynomial from this construction.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
  development confers no formal status**. The project has formalized none of
  this report's statements: its Lean development has no smoothness, Jacobian
  or finalizer module. Background it uses is formalized there in other
  forms: MRDP as `Diophantine.mrdp`, `Diophantine.mrdp_iff` and
  `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33,
  42 and 26), and the natural-to-integer four-square substitution as
  `exists_sqTerm_eq`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1978/Enumeration.lean`,
  line 227). The project README (`Computability/HilbertTenthProblem/README.md`)
  still states the 75- and 87-operation bounds; this report does not bear on
  them.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
mathtools, microtype, booktabs, array, longtable, xcolor, enumitem, listings,
fancyhdr, hyperref, xurl). The committed build has 34 pages: no errors, no
undefined references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes. The log's only box message is one
underfull line in the files table of Section 13.1, which the delivered source
already produces.

## Rerunning the programs

The suite imports `smooth_compiler` and `counter_frontend` by their delivered
names and writes `examples/countdown_T3.json`, `examples/inconsistent.json` and
`verification/results.json` relative to the parent of its own directory. Run
in place it fails at the import; **never run it in the report directory.**
Copy the three modules to a scratch directory with the delivered layout (`py`
is the Python launcher on this machine; the delivered texts say `python`):

```sh
R=SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/smooth-diophantine-finalizers
mkdir -p r13/code
for f in smooth_compiler counter_frontend verify; do
  cp $R/code/13-smooth-quartic-$f.py r13/code/$f.py; done
(cd r13 && uv run --no-project --with sympy==1.14.0 python code/verify.py)
# writes r13/examples/*.json and r13/verification/results.json
for f in countdown_T3 inconsistent results; do
  d=examples; [ $f = results ] && d=verification
  tr -d '\r' < r13/$d/$f.json | cmp - $R/data/13-smooth-quartic-$f.json; done
```

At the write (Windows, uv with Python 3.13.5 and SymPy 1.14.0) the suite
passed with 21,128 assertions in about 20 s, and all three regenerated files
equal the shipped ones. At placement, under `py` (Python 3.14.4, SymPy 1.14.0)
it took 113 s; its `results.json` differs from the shipped one only in the
recorded `"python"` version, and its two exports were written with CRLF line
endings and equal the shipped LF files after stripping carriage returns,
hence the `tr` above. The programme's review replays the original archive in
an isolated extraction with its own helper.

## Discrepancies and disclosures

- The shipped `code/13-smooth-quartic-Makefile` keeps the delivered layout:
  `make test` runs `python code/verify.py`, `make pdf` runs pdflatex three
  times on `article.tex` from the package root, and `make clean` deletes
  `article.aux`, `.log`, `.out`, `.toc`, `.fls` and `.fdb_latexmk` in the
  current directory. Do not run it here; use the build command and the rerun
  recipe above.
- Delivered names in shipped and printed text: the article's Section 13 and
  Appendices A–B, `RESEARCH_STATUS.md` and the Makefile name
  `code/verify.py`, `requirements.txt`, `examples/…` and
  `verification/results.json`; Section 13 also says that the archive contains
  a compiled PDF and an execution report, which are not shipped. `[write]`
  notes in Section 13 and Appendix B give the shipped names.
- `data/13-smooth-quartic-document_qa.json` describes the delivered 28-page
  PDF (size, rendering review), not this report's 34-page PDF.
- `13-smooth-quartic-SOURCE_AUDIT.md` names four repository files read
  through a GitHub connector; all exist at the write, and the two blobs it
  records (`bc4c514b61e3` of `README.md`, `e768b2284c67` of the
  canonical-certificates status file) are unchanged.
- Corollary 9.4 displays `w_j > 0`; `w_j ∈ Z_{>0}` is meant, as in the
  weighted family of Section 9. A `[write]` note says so and that the
  corollary does not assume the normalization `w_1 = 1` of Theorem 9.1.
- The title "Smooth Everywhere" and the phrase "smooth at every prime" refer
  to the affine model only, as Sections 6 and 14 state.
- Layout: the title page's top space was reduced from 16 mm to 2 mm so that
  the added `[write]` status sentence stays on that page; the package `xurl`
  was added for line breaks in long paths. No other change to the
  manuscript's text or layout beyond the `[write]` material and the label
  prefix.
- AI wording kept as delivered: "Developed with ChatGPT" on the title page,
  "Research prepared for Vladimir Reshetnikov with ChatGPT" in the PDF
  metadata.
- The archive ships no licence file; the repository's MIT-0 default applies to
  the delivered text and code. Poonen's paper is cited, not redistributed.
