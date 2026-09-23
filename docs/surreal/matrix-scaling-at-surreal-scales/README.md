# Sharp Matrix-Scaling Stability over Surreal and Surcomplex Fields

**Spanning-tree gaps, infinitesimal normalization, and exact multiscale propagation**
Single-source research report, 22 September 2026, built from one manuscript
(batch 19, number 09, archive `surreal_matrix_scaling`). Prepared for
Vladimir Reshetnikov. An AI-assisted research draft, not refereed. The
[formalization ledger](../../FORMALIZATION.md) inventories its 16 standard
statements but gives none a Lean Implementation mapping; this review adds
no Lean coverage.

This directory holds one manuscript. It is not a merge. There was no second
source, and nothing here was selected out of a larger body of work.

```
article.tex        the report, standalone LaTeX with an internal bibliography
                   (delivered as surreal_matrix_scaling.tex, renamed on placement)
article.pdf        the compiled report, 33 pages
README.md          this guide
PROOF_AUDIT.md     the manuscript's own proof-dependency and self-review record, as delivered
SOURCE_AUDIT.md    the manuscript's own repository and literature audit, as delivered
code/verify.py     exact finite checks (Python and SymPy)
code/build.sh      the manuscript's build script, as delivered; does not work as placed
data/verification.json          recorded output of code/verify.py
data/verification_console.txt   console record of that run
data/build_validation.json      the manuscript's own build record, as delivered
data/final_build_console.txt    console record of that build
data/requirements.txt           the SymPy pin, as delivered
```

`PROOF_AUDIT.md`, `SOURCE_AUDIT.md`, everything in `code/` and everything in
`data/` are byte-identical to the delivered files. `build.sh` was delivered at
the top of the package and `requirements.txt` next to it. On placement they
moved to `code/` and `data/`. The delivered PDF and README are not shipped.

Every label in `article.tex` carries the prefix `scale:`. There are 94 labels:
the manuscript's 88, which already carried the prefix and are unchanged, and 6
added during assembly. None was dropped. No label of any other report was touched.
The added material was inserted so that every theorem, equation and section
number of the manuscript is unchanged, so the theorem numbers quoted in
`PROOF_AUDIT.md` still apply. The numbers below are checked against the build
of `article.tex` in this directory.

## What the report claims

**Setting.** `Γ` is any set-sized ordered abelian group: not necessarily
divisible, Archimedean, discrete, countable or of finite rank. `F = R((t^Γ))`,
`K = C((t^Γ))`, `v` is the least exponent of the support, and `𝔪` is the ideal
of positive-valuation elements of `K`. A finite matrix is positive on a fixed
support, which is a connected bipartite graph `G` with edge set `E`. The base
weights `p_e` may be surcomplex provided each is **positive-leading**: its
leading coefficient is a positive real number (Definition 3.1). The cost of an
edge is `c_e = v(p_e)`. Let `τ` be the least total cost of a spanning tree,
`τ_e⁻` the least cost of a spanning tree avoiding `e`, and
`κ_e = τ_e⁻ − τ` the **spanning-tree deletion gap**; a bridge has `κ_e = +∞`.
A perturbation `f ∈ 𝔪^E` changes the kernel to `p_e exp(f_e)`, and the
normalization restores the original row and column sums. The surreal and
surcomplex forms come through the normal-form embedding `t^γ ↦ ω^(−γ)`.

1. **Weighted tree interpolation** (Theorem 4.1, `scale:thm:tree`). For the
   reduced incidence matrix `B`, `det(B W_p Bᵀ)` is the positive tree sum
   `Z(p)`, and the weighted cut projection `Π_p` is the tree-weighted average
   of the tree interpolation matrices, whose entries are `0` and `±1`. So
   `Π_p` and `H_p = I − Π_p` have integral entries, and
   `(H_p)_ee = Z_e⁻(p)/Z(p)` has valuation `κ_e` (equation 4.6).
2. **Normalization on the whole relative infinitesimal polydisc** (Theorem 5.1,
   `scale:thm:existence`). For every `f ∈ 𝔪^E` there is exactly one
   infinitesimal solution. It is the strong evaluation of a unique formal
   series whose coefficients lie in the finitely generated algebra
   `C[(Π_p)_ab]`, with no lower bound on the entries, no rank-one hypothesis and
   no divisibility. The row and column factors can be taken in `1 + 𝔪`, and the
   map is a retraction onto the balanced set (Corollary 5.2). The
   finite-generator evaluation lemma (Lemma 3.4) is what licenses evaluation at
   arbitrary rank; Example 3.5 shows that integral formal coefficients alone
   do not.
3. **The sharp nonlinear tree-gap law** (Theorem 6.2, `scale:thm:sharp`). For
   any two perturbations `f ≠ g` with `δ = min_a v(f_a − g_a)`, the normalized
   entries satisfy `v(q(f)_e/q(g)_e − 1) ≥ δ + κ_e`. A bridge entry is fixed
   exactly. For a nonbridge and a change in entry `e` alone, equality holds and
   the leading coefficient is the positive real ratio `C_e` of minimizing-tree
   amplitudes (equation 6.3), with ties allowed and complex perturbations
   allowed. The proof is an exact secant identity (Lemma 6.1). So `κ_e` is the
   largest uniform gain when `Γ ≠ {0}`; a particular direction can gain more
   (Remark 6.3). For the trivial group, the evaluated domain is a singleton;
   the formal coefficient sharpness below still holds.
4. **Every Taylor order** (Theorem 6.4, `scale:thm:coeffgain`). At entry `e`,
   every positive-degree Taylor coefficient of the logarithmic response and of
   the relative output has valuation at least `κ_e`, at every centre. For a
   nonbridge the coefficient of `X_e` has valuation exactly `κ_e` and leading
   coefficient `C_e`. Corollary 6.5 is a remainder certificate `κ_e + (D+1)δ` for truncation at degree `D`.
5. **The gain without enumerating trees** (Theorem 7.1,
   `scale:thm:bottleneck`). `κ_e = max(0, b_e − c_e)`, where `b_e` is the
   minimax cost of a path joining the ends of `e` without `e`.
6. **Exact propagation along a chain** (Theorem 8.1, `scale:thm:chain`). For
   a tridiagonal bistochastic matrix with link valuations `γ_i` and a change of
   valuation `δ` in the last diagonal kernel entry, every entry's relative
   change has an exact valuation, `δ` plus a sum of consecutive link
   valuations (equations 8.2–8.4): the gains add along the chain. This holds
   for the nonlinear solution, not only for its linearization. Section 8.3 is
   a rank-two example in lexicographic `Z²`.
7. **The usual positive normalization is the local branch** (Section 9). If the
   margins have a feasible witness positive on every support edge, every positive
   kernel on that support has a unique normalized matrix over a real closed field
   (Proposition 9.1, by real scaling and first-order transfer). On connected
   support its factors are unique modulo a common reciprocal gauge. Proposition 9.2 is a
   finite cut bound `η^(−N) ≤ P'_e/P_e ≤ η^N`. For divisible `Γ`, Corollary 9.3
   identifies the positive normalization of a relatively infinitesimal
   perturbation with the branch of Theorem 5.1, with tree costs taken from the
   normalized base matrix.
8. **Real linear constraints** (Theorem 10.1, `scale:thm:linear`). For a real
   constant full-row-rank `B`, the same results hold with spanning trees
   replaced by column bases, each basis weighted by `(det B_T)²`.
9. **No new exponents locally, ramification globally** (Section 11).
   Corollary 11.1 keeps the local normalization in `C((t^Λ))`, `Λ` the group
   generated by the input supports. Equation 11.1 is a `2 × 2` matrix over
   `R((t^Z))` whose bistochastic scaling needs `t^(1/2)`. Section 11.2
   transports everything to finitely many surreal or surcomplex entries by
   set-sized support-group localization.
10. **Boundaries** (Section 12). A closed-form `2 × 2` example with its exact
    gaps; without positive leading coefficients, a formal derivative of
    valuation `−β` (Example 12.1) and two distinct infinitesimal solutions
    (Example 12.2); failure of bridge rigidity when the margins move (12.3);
    and a rank-two exponential that is not the limit of its Taylor sums (12.4).

## What the report does not claim

These are the manuscript's own limitations. Each is stated where it applies,
and all are collected in Section 1.4 as (N1)–(N12).

- **Priority is not certified.** The whole-polydisc normalization, the sharp
  tree- and basis-gap laws and the chain formulas are **candidate original**
  results after a targeted, non-exhaustive comparison. No named open problem is
  claimed solved. The repository audit was not a line-by-line review, and its
  indexed searches were unusable as negative evidence. The ledger has no
  Implementation mapping for these results; Section 13.2's outline of Lean
  modules does not assert that they exist.
- **Credited, not claimed:**
  - existence, uniqueness and real continuity of scaling (Idel's review);
  - generalized-series expansions for a one-parameter scaling problem, so no
    first use of Hahn-type series in matrix scaling (Sharify–Gaubert–Grigori);
  - the first-order implicit differentiation formula (Eisenberger et al.);
  - the determinant formula, its tree interpretation and transfer currents
    (Burton–Pemantle);
  - the minimax path formula and minimum-spanning-tree exchange arguments;
  - Hahn and surreal background (Gonshor, Berarducci–Mantova), Higman's theorem
    and real-closed transfer (Tarski).

  Theorem 10.1 claims no new matroid combinatorics.
- **No convergence claims.** Not for the alternating Sinkhorn iteration in an
  arbitrary-rank valuation topology, not for its complexity, and not for
  set-indexed sequences in the surreal fine topology. Strong summability alone
  does not imply convergence of partial sums. The remainder certificate does not promise that finite
  Taylor degree reaches every precision at higher rank.
- **"Analytic"** means given by a strongly evaluated formal series on the
  relative infinitesimal polydisc; no classical holomorphic structure in the
  fine topology is claimed. No exponential or logarithm at an infinite
  argument, no global surcomplex exponential and no surreal derivation is used.
- **The hypotheses matter.** Positive leading coefficients are sufficient, not
  claimed necessary. Margins and support are fixed. `K` is not ordered;
  "positive-leading" concerns only the leading coefficient.
- **Sharp** means the largest uniform gain over infinitesimal inputs when
  `Γ ≠ {0}`, not equality in every direction. Formal coefficient sharpness also
  holds for the trivial group. Optimality of the exponent `N` in Proposition 9.2 is not claimed.
- The tree costs are those of the **normalized** base matrix. No equally sharp
  formula from the valuations of an unscaled kernel is claimed.
- **Divisibility.** The local theory needs none. Only the global positive
  interpretation (Proposition 9.1, Corollary 9.3, the global part of
  Section 11.2) uses real closedness, via the divisible hull and transfer. The
  descent statement is local; global scaling can ramify.
- Theorem 10.1 needs a **real constant** constraint matrix.
- Surreal statements use set-sized localization only: no class-sized sums,
  nets or compactness, and no spherical completeness or Banach contraction.
- **Computation.** The workflow is an exact-operation specification, not a
  uniform algorithm on arbitrary surreal names. The finite checks do not prove
  strong summability, arbitrary-rank existence or surreal transport, and
  compilation is not a proof check.
- **Open.** The three questions of Section 13.3: sharp two-edge propagation on
  a general support graph (the chain theorem settles one family); which
  surcomplex base weights keep a unique integral branch; and convergence and
  complexity of alternating normalization over higher-rank valued fields,
  with a global surcomplex scaling theorem for arbitrary complex kernels.

## Words used differently elsewhere

Section 1.6 of the article fixes these once. In prose that spans several
reports, use the plain names given here.

- *Scaling* and *normalization* are diagonal row and column scaling to
  prescribed margins. *Scale* in the title means a valuation.
- *Positive* matrix means entries positive on the support; *positive-leading*
  is the only positivity notion in `K`. Neither means positive definite.
- *Gap* is the spanning-tree deletion gap `κ_e`: not a spectral gap and not a
  surreal gap. `κ` is unrelated to the Prony report's moment precisions `κ_k`
  and to `κ = v(q)` in expanding polynomial dynamics.
- *Tree* is an undirected spanning tree of the support graph, not a Markov
  in-forest or a cluster, separation or splitting tree.
- *Branch* is the unique relative-infinitesimal solution; it is neither a
  germ-analytic class of the analysis report nor a computational branch selector.
- `q` are normalized weights (rates in the Markov report); `L_p = B W_p Bᵀ` is
  a symmetric reduced Laplacian (not a row Laplacian); `H_p` is a projection
  (not a Hermitian `H`); `Π_p` is not the Hahn–Tate theta exponent matrix `Π`.
- The formal series of Lemma 3.4 and Example 3.5, written `F(X)` in the
  manuscript, is `Φ(X)` here, so that `F` is always the real Hahn field.

## Relation to the neighbouring reports

**`surreal/markov-generators-at-every-scale`.** Shared: the mechanism by which a
positive tree or forest sum has the minimum cost as its valuation and the sum
of minimizing amplitudes as its leading coefficient. There it is applied to
directed in-forests (Proposition 3.1 there, `markov:prop:forest`; equation 3.10
there); here to undirected spanning trees (Theorem 4.1). In both reports an
entry's valuation is a restricted minimum minus the unrestricted one: forests
with a prescribed root there (Theorem 4.1 there, `markov:thm:leading`), trees
avoiding `e` here (`κ_e`). For symmetric rates on the support graph, that
report's top forest coefficient `σ_(N−1)` equals `N · Z(p)`; this report does
not use the identity. Not shared: that report studies the linear-fractional
normalized resolvent of a generally nonsymmetric row Laplacian at every scale
parameter, with forests of every size. This one studies a nonlinear
fixed-margin normalization with spanning trees only. Its stability theorem
(Theorem 8.1 there, `markov:thm:stability`) gives relative errors `≥ δ` and no
gain in general (Example 8.3 there). Theorem 6.2 here gives `≥ δ + κ_e`,
exactly, because the margins are fixed. The two theorems concern different
maps and neither implies the other. That report assumes a divisible value
group and real rates; the local theory here assumes neither.

**`surcomplex/spectral-theory`.** Shared:
- positive Cauchy–Binet sums with no leading cancellation (Theorem 8.1 there,
  `thm:gram`, for Gram determinants; Theorems 4.1 and 10.1 here). For real
  positive weights with square roots, `det L_p` is the top Gram coefficient of
  that theorem. The proof here needs neither square roots nor real weights, and
  the projection identity (4.3) has no counterpart there.
- the support engine. Lemma 3.3 here and Lemma 9.4 there (`spec:lem:neumann`)
  are the same statement, both from Higman's theorem. Lemma 3.4 with no
  generators gives the strong evaluation of Lemma 9.5 there
  (`spec:lem:evaluate`); the finitely many generators in `𝒪` are this report's
  addition, and Example 3.5 shows they cannot be arbitrary. The rank-two
  warning (Example 9.2 there) uses a geometric series; Section 12.4 here uses
  an exponential with the same obstruction to convergence of Taylor sums.
- descent without new exponents (Theorem 9.18 there, `spec:thm:svd`;
  Corollary 11.1 here). The ramification example (11.1) here is computed
  directly, not from that report's Section 10.

Not shared: that report's eigenvalues, singular values, Hermitian and normal
matrices, and eigenvalue perturbation bounds (Theorem 5.2 there, `thm:weyl`).
No eigenvalue or singular value appears here, and `κ_e` is not a condition
number. Both reports keep their own proofs.

**`surcomplex/prony-reconstruction-at-surreal-scales`.** Its nonuniform
certificate (Theorem 8.1 there, `prony:thm:graph`) is also a minimum-cost path
computation in an ordered group, on a directed graph of moment interactions.
It requires positive cycle weights and strict-ball inequalities
`ρ_i − E_i > δ_i` for every `i`; these are sufficient conditions in that
report's notation. It involves no spanning trees and no normalization.

These comparisons were added during editorial assembly at `ed88b8f` and
rechecked against the source labels at `034ab96` during the main-text review.
Historical searches below still describe their original snapshots.

## Stale repository statements, corrected

The manuscript's audit is pinned to `048b72c`. The article keeps the pin as
provenance; editorial assembly added a "Since the pin" paragraph to Section
2.2. Its catalogue and search observations describe the raw-placement
snapshot, `30dfb4f`.
`SOURCE_AUDIT.md` is kept as delivered, so it still describes the repository at
the pin.

- *"The complete research catalogue `docs/README.md` at that pin lists 36
  reports."* It still did at raw placement, `30dfb4f`, when it did not yet
  list this report or the three others placed with it.
- *"The directory `docs/new` at the pin contains only its README."* True at the
  pin. Commit `330aa79` then added nine archives, this one among them, and
  `30dfb4f` placed and removed all nine.
- *"Searches for `Sinkhorn` and `spanning` returned no results"* (with an
  unreliable index). At `30dfb4f`, a full-text search of every LaTeX source
  finds `Sinkhorn`, `bistochastic`, `Kirchhoff` and `transfer current` only in
  this report. `spanning tree` occurs once elsewhere, in the Markov report's
  proof of the matrix-forest identity. `matrix scaling` occurs once elsewhere, in
  the Prony report's Lean outline, in another sense. No Lean source mentions
  Sinkhorn scaling, spanning trees or Kirchhoff's theorem.
  `Surreal/Algebra/MarkovResolvent.lean`, the audit's positive control, is still
  present and contains no tree, forest-sum or Cauchy–Binet statement.
- Appendix B said that `build.sh` works from anywhere and that the source is
  `surreal_matrix_scaling.tex`. It now gives the commands for this directory
  and says the script does not work as placed.

Editorial assembly also fixed one typesetting defect. All numbered statements
share one counter, and the delivered build called every referenced lemma, corollary,
proposition, definition, example and remark a "theorem". Six preamble lines now
give each reference its right name. No number changed.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

This build of `article.tex` gives 33 pages (a title page, two contents pages
and 30 numbered pages). It has no errors, no undefined or multiply-defined
references or citations, no duplicate PDF destinations, and no LaTeX, package
or box warnings. The source needs no external figures and no bibliography
database.

`code/build.sh` is kept as delivered, and **it does not work as placed**. It
changes into its own directory (`code/`), then runs `code/verify.py` and builds
`surreal_matrix_scaling.tex` from there, and neither exists at that location.
Use the `latexmk` command above instead. The delivered record in
`data/build_validation.json` (26 pages, pdfTeX from TeX Live 2025/dev) and
`data/final_build_console.txt` describe the manuscript's own build, before the
material added during assembly.

`code/verify.py` **overwrites `data/verification.json`**, since it writes to
`../data/` relative to its own location. Run it on a copy of this directory:

```sh
# from docs/surreal/; any scratch location will do
cp -r matrix-scaling-at-surreal-scales /tmp/scale-check
cd /tmp/scale-check
python -m pip install -r data/requirements.txt              # SymPy 1.14.0
python code/verify.py
```

The program uses exact integers, rationals and rational functions in SymPy, a
fixed seed (`20260922`), no floating point and no network. It stops with an
assertion error if a check fails, and refuses to run under `python -O`. The
recorded run (Python 3.13.5, SymPy 1.14.0) reports `PASS` for:

- tree interpolation and projection identities on 60 connected bipartite
  graphs, a fixed-seed sample: 348 spanning trees and 2,056 projection-matrix
  entries;
- the deletion gap against the bottleneck formula of Theorem 7.1 on all 229
  connected spanning subgraphs of `K_{2,2}`, `K_{2,3}` and `K_{3,3}`, with
  costs in `Z` and in lexicographic `Z²`: 458 instances, 2,612 edges, of which
  1,266 are bridges and 421 have gap zero;
- the formal normalization recurrence: two constant-weight examples through
  degree 7 and two Laurent-weight `2 × 2` examples through degree 6
  (conservation, cut condition, coefficient gains);
- chain inverse valuations for sizes 2 to 6 (55 entries) and three exact
  identities for the closed-form `2 × 2` example.

A rerun on a copy during assembly took about twenty seconds under Python 3.14.4
and SymPy 1.14.0. It reproduced the recorded file except for the Python
version field and the line endings the operating system writes. The console
record `data/verification_console.txt` prints the path of the original run's
environment. The main-text review reran the unchanged suite under Python
3.13.14 and SymPy 1.14.0 on a scratch copy; every group passed, and the JSON
matched except for the Python version. These finite checks do not prove the
general theorems or add Lean coverage.

## Provenance

The source is one manuscript, *Sharp Matrix-Scaling Stability over Surreal and
Surcomplex Fields*, dated 22 September 2026. It arrived with the nine archives
committed as `330aa79`. Raw source placement is commit
`30dfb4f5b794818315af63ab6f4215337e68dec8`; editorial assembly and addition
of the first report PDF followed in its child commit
`ed88b8f6a3901d4cbcf8e4249673161f493f679b`.
Its repository comparison is pinned to
`048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`. With one source there
were no merge decisions. Every theorem, proof, example and disclaimer is kept.

Raw placement renamed the source `article.tex` and moved `build.sh` to
`code/` and `requirements.txt` to `data/`. Editorial assembly then made the
following changes, recorded in Section 1.7 of the article:

- It added Sections 1.4 (non-claims), 1.5 (neighbouring reports), 1.6 (words)
  and 1.7 (provenance), and Remarks 3.6 and 4.2, which point to the spectral
  and Markov reports.
- It added the "Since the pin" paragraph (Section 2.2), a rerun note
  (Section 13.1), and build instructions for this directory (Appendix B). It
  also added the draft status to the title page and an assembly note to the
  two repository bibliography entries.
- It renamed the formal series `F(X)` to `Φ(X)` and fixed the cross-reference
  names.

The assembly changes left the mathematics unchanged. The provenance correction
distinguished the two verified commits. The subsequent main-text proof review
is recorded below; `PROOF_AUDIT.md` remains the manuscript's own self-review,
not an independent referee report.

## Main-text proof review

Sections 1–14 and the dependency appendix have received a mathematical
review. The proof expansions make composition evaluation, complementary
projections, formal unit inversion, recentering, minimum-tree replacement,
chain base cases, strict feasibility and normalized factor ratios explicit.
The real-constraint extension includes zero columns, coloops and the empty
constraint system, with a counterexample showing why Hahn-valued constraint
minors cannot be omitted from costs.

The scope corrections distinguish formal tangent spaces from evaluated
infinitesimal domains, require a nontrivial group only for evaluated
optimality, and separate strong summability from convergence. The two
published comparison citations now point to Idel's Theorem 4.5 and
Sharify–Gaubert–Grigori's Theorem 2.4 in the named versions. Their settings,
the implicit-differentiation comparison and transfer-current background were
checked against primary sources. Other foundational imports, original-source
reconciliation and priority remain separate obligations. See
[the review record](../../REVIEW.md). All nine historical audit/code/data
files are preserved.
