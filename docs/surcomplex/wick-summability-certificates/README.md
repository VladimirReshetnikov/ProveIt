# Finite Certificates for Surcomplex Wick Summability

**Valuation balancing, connected obstructions, and multiscale Gaussian perturbations**
Single-source research report, 22 September 2026, built from one manuscript
(number 12 of batch 18) whose repository audit is pinned at `4cf691c`.
An AI-assisted draft: not refereed, and not checked in Lean or any other proof
assistant.

```
article.tex         the report, standalone LaTeX with an internal bibliography
article.pdf         the compiled report, 31 pages (title, contents, 29 numbered pages)
README.md           this guide
VERIFICATION.md     the source's verification record, as delivered
RESEARCH_AUDIT.md   the source's novelty and repository audit, as delivered
code/               wick_certificates.py  exact certificate solver
                    verify.py             the finite checks
                    Makefile              optional targets; run from the report root
data/               verification.json, the recorded run (7,684 passing cases)
```

Every label in `article.tex` carries the prefix `wick:`. The manuscript arrived
with unprefixed labels, two of which (`thm:main`, `thm:positive`) are also
used by other manuscripts of the same batch. All 83 delivered labels survive
with the prefix; 8 subsection labels were added. No label of any other report
was touched.

This is not a merge. There was one manuscript, and nothing was selected out of
a larger body of work. The programs, the recorded run, `VERIFICATION.md` and
`RESEARCH_AUDIT.md` are byte-identical to the delivery. The delivered
`Makefile` was moved from the package root into `code/`. The delivered README
and PDF are not shipped; the PDF here is rebuilt from `article.tex`.

## What the report is about

Let `Γ ≠ 0` be a set-sized **divisible** ordered abelian group, of arbitrary
rank, and `K = C((t^Γ))`. Take a finite polynomial interaction
`P = Σ_a g_a x^(α^a)` with `g_a ∈ K^×` and `α^a ∈ N^d \ {0}`, and a symmetric
covariance matrix `C` over `K`. The covariance is bilinear, not Hermitian, may
be singular, and need not be real or positive. Write `λ_a = v(g_a)` and
`c_ij = v(C_ij)`; zero entries are omitted.

Formally expanding `E_C[x^β e^P]` gives an infinite family of Wick diagram
terms. The question is for which actual couplings and covariances this family
has a well-defined, order-independent Hahn sum. Here `E_C` is a finite sum over
pairings: no measure or integral is involved.

## What the report claims

Numbers are those of the build in this directory.

- **Theorem 6.1 (`wick:thm:main`), the exact diagramwise domain.** The
  following are equivalent:
  1. the vacuum Wick family is strongly summable;
  2. the weight `L` is positive on every nonzero element of the integer
     incidence semigroup `S = {(m,k) : Am = Dk}`;
  3. `L` is positive on the finite Hilbert basis of `S`;
  4. there is `p ∈ Γ^d` with `λ_a + α^a·p > 0` for every interaction type and
     `c_ij − p_i − p_j > 0` for every nonzero covariance entry;
  5. every observable sector is strongly summable.

  Summability of any one pairable sector is already equivalent to these
  conditions. Arbitrary Hahn-unit tails are allowed. So the answer is a
  **finite system of strict valuation inequalities**. Condition 4 says that the
  **diagonal monomial change of variables** `x_i = t^(p_i) y_i` makes every
  coupling and every nonzero covariance entry infinitesimal.
- **Theorem 5.1 (`wick:thm:alternative`).** A strict rational theorem of the
  alternative over any divisible ordered group, of any rank, proved by
  Fourier–Motzkin elimination without real separation.
- **Corollaries 6.2 and 6.3.** If balancing fails, a **finite nonnegative
  integer certificate** `q ∈ S \ {0}` with `L(q) ≤ 0` exists, and an
  indecomposable one can be chosen. Its multiples form an explicit infinite
  obstruction: leading exponents that descend, or infinitely many terms at one
  exponent. The domain is unchanged by same-valuation replacements and by
  diagonal monomial changes of variables.
- **Theorem 7.3 (`wick:thm:connected`).** When every interaction vertex has
  valence at least 2, the **connected vacuum diagrams** have exactly the same
  domain. Every obstruction is realized by connected diagrams of every multiple
  size, through cyclic rewiring of a non-bridge edge (Lemma 7.2). Example 7.5
  shows that valence 1 breaks this. On the domain, `log Z` equals the summed
  connected family (Proposition 7.4).
- **Theorem 8.2 (`wick:thm:positive`).** For **positive-definite real
  covariance** (ordered-field positivity over `R((t^Γ))`), or for any diagonal
  covariance with nonzero diagonal, the criterion reduces to one inequality per
  interaction monomial, `λ_a + ½ Σ_i α_i^a c_ii > 0`. An explicit balancing
  vector is given. The key step is a valuation Cauchy–Schwarz inequality
  (Lemma 8.1).
- **Corollary 8.3 (`wick:cor:stationary`), the multiscale stationary-phase
  condition.** For `S(x) = ½ Σ q_i x_i² + Σ u_a x^(α^a)` with all degrees at
  least 3, the normalized expansion is summable exactly when
  `v(u_a) + (|α^a|/2 − 1) v(ħ) − ½ Σ_i α_i^a v(q_i) > 0` for every `a`. The
  strict boundary cannot be relaxed to `≥`.
- **Theorem 9.2 (`wick:thm:SD`).** Exact perturbative Schwinger–Dyson
  identities hold on the domain, with no invertibility assumption on `C`.
  Proposition 9.3 is a valuation bound on truncation errors. Example 9.4 shows
  that in rank two it does not imply convergence of the truncations.
- **Explicit models (Section 10).** The quartic series (10.1) has ordinary
  radius of convergence zero but an exact Hahn value whenever `v(g) > 0`. An
  infinite coupling (negative valuation) can be admissible (Section 10.2).
  **Proposition 10.1** gives the four-element Hilbert basis and irredundant
  tests of the mixed quartic. In model (10.6) each quartic interaction alone
  is admissible but `w_4 = −2`. This **mixed instability** is invisible to the
  individual interactions. Section 10.4 gives a rank-two boundary that no
  real-valued first coordinate can decide.
- **Cancellation (Section 11).** In the isotropic example `C = I_2`,
  `P = t^(−1)(x + iy)^4`, grouping by interaction order gives the sum 1 while
  the diagram family is not summable. Complex cancellation can therefore evade
  any criterion for the ungrouped family. For sign-coherent data, grouping and
  the raw family are equivalent (Proposition 11.1).
- **Surreal transfer.** Through a chosen order embedding `Γ ↪ No`, the values
  land in `No[i]` as normal forms (Proposition 2.4).
- **Software.** `code/wick_certificates.py` solves the strict balancing
  problem exactly over `Q^r` with lexicographic order. It returns a balancing
  vector or a primitive integer obstruction, and rechecks either one against
  the original system. Appendix A shows how to check a certificate without
  trusting the solver.

## What the report does not claim

These are the source's own limitations, kept in full (Sections 1.2, 11, 12 and
13 of the article and the two delivered audit files).

1. **Classical inputs are credited, not claimed.** These are Wick's pairing
   formula, the connected-diagram logarithm (Etingof, Chapter 3), formal
   stationary-phase degree counting, Neumann's support lemma, Dickson's lemma
   and Fourier–Motzkin elimination (Table 2). The theorem package is a
   **candidate** contribution, and its priority is **provisional**. The
   literature search was targeted and did not include an expert review.
2. **Diagramwise only.** The theorem is about one prescribed monomial
   presentation and its Wick pairings. Cancellation-aware regroupings are not
   classified; the isotropic example shows they can be legal where the diagram
   family is not. The criterion is invariant under diagonal monomial changes
   but **not under general complex linear changes of coordinates**.
3. **The connected-domain equality needs valence at least 2** (Example 7.5).
4. **Finite-dimensional, finitely many couplings.** No field modes, no
   ultraviolet divergence, no renormalization, no path measure, no
   nonperturbative completion. The criterion does not by itself extend to
   infinitely many couplings or covariance entries.
5. **Strong summability is not convergence.** It is not analytic convergence,
   not Borel–Laplace summability, and not convergence of truncations in higher
   rank. A Hahn value is **not the integral of a Gaussian function over a
   surreal line**. The surreal value depends on a chosen embedding, with
   set-sized supports and no proper-class sum.
6. **No physics.** The source proposes no resolution of a spacetime
   singularity, no new measure theory and no solution of physical
   divergences. The Schwinger–Dyson identity is an algebraic identity, not an
   integration theorem for a measure. `∂_j` is formal differentiation in
   `x_j`, not the Berarducci–Mantova derivation.
7. **Software limits.** Only finite-rank `Q^r` with lexicographic order is
   implemented. Valuations and the nonzero pattern must be supplied; the code
   reads no Hahn series. It does not enumerate Hilbert bases and is not a Hahn
   or surreal CAS. Fourier–Motzkin elimination can be exponential, so the solver
   has a **resource guard** (`max_rows`, default 200,000 generated rows). Hitting
   it raises `RuntimeError`, which is not an infeasibility certificate. The test
   suite exercises the cyclic rewiring only on three base multigraphs, not the
   whole refinement pipeline of Section 12.2.
8. **The finite checks are checks.** The 7,684 cases test formulas and the
   implementation at ranks 1, 2 and 3. They do not prove the infinite or
   arbitrary-rank statements.
9. **No Lean, no refereeing.** No existing Lean coverage in the repository
   covers this report.
10. The three follow-on questions of Section 14 are **posed here**, not claimed
    to be established open problems.

## Corrections to the source's repository statements

The source audited the repository at `4cf691c7d951e037739d32d9f5c387dcce724f3c`.
Its statements are kept as provenance, and the article (Sections 13.1 and 13.5)
corrects them for the present tree:

- **"Searches for Wick and Gaussian returned no matches."** This is true for
  *Wick*. The only case-insensitive match is inside *Entwicklung*, in a
  nonabelian-support bibliography entry. It is **false for Gaussian**: at the
  pin, the word occurs in 20 files. In the physics report it names a Gaussian
  regulator (Computation 17.5 there, `phys:comp:gaussian`). Everywhere else it
  names Gaussian-rational arithmetic or Gaussian elimination. None of these
  occurrences concerns Gaussian perturbation expansions, so the gap the source
  identified is real. `RESEARCH_AUDIT.md` still carries the original sentence.
- **"The 18 ZIP archives in `docs/new` could not be opened."** They have since
  been unpacked and placed in the collection. None of their texts mentions Wick.
  In them "Gaussian" means only Gaussian rationals.
- **"The catalogue lists 26 reports."** True at the pin; the collection has grown
  since.

`VERIFICATION.md` says the PDF has 27 pages. That was the delivered build. The
build here has 31 pages because of the material added on placement: Sections
1.3, 13.4 and 13.5, the correction in Section 13.1 and the notes in Section
12.3. The numbers cited by the two delivered files (Section 13 and Appendix A)
are unchanged.

## Relation to the neighbouring reports

**[Surreal scalars and spacetime](../../physics/surreal-scalars-and-spacetime/)**
(the physics report). That report separates exact identities, conditional
theorems and assessments, and none of its statements is used here. Its passages
on perturbative families are **cautions, not open problems**:

- Section 17.2 (`phys:sub:formalpert`) warns that an arbitrary triple-indexed
  family is not automatically admissible, and its non-claim N21 repeats this.
- Computation 17.1 (`phys:comp:factorial`) shows that a factorial series is an
  exact Hahn element despite zero radius of convergence.

For one precisely delimited class, finite polynomial Gaussian models over
`C((t^Γ))` with divisible `Γ`, this report decides admissibility exactly. The
mixed quartic is a concrete family that fails the test. The quartic example
(10.1) is the Wick counterpart of that Computation 17.1. That report says exact
denotation gives no real-valued sum; this one says its value is a normal-form
value, not an integral. This report answers none of the physics report's
questions and changes none of its assessments. Its result says nothing about
that report's schematic transseries display, or about physics. Section 13.4 of
the article gives the full statement.

**[Hahn–Tate uniformization](../hahn-tate-uniformization/).** The multiscale
theta series in several variables, placed there in the same batch, is the
closest relative. Both reports characterize strong summability of a monomial
family indexed by a lattice or semigroup through a finite certificate. Both
allow unit tails, and both assume divisible `Γ`. The mathematics differs, and
neither report uses a theorem of the other: there, a quadratic energy with
radical flags; here, a linear weight on an integer semigroup, with its Hilbert
basis and the strict alternative.

**Words that change meaning between reports.** Section 1.3 of the article fixes
the meanings used here. *Gaussian* means the formal Wick expectation. A
*moment* is a Wick moment, not a measure moment. *Positive* is ordered-field
positivity. A *Hilbert basis* is a semigroup basis. The *cone* and
*admissible* are those of Theorem 6.1. `D` is an incidence matrix.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build in this directory has zero errors and zero warnings: no undefined
references or citations, no multiply defined labels, no duplicate PDF
destinations, and no overfull or underfull boxes. It needs pdfLaTeX with
standard packages, including TikZ and `listings`, and no external
bibliography, figures or fonts.

**Run the checks on a copy of this directory**, never in place. `code/verify.py`
always writes `data/verification.json` in the directory that contains its own
`code/` folder, whatever the working directory. That file records
`elapsed_seconds`, so every run rewrites the delivered record.
From the root of the copy:

```sh
python3 code/verify.py               # the 7,684 finite checks; rewrites data/verification.json
python3 code/wick_certificates.py    # prints the mixed-quartic obstruction (1, 1, 0, 4, 0)
make -f code/Makefile check          # the same as the first line
make -f code/Makefile pdf            # builds the article with latexmk
```

The checks need Python 3.10 or later and only the standard library. Do not run
them with `python -O`: the certificate rechecks are `assert` statements. To
call the solver from your own code, put `code/` on the import path (Section 12.1
has an example). Edge indices are zero-based, and a zero covariance entry is
specified by omitting the edge.

When this report was placed, the suite was rerun on a copy under Python 3.14.4.
It passed all 7,684 cases. The rewritten record matched the delivered one in
every entry except `elapsed_seconds`: 0.632 s recorded, 1.592 s on rerun.
