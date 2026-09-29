# Specialization-Safe Radical Solvers

**Exact bad characteristics for subset-sum resolvents, a Fourier–Kummer atlas, and a global obstruction**

A research report of ProveIt's research-report collection, dated September
2026, built from one manuscript ("Research prepared for Vladimir
Reshetnikov"). It continues the formal project `Algebra/PolynomialFormulas`
(the Lean/Rocq audit of Lazard's solvable-quintic algorithm), but it is not
part of that development.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batch 36, manuscript 04 | `ProveIt_Radical_Solvers_Research` (main file `article.tex`, 29-page PDF) | `e21766d04` | `e13affd32` | `1a1396d4d` | the whole article, Sections 1–15 and Appendices A–B |

The pin is the full commit `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9` (the
article's `\snapshot` macro). `Algebra/PolynomialFormulas` is byte-identical
at the pin and at batch 36, so every repository statement in the report was
checked against the current tree. The placement commit first filed the
package under `Algebra/PolynomialFormulas/Research/`; use `git log --follow`
for its history before the move into this collection.

**Status: AI-assisted, unrefereed, not formalized.** No statement of this
report has a Lean or Rocq proof; that it continues a formal project confers
no formal status on it.

```
article.tex                            the report, standalone LaTeX with an internal bibliography
article.pdf                            the compiled report, 32 pages (title and abstract page 1,
                                       contents page 2, text from page 3)
README.md                              this guide
code/verify_results.py                 exact checks (SymPy): resultants, determinants, finite-field
                                       witnesses, Fourier charts, worked polynomials, patterns
code/audit_certificates.py             independent auditor of the norm certificates (standard library only)
data/requirements.txt                  the pin sympy==1.14.0
data/cyclotomic_norm_certificates.json the 29 multiplication matrices, orbit representatives, sizes, norms
data/affine_orbits.csv                 the 29 affine-orbit rows (CRLF line endings, as delivered)
data/finite_field_witnesses.json       the F_29, F_8, F_7, F_5 witness families and repaired F_29 vectors
data/worked_polynomials.json           the six worked minimal polynomials of Section 10
data/affine_factor_patterns.json       the four solvable affine septic factor patterns
data/septic_rigidity_checks.json       the character-root pattern counts for Section 11
data/verification_report.json          recorded run of verify_results.py (Python 3.13.5, SymPy 1.14.0)
data/independent_audit_report.json     recorded run of audit_certificates.py
data/document_build_report.json        the delivery's build and visual-review record of its PDF
```

Every file under `code/` and `data/` is byte-identical to the delivery. The
delivered `README.md` and PDF are not shipped: this README replaces the
first, and `article.pdf` is a build of the written text. The delivery's
layout was flat, with a `certificates/` directory; the mapping is
`verify_results.py` → `code/verify_results.py`,
`audit_certificates.py` → `code/audit_certificates.py`,
`requirements.txt` → `data/requirements.txt`, and `certificates/X` →
`data/X` for all nine certificate files.

## Labels and numbering

Every label in `article.tex` carries the prefix `rss:`. The 64 delivered
labels keep their names after the prefix; the write added three,
`rss:sec:notation`, `rss:sec:provenance` and `rss:sec:nonclaims` (67 in
total). Every theorem, equation, table and section number is that of the
delivered 29-page PDF: the write adds only unnumbered `[write]` notes, three
subsections at the end of Section 1 (1.4–1.6), two footnotes and four
bibliography entries, and the `.aux` numbers of all 64 delivered labels were
compared with a build of the delivered text.

## Setting and notation

Throughout, `f` is monic, separable and irreducible of odd prime degree `p`,
with roots numbered cyclically by a Galois `p`-cycle `σ`. The orbit product
`R_{p,k,f}(Y) = ∏_{|A|=k} (Y − s_A)` of the `k`-subset sums, the norms
`N_{A,B} = |Res(Φ_p, q_{A,B})|`, and the bad set `𝓑_{p,k}` of their prime
divisors are the objects of Sections 2–6.

Section 1.4 of the article tabulates every overloaded letter. The readings
most likely to mislead:

- **Fourier sign.** The article's modes are `u_j = Σ_i ζ^{−ij} x_i`. The
  project (Lazard's report and `LazardGeneralFourier.lean`, whose character
  is `ψ`) uses `s_k = Σ_j ω^{kj} x_j`. True: with `ζ = ω^{−1}`, `u_k = s_k`.
  False reading: `u_k = s_k` with `ζ = ω`; then `u_k = s_{p−k}`.
- **Lazard's quintic chart.** For `p = 5` and pivot `j = 1`, `a_1 = S_1`,
  `c_{1,k} a_1 = S_k` and `ρ = P_1` in Lazard's notation; `c_{1,k}` itself
  is not `S_k`.
- `𝓑_{p,k}` is a set of primes; `B_{n,k} = (k−1)·C(N,2)` is an integer
  bound; `B` is also a fixed field (Sections 8–9) and a ring of invariants
  (Section 12). `e_j(k)` is an integer exponent, `e_r` an elementary
  symmetric function. `E` is a field, `E(A)` a descriptor vector, and
  neither is Lazard's denominator invariant `E`. In the transition rule,
  `f = e_h(k)` and `g = e_j(k)` are integers. `ψ` in Theorem 11.2 is an
  `F_2`-linear map, not the Lean module's character.

No symbol was renamed and no normalization changed.

## What the report claims

Theorem numbers are those of `article.pdf` (and of the delivered PDF).

- **Theorem 3.3 (exact criterion).** In characteristic 0 the `k`-subset sums
  of every separable irreducible degree-`p` polynomial separate. In
  characteristic `ℓ ≠ p`, universal separation holds iff `ℓ ∉ 𝓑_{p,k}`
  (Bézout identity in `F_ℓ[T]` applied to `(σ − 1)x_0`; necessity by the
  Eisenstein binomial `X^p − t` over `F_ℓ(ζ)(t)`). In characteristic `p`
  it always fails (Artin–Schreier `X^p − X − t`). Section 3.3 extends the
  argument to any balanced coefficient vector.
- **Theorem 4.1.** `𝓑_{5,2} = {5}`, `𝓑_{7,2} = {2,7}`,
  `𝓑_{7,3} = {2,7,29}`, the same for complementary sizes, from 850 pairs in
  4 + 7 + 18 = 29 affine orbits (the 18 septic-triple orbits are Table 1;
  the integer matrix of equation (4) has `|det| = 203 = 7·29`).
- **Theorem 5.1.** Over `F_29(t)`,
  `R_{7,3,X^7−t} = (Y^7−12t)^2 (Y^7−t)(Y^7−17t)(Y^7−28t) = (Y^7−12t)(Y^28−t^4)`;
  also `Y^7 (Y^7−t)^4` over `F_8(t)`, `(Y^7−Y−3t)^5` for `X^7−X−t` over
  `F_7(t)`, and `(Y^5−Y−2t)^2` for `X^5−X−t` over `F_5(t)`.
- **Section 6.** Faggal–Lazard's (2014) five degree-7 factors for cyclic
  septics cannot be read as five *distinct* factors in characteristic 29,
  which their Section 5.2 permits; excluding `{2, 7, 29}` is the sharp
  repair for this separation step.
- **Lemma 7.1 and Theorem 7.2 (separating repair).** Subset elementary
  symmetric vectors are injective in every characteristic;
  `h_A(u) = Σ u^{r−1} e_r(x_A)` separates for all but at most
  `(k−1)·C(N,2)` values of `u`, so 1191 distinct parameters suffice for
  septic triples; explicit repaired factors (13) for the characteristic-29
  example, and the four affine septic factor patterns.
- **Theorem 8.1, Corollary 8.2 (one-radical chart).** For a nonzero pivot
  `u_j`, `a_j = u_j^p` and `c_{j,k} = u_k / u_j^{e_j(k)}` lie in the fixed
  field, and *every* root `ρ` of `T^p − a_j` reconstructs the cyclic shift
  `x_{i + r j^{−1}}`; transition rules (18), (19) on overlaps; `T^p − a_j`
  is the minimal polynomial of `u_j`.
- **Lemma 9.1, Corollary 9.2.** Solvable transitive groups of prime degree
  are affine; a field-degree bound `(p−1)^2` for the abelian stage.
- **Theorem 10.1, Corollary 10.2.** Every nonempty Fourier support occurs,
  via `x_i = P(2^{1/p} ζ^i)`, with Galois group `AGL_1(F_p)`; six worked
  minimal polynomials; none of the `p − 1` coordinate charts can be omitted.
- **Theorem 11.1.** In characteristic 29 an irreducible septic has colliding
  triple sums iff `f = (X − η)^7 − b`; such `f` is cyclic, so noncyclic
  septics separate.
- **Theorem 11.2 and its corollary.** In characteristic 2, pair collisions,
  triple collisions and `f(X) = F(X − η)`, `F = Z^7 + aZ^3 + bZ + d`,
  `d ≠ 0`, are equivalent (an affine Fano configuration); `GL_3(F_2)` of
  order 168 occurs.
- **Theorem 12.1.** No nontrivial eigenunit: the universal cyclic cover of
  the distinct-root configuration space has no single global regular
  Kummer generator.
- **Theorem 12.3.** `Pic(k[x_0, …, x_{p−1}, Δ^{−1}]^{C_p}) ≅ Z/pZ`, by
  descent (Lemma 12.2) from `A^× ≅ k^× × Z[C_p]^{(p−1)/2}`; the Fourier
  charts trivialize the torsor locally.
- **Section 13**: a proof architecture and nine proposed Lean declarations
  (a plan, see below). **Section 14**: nine research questions (14.1–14.9).

## What the report does not claim

The article's Section 1.6 collects these. In brief:

- **Not formalized.** No statement is formalized, and no `rss:` label has a
  Lean or Rocq counterpart. **Section 13 stays a plan: none of it is
  formalized, and no Lean or Rocq code was delivered or is shipped.** Its
  nine declaration names are proposals, not existing identifiers.
- **Evidence.** General theorems rest on written proofs; the finite tables
  on exact computations by ordinary Python programs, not a proof-assistant
  kernel. The Fourier checks cover coefficient-one supports only.
  **The Picard-group and eigenunit section (Section 12) has a written proof
  only: nothing computational checks it.** Nor are the transition rule
  (19), the `AGL_1(F_p)` Galois groups, or the rigidity theorems beyond their
  finite character-pattern counts checked by the suites.
- **The source's own non-claims.** Not a kernel-checked development; the
  classical Fourier, Galois, resultant, additive-polynomial and descent
  tools are not new; priority over the literature is not established; no
  claim to radical formulas in every degree. Section 6 concerns
  distinct-factor separation only, is not a complete audit of the published
  algorithm's matching predicates or denominators, and does not claim that
  later identities there fail. Theorem 8.1 *assumes* the invariant data
  `u_0, a_j, c_{j,k}`; a coefficient-only solver is a further task.
  Corollary 8.2 is relative minimality, not a minimal radical count.
  Corollary 10.2 is minimality of the coordinate-pivot cover only.
  Theorem 12.1 does not rule out piecewise or dense-open formulas,
  line-bundle formulations, or case-distinguishing expression languages.
  The research questions are not asserted to be known open problems, and
  the 1191 bound is not claimed sharp.
- **Novelty relative to the project.** Lazard's quintic scheme already has
  the pivot-1 chart and the ratio invariants
  (`Algebra/PolynomialFormulas/LazardQuinticFormalization.tex:606-612`).
  What Theorem 8.1 adds is the arbitrary odd prime, the arbitrary pivot, the
  all-branch shift statement and the transitions (the delivered Section 1.1
  wording "adds a pivot chart, invariant ratios" is qualified by a `[write]`
  note there). Descriptor separation already exists formally for sextics
  (below); Lemma 7.1 and Theorem 7.2 add the general `(n, k)` setting and a
  characteristic-free explicit bound.
- **Review.** AI-assisted and unrefereed. At intake the proofs were read,
  the headline computations were repeated by a separate script (bad sets,
  the characteristic-29 and characteristic-2 resolvents, finite-field tests
  of Theorems 11.1–11.2, a numerical test of Theorem 8.1 and the transition
  rule for `p = 5, 7, 11`, the six minimal polynomials), and both suites were
  rerun on a copy. That is not an independent proof review. The
  relation-module viewpoint of Section 3.3 and the characteristic-zero
  separation may be close to classical work on linear relations among
  conjugates; this was not checked.

## Relation to the formal project `Algebra/PolynomialFormulas`

Nothing in the project is refuted: every characteristic-sensitive project
statement is characteristic zero or assumes the degree is invertible
(`Algebra/PolynomialFormulas/README.md:14`,
`Algebra/PolynomialFormulas/Lean/PolynomialFormulas/LazardGeneralFourier.lean:14-16`).
The project has formalized **none** of this report's statements. The nearby
declarations, each named at its point of use in the article:

- **Arbitrary-degree Fourier core, the report's starting point.** Lean:
  `Algebra/PolynomialFormulas/Lean/PolynomialFormulas/LazardGeneralFourier.lean`,
  `character_orthogonality` (l.49), `dft_shift` (l.57), `invDFT_dft` (l.98),
  in `LeanProofs.PolynomialFormulas.LazardGeneralFourier`; its docstring
  (l.18-21) records the branch-sensitive invariant-recovery boundary that
  Theorem 8.1 addresses under assumed invariant data. Rocq twin, which the
  manuscript did not cite: `Algebra/PolynomialFormulas/Coq/LazardGeneralFourier.v`,
  `lazard_general_character_orthogonality` (l.96),
  `lazard_general_dft_shift` (l.128), `lazard_general_invDFT_dft` (l.207).
  The crosswalk row `Algebra/PolynomialFormulas/LazardPaperClaimCrosswalk.md:199`
  records both as focused kernel-green with public aggregate/audit pending,
  and states the same boundary.
- **Separation by root polynomials.**
  `Algebra/PolynomialFormulas/Lean/PolynomialFormulas/SexticSeparatingInvariants.lean`:
  `rootPolynomial_injective` (l.115; six roots, any subsets, any commutative
  domain) is Lemma 7.1's argument for sextics; `exists_nat_eval_injective`
  (l.1048; characteristic zero, combinatorial Nullstellensatz) with
  `exists_pairDescriptor_separating_evaluation` and
  `exists_tripleDescriptor_separating_evaluation` (l.1074, l.1083) is the
  characteristic-zero sextic analogue of the separating-parameter existence
  in Theorem 7.2, described in `Algebra/PolynomialFormulas/Decidability.md:284-290`.
  They are the existing counterparts of the proposed
  `elementarySubsetDescriptor_injective` and `separatingParameter_exists`,
  which should generalize them rather than duplicate them.
- **Kummer generator.** `Algebra/PolynomialFormulas/Coq/LazardCyclicKummerGenerator.v:32`,
  `cyclic_kummer_generator`, is the abstract existence form of Corollary 8.2.
- **Positive characteristic.** `LazardAlternatingResolventCounterexample`
  (Lean and Rocq; crosswalk l.202): over `F_3(t)` the cubic `X^3 − t` is
  irreducible but inseparable, and its alternating resolvent is `X^2`.
  Unlike the report's characteristic-29 example, the source polynomial is
  itself inseparable there. `LazardArtinSchreierRadicalCounterexample`
  (crosswalk l.200) uses `X^3 − X − t`, the `p = 3` case of the witness of
  Theorem 3.3(iii), for a different purpose (a solvable group without a
  radical tower).
- **The quintic report.** The distinction between raw invariant equations
  and root-origin evidence (`Algebra/PolynomialFormulas/LazardQuinticFormalization.tex:171-175`)
  and coherent projection branches
  (`Algebra/PolynomialFormulas/LazardQuinticFormalization.tex:152-158`) are
  the project-side counterparts of Sections 13.1 and 13.3. Septics appear in
  the project only as Lazard's unformalized degree-seven forecast
  (`Algebra/PolynomialFormulas/LazardPaperClaimCrosswalk.md:150-158`);
  Faggal–Lazard 2014 is cited in no other tracked file.

No other report of the collection shares a theorem with this one.

## Building

From a scratch copy of this directory (keeps auxiliary files out of the
repository):

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, no external bibliography or figures. The committed build: 32
pages, 0 errors, 0 undefined references or citations, 0 multiply defined
labels, 0 duplicate destinations, 0 overfull boxes, one underfull box
(the status column of the Section 1.3 table, present in the delivered text).

## Rerunning the checks

Run from this directory. Never let the scripts write into `data/`.

```
uv run --no-project --with sympy==1.14.0 python code/verify_results.py --out <tmpdir>
py code/audit_certificates.py --cert data/cyclotomic_norm_certificates.json
```

The verifier (about 15 s after uv resolves its environment) writes seven
files into `<tmpdir>` and prints its report; compare them with the same names
in `data/` after removing carriage returns (on Windows `write_text` emits
CRLF). The auditor is read-only without `--out` and prints its report, which
should equal `data/independent_audit_report.json`. At the write both
commands exited 0 with `"status": "PASS"`, and every fresh file matched its
shipped counterpart modulo CR (`affine_orbits.csv` byte for byte). The one
field expected to vary is `"python"` in `verification_report.json`, which
records the interpreter (3.13.5 in the delivery and at the write, when uv
chose 3.13.5). Do not run Python with `-O`: both scripts refuse it.

## Discrepancies and delivery names

- The delivered text uses the delivery layout: the article's Section 4 and
  Appendix A name `certificates/…` files (each has a `[write]` footnote or
  note), Appendix A's commands run `python verify_results.py --out
  certificates`, and it describes an archive containing the PDF and a
  README, which are not shipped.
- `code/verify_results.py` states `Run: python verify_results.py --out
  certificates` in its docstring (l.7), and its `--out` defaults to
  `certificates` (l.335): run without `--out` it creates a `certificates/`
  directory in the working directory. `code/audit_certificates.py`'s
  `--cert` defaults to `certificates/cyclotomic_norm_certificates.json`
  (l.132), which does not exist here; always pass `--cert` as above.
- `data/document_build_report.json` describes the delivered 29-page PDF
  (not shipped) and "all-page contact sheets" (not shipped); it does not
  describe `article.pdf`.
- `data/affine_orbits.csv` has CRLF line endings, as delivered (Python's
  `csv` writer emits `\r\n` on every system). A path-specific `-text` line
  in the root `.gitattributes` keeps the committed blob byte-identical (535
  bytes) instead of normalizing it to LF.
- The delivered README asked for `python -m pip install -r
  requirements.txt`; here the file is `data/requirements.txt`, and the
  `uv --with sympy==1.14.0` form above needs no install.
