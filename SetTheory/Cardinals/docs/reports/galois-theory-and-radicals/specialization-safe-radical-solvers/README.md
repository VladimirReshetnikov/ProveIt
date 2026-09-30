# Specialization-Safe Radical Solvers

**Exact bad characteristics for subset-sum resolvents, a Fourier–Kummer atlas, and a global obstruction; Part II: optimal Kummer atlases for prime cyclic configurations**

A research report of ProveIt's research-report collection, dated September
2026, built from two manuscripts, both "Research prepared for Vladimir
Reshetnikov". Part I is the original report. Part II answers Part I's
Research question 14.5: covering the cyclic quotient of the distinct-root
configuration by regular Kummer charts needs exactly `p − 1` charts, even
with nonlinear character sections. The report continues the formal project
`Algebra/PolynomialFormulas` (the Lean/Rocq audit of Lazard's
solvable-quintic algorithm), but it is not part of that development.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batch 36, manuscript 04 | `ProveIt_Radical_Solvers_Research` (main file `article.tex`, 29-page PDF) | `e21766d04` | `e13affd32` | `1a1396d4d` | Part I: Sections 1–15 and Appendices A–B |
| 02 | batch 52, manuscript 09 | `ProveIt_Optimal_Kummer_Atlases` (inner directory `Optimal_Kummer_Atlases/`, main file `optimal_kummer_atlases.tex`, 22-page A4 PDF) | `1ee53d57d` | `458ccfb80` | `a701d9098` | Part II: Sections 17–29 and Appendix C (Section 16 is the write's) |

Pins in full: source 01 `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9` (the
article's `\snapshot` macro); source 02
`1ee53d57de253d16cdaad79d1f54bbd95d76d682`.

- **Source 01.** `Algebra/PolynomialFormulas` was byte-identical at the pin
  and at the placement commit, so every repository statement in Part I was
  checked against the tree it describes; the batch-36 catalogue commit later
  added a pointer to this report in its README. The placement commit first
  filed the package under `Algebra/PolynomialFormulas/Research/`; use
  `git log --follow` for its history before the move into this collection.
- **Source 02** was written against Part I itself: at its pin this report's
  `article.tex` had the blob `f8303298d0` and its `README.md` the blob
  `dc0dd198ad`, both unchanged at the placement commit, and its secondary
  source `Algebra/PolynomialFormulas/LazardQuinticFormalization.tex` (blob
  `5281cbf260`) is also unchanged. So every statement it makes about "the
  report" refers to Part I as printed. It saw no other batch-52 delivery.
  Its manuscript, README and PDF are not shipped; they survive in the
  arrival commit `458ccfb80`.

**Status: AI-assisted, unrefereed, not formalized.** Neither part has a
Lean or Rocq proof of any of its statements. That the report continues a
formal project confers no formal status on it.

```
article.tex                            the report, standalone LaTeX with an internal bibliography
article.pdf                            the compiled report, 59 pages (title and abstract page 1,
                                       contents pages 2-3, Part I from page 4, Part II from
                                       page 34, references pages 57-59)
README.md                              this guide

Part I (source 01)
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

Part II (source 02, prefix 02-kummer-atlases-)
code/02-kummer-atlases-verify_finite_checks.py  exact finite checks (standard library only):
                                       partitions, Euler coefficients, Fourier identities
code/02-kummer-atlases-build.sh        the delivery's build script (does not work here; see below)
data/02-kummer-atlases-finite_checks.json       recorded run of the checker (Python 3.13.5)
data/02-kummer-atlases-source_manifest.json     the delivery's pin, inspected blobs and references
data/02-kummer-atlases-build_check.json         the delivery's build record of its 22-page PDF
```

Every file under `code/` and `data/` is byte-identical to its delivery. The
delivered READMEs and PDFs and source 02's manuscript are not shipped: this
README replaces the READMEs, and `article.pdf` is a build of the written
text.

- Source 01's layout was flat, with a `certificates/` directory; the mapping
  is `verify_results.py` → `code/verify_results.py`,
  `audit_certificates.py` → `code/audit_certificates.py`,
  `requirements.txt` → `data/requirements.txt`, and `certificates/X` →
  `data/X` for all nine certificate files.
- Source 02's mapping is `code/verify_finite_checks.py` →
  `code/02-kummer-atlases-verify_finite_checks.py`, `build.sh` →
  `code/02-kummer-atlases-build.sh`, and `data/X.json` →
  `data/02-kummer-atlases-X.json` for its three records. Part I's unprefixed
  files count as `01` in the report's local sequence.

## Labels and numbering

Part I's labels carry the prefix `rss:`: its 64 delivered labels keep their
names after the prefix, and batch 36 added three (`rss:sec:notation`,
`rss:sec:provenance`, `rss:sec:nonclaims`). Part II's labels carry the prefix
`ka:`: its 73 delivered labels keep their names after the prefix, and the
batch-52 write added six (`ka:sec:write`, `ka:sec:provenance`,
`ka:sec:notation`, `ka:sec:nonclaims`, `ka:sec:conclusion`, and
`ka:q:rss-minimal-covers` on Part I's Research question 14.5). That is
67 + 79 = 146 labels. No label was renamed or deleted.

- **Part I** numbers are those of the delivered 29-page PDF: the writes add
  only unnumbered `[write]` notes, three subsections at the end of
  Section 1 (1.4–1.6), two footnotes and four bibliography entries. At
  batch 52 the `.aux` numbers of all 67 `rss:` labels were compared with a
  build of the committed text: identical.
- **Part II** continues the numbering after Part I's appendices. The
  manuscript's Section `n` is Section `n + 16` here (Section 16 is the write's
  provenance section), its Appendix A is Appendix C, theorem numbers follow
  the sections (its Theorem 1.1 is Theorem 17.1), and its equation `(m)` is
  printed as `(m + 30)`.

## Setting and notation

Throughout Part I, `f` is monic, separable and irreducible of odd prime
degree `p`, with roots numbered cyclically by a Galois `p`-cycle `σ`. The
orbit product `R_{p,k,f}(Y) = ∏_{|A|=k} (Y − s_A)` of the `k`-subset sums,
the norms `N_{A,B} = |Res(Φ_p, q_{A,B})|`, and the bad set `𝓑_{p,k}` of their
prime divisors are the objects of Sections 2–6. Part II works on
`X_{p,d} = Conf_p(A^d_k)/C_p` with `N = d(p − 1)`, over any field `k` of
characteristic `≠ p` containing a primitive `p`th root of unity `ζ`; for
`d = 1`, `X = Spec B` with Part I's `B = A^{C_p}` of Section 12.

Section 1.4 tabulates Part I's overloaded letters and Section 16.2 those of
Part II. The readings most likely to mislead:

- **Fourier sign.** Both parts use `u_j = Σ_i ζ^{−ij} x_i`. The project
  (Lazard's report and `LazardGeneralFourier.lean`, whose character is `ψ`)
  uses `s_k = Σ_j ω^{kj} x_j`. True: with `ζ = ω^{−1}`, `u_k = s_k`. False
  reading: `u_k = s_k` with `ζ = ω`; then `u_k = s_{p−k}`.
- **Lazard's quintic chart.** For `p = 5` and pivot `j = 1`, `a_1 = S_1`,
  `c_{1,k} a_1 = S_k` and `ρ = P_1` in Lazard's notation; `c_{1,k}` itself
  is not `S_k`.
- **Pivot ratios across the parts.** Part I's `c_{j,k}` has the pivot as its
  first index. Part II's `c_{a',k}` (Section 23) has a *coordinate* index
  first, with the pivot `u_{b,j}` fixed. True: for `d = 1`, Part II's
  `c_{1,k}` with pivot `u_{1,j}` is Part I's `c_{j,k}`. False: it is Part I's
  `c_{1,k}`.
- **Chart count is not a radical count.** `p − 1` charts cover the universal
  quotient; each chart uses one `p`th radical, so `p − 1` independent
  radicals are *not* needed at one input. And a nonzero class in `Pic B`
  alone bounds the chart count below by two, not `p − 1`: the higher powers
  of `t` are needed.
- Part I: `𝓑_{p,k}` is a set of primes; `B_{n,k} = (k−1)·C(N,2)` is an
  integer bound; `B` is also a fixed field (Sections 8–9) and a ring of
  invariants (Section 12). `e_j(k)` is an integer exponent, `e_r` an
  elementary symmetric function. `E` is a field, `E(A)` a descriptor vector,
  and neither is Lazard's denominator invariant `E`. In the transition rule,
  `f = e_h(k)` and `g = e_j(k)` are integers. `ψ` in Theorem 11.2 is an
  `F_2`-linear map, not the Lean module's character.
- Part II: `t = c_1(𝓛)` is a Chow class, not Part I's transcendental in
  `F_29(t)`; `N = d(p − 1)`, not a norm; `F` is the full diagonal; `κ`, `γ`,
  `α` are the chart, section-generator and algebra-generator numbers, and
  `α` is not Part I's `2^{1/p}`; `a` is a coordinate index as well as a
  radicand (`a_{a,j} = u_{a,j}^p`).

No symbol was renamed and no normalization changed in either part.

## What the report claims

Theorem numbers are those of `article.pdf` (for Part I, also those of the
delivered PDF).

### Part I

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
  (a plan, see below). **Section 14**: nine research questions (14.1–14.9);
  14.5 is answered by Part II (a dated `[write]` note there says so), the
  others stay open.

### Part II

- **Theorem 17.1 (main theorem).** For `X_{p,d} = Conf_p(A^d_k)/C_p`,
  `N = d(p − 1)`, `t = c_1(𝓛)`:
  `CH^*(X_{p,d}) = Z[t]/(pt, t^N)` as graded integral rings, and the least
  number of regular Kummer charts covering `X_{p,d}` equals the least number
  of global sections generating any nontrivial character line bundle, both
  `N`. Charts may be arbitrary Zariski opens, with arbitrary nonlinear
  character sections and different nontrivial characters on different
  charts. Thus `CH^r = Z/pZ` for `1 ≤ r < N`; at `(p, d) = (2, 1)`,
  `N = 1` and the ring is `Z`.
- **Corollary 17.2 (answer to Research question 14.5).** `Spec B` needs
  exactly `p − 1` regular Kummer charts (four for quintics, six for
  septics), and each nontrivial eigenmodule `L_j` needs exactly `p − 1`
  generators as an invertible `B`-module.
- **Lemma 18.1.** A Kummer chart is exactly an open trivializing one (hence
  every) nontrivial character line.
- **Proposition 19.2 and Theorem 20.4.** The ring for the quotient with only
  the full diagonal removed, by a finite scalar approximation and the Euler
  class `((p−1)!)^d t^N`; deleting the partial diagonals adds no relation,
  because the only cyclically invariant partitions of `F_p` are the two
  trivial ones and each partial-diagonal class pushes forward to zero
  (Lemmas 20.1–20.3). For `d = 1` the degree-one part reproves Part I's
  Theorem 12.3 by a different route; both proofs are printed.
- **Lemma 21.1, Propositions 21.2–21.3.** A cover by `m` opens trivializing a
  line bundle kills `c_1^m`; hence at least `N` charts; the `N` Fourier charts
  attain the bound.
- **Theorem 22.2 (noncompression).** Any `m < N` regular character
  covariants on `Conf_p(A^d)` have a common geometric zero; `N` Fourier modes
  do not. Example 22.1: `u_1, u_2^3, u_3^2, u_4^4` generate the weight-one
  quintic eigenmodule, and no three elements do.
- **Section 23.** One shared radical reconstructs the whole tuple in every
  dimension `d` (Proposition 23.1, Part I's Theorem 8.1 for `d = 1`), with
  the branch transition on overlaps.
- **Theorems 24.2–24.3.** No equivariant regular map
  `Conf_p(A^d) → Conf_p(A^s)` for `d > s ≥ 1`; the finite algebra of the
  cyclic cover needs exactly `d` global algebra generators. For `d = 1` it is
  globally monogenic, `B[T]/(∏(T − x_i)) ≅ A`, yet needs `p − 1` Kummer
  charts; `c(q_*𝒪) = 1 − t^{p−1}` shows non-freeness for `d ≥ 2`.
- **Theorem 25.1, Corollary 25.2.** The same ring and chart count for every
  invariant open between the distinct configurations and the complement of
  the full diagonal, e.g. cyclic graph configurations `z_i ≠ z_{i+1}`.
- **Proposition 26.1.** The loci `u_{a,j} = 0`, `(a, j) ∈ S`, `|S| < N`,
  have class `(∏ j) t^{|S|}`, a generator of `CH^{|S|}`; the top power is
  represented by translated binomial configurations `(T − η)^p − β^p`; a
  table of small cases.
- **Section 27**: proof audit, finite checks and a formalization plan (a
  plan only). **Section 28**: eight research questions (28.1–28.8).

## What the report does not claim

Sections 1.6 (Part I) and 16.3 (Part II) collect these. In brief:

- **Not formalized.** No statement is formalized, and no `rss:` or `ka:`
  label has a Lean or Rocq counterpart. **Section 13 and Section 27.3 are
  plans: none of them is formalized, and no Lean or Rocq code was delivered
  or is shipped.** Section 13's nine declaration names are proposals, not
  existing identifiers.
- **Evidence.** General theorems rest on written proofs; the finite tables
  on exact computations by ordinary Python programs, not a proof-assistant
  kernel. Part I's Fourier checks cover coefficient-one supports only.
  **Part I's Picard-group and eigenunit section (Section 12) has a written
  proof only: nothing computational checks it.** Nor are the transition rule
  (19), the `AGL_1(F_p)` Galois groups, or the rigidity theorems beyond their
  finite character-pattern counts checked by the suites. **Part II's
  Chow-ring computation and atlas lower bound are written proofs using
  standard integral intersection theory (Fulton, Totaro, Edidin–Graham); its
  checker verifies partition counts, Euler coefficients and Fourier
  identities only** (exhaustive over `F_7` and `F_11`, seeded samples over
  `F_29`; branch checks on 128 inputs per field).
- **Source 01's own non-claims.** Not a kernel-checked development; the
  classical Fourier, Galois, resultant, additive-polynomial and descent
  tools are not new; priority over the literature is not established; no
  claim to radical formulas in every degree. Section 6 concerns
  distinct-factor separation only, is not a complete audit of the published
  algorithm's matching predicates or denominators, and does not claim that
  later identities there fail. Theorem 8.1 *assumes* the invariant data
  `u_0, a_j, c_{j,k}`; a coefficient-only solver is a further task.
  Corollary 8.2 is relative minimality, not a minimal radical count.
  Corollary 10.2 is minimality of the coordinate-pivot cover only (Part II
  now gives the lower bound for all regular Kummer covers of the universal
  quotient; a dated note after the corollary says so).
  Theorem 12.1 does not rule out piecewise or dense-open formulas,
  line-bundle formulations, or case-distinguishing expression languages.
  The research questions are not asserted to be known open problems, and
  the 1191 bound is not claimed sharp.
- **Source 02's own non-claims.** The intersection-theoretic machinery is
  established work, Totaro's treatment of cyclic products is close
  background, and no exhaustive priority review was made. Part II does not
  solve the generic quintic over its symmetric coefficient field, compute
  coefficient-level invariants, minimize nested radicals for one input, or
  bound programs with case distinctions; it concerns regular Kummer
  presentations on Zariski opens of a specified universal cyclic quotient.
  Theorem 25.1 does not cover further deletions, and the algebra-generator
  count is not asserted for the larger opens. The algebraic chart count is
  not claimed to equal holomorphic or continuous counts. Its research
  questions are not asserted to be known open problems. The proof-assistant
  library coverage of the needed intersection theory was not audited.
- **Novelty relative to the project.** Lazard's quintic scheme already has
  the pivot-1 chart and the ratio invariants
  (`Algebra/PolynomialFormulas/LazardQuinticFormalization.tex:606-612`).
  What Theorem 8.1 adds is the arbitrary odd prime, the arbitrary pivot, the
  all-branch shift statement and the transitions (the delivered Section 1.1
  wording "adds a pivot chart, invariant ratios" is qualified by a `[write]`
  note there). Descriptor separation already exists formally for sextics
  (below); Lemma 7.1 and Theorem 7.2 add the general `(n, k)` setting and a
  characteristic-free explicit bound.
- **Review.** AI-assisted and unrefereed. At the batch-36 intake Part I's
  proofs were read, the headline computations were repeated by a separate
  script (bad sets, the characteristic-29 and characteristic-2 resolvents,
  finite-field tests of Theorems 11.1–11.2, a numerical test of Theorem 8.1
  and the transition rule for `p = 5, 7, 11`, the six minimal polynomials),
  and both suites were rerun on a copy. At the batch-52 write Part II's
  proofs were read, its checker was rerun on a copy, and a separate script
  recomputed the proper-partition orbit counts from Stirling numbers, the
  Wilson residues `((p−1)!)^d ≡ (−1)^d`, the integral identity behind
  `c(q_*𝒪) = 1 − t^{p−1}` for `p ≤ 13`, the quintic coefficient
  `2·3·4 ≡ −1 (mod 5)`, the tuple and branch counts of Section 27.2 and the
  pivot-change shift. None of that is an independent proof review. The
  relation-module viewpoint of Section 3.3 and the characteristic-zero
  separation may be close to classical work on linear relations among
  conjugates; this was not checked.

## Relation to the formal project `Algebra/PolynomialFormulas`

Nothing in the project is refuted: every characteristic-sensitive project
statement is characteristic zero or assumes the degree is invertible
(`Algebra/PolynomialFormulas/README.md:14`,
`Algebra/PolynomialFormulas/Lean/PolynomialFormulas/LazardGeneralFourier.lean:14-16`).
The project has formalized **none** of this report's statements, and the
repository has no Chow-group development, so nothing in Part II has a formal
counterpart. The nearby declarations, each named at its point of use in the
article:

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
  `cyclic_kummer_generator`, is the abstract existence form of Corollary 8.2:
  a cyclic Galois extension containing the needed roots of unity has one
  Kummer generator. It is a field-level statement; Part II does not rely on
  it, and it says nothing about regular charts on the configuration space.
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
  Faggal–Lazard 2014 is cited in no other tracked file. Part II cites the
  quintic report only as background and assumes none of its unformalized
  claims.

No other report of the collection shares a theorem with this one. The
sibling report
[`sextic-block-resolvent-separators`](../sextic-block-resolvent-separators/README.md)
(batch 41, written without knowledge of this one) bounds, on paper, the
Lean parameter search built on the sextic descriptors above: one of
`t = 1, …, 196` on the curve `(u, v) = (t, 2t²)` separates both partition
families, sharply for arbitrary complex test sets. It is a sextic-partition
counterpart of Theorem 7.2, obtained by the orbit counting that Research
question 14.3 asks for, but it answers no question of this report (14.3 is
about septic triples). A dated `[write]` note after Theorem 7.2 points to
it (added 29 September 2026).

## Building

From a scratch copy of this directory (keeps auxiliary files out of the
repository):

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, no external bibliography or figures. The committed build: 59
pages, A4, 0 errors, 0 undefined references or citations, 0 multiply
defined labels, 0 duplicate destinations, 0 overfull boxes, one underfull
box (the status column of the Section 1.3 table, present in the delivered
text and in a build of the batch-36 text). All fonts are embedded Type 1.

## Rerunning the checks

Run from this directory. Never let the scripts write into `data/`.

```
uv run --no-project --with sympy==1.14.0 python code/verify_results.py --out <tmpdir>
py code/audit_certificates.py --cert data/cyclotomic_norm_certificates.json
py code/02-kummer-atlases-verify_finite_checks.py --output <tmpdir>/finite_checks.json
```

- **Part I.** The verifier (about 15 s after uv resolves its environment)
  writes seven files into `<tmpdir>` and prints its report; compare them with
  the same names in `data/` after removing carriage returns (on Windows
  `write_text` emits CRLF). The auditor is read-only without `--out` and
  prints its report, which should equal `data/independent_audit_report.json`.
  At the batch-36 write both commands exited 0 with `"status": "PASS"`, and
  every fresh file matched its shipped counterpart modulo CR
  (`affine_orbits.csv` byte for byte). The one field expected to vary is
  `"python"` in `verification_report.json`, which records the interpreter
  (3.13.5 in the delivery and at that write). Do not run Python with `-O`:
  both scripts refuse it.
- **Part II.** The checker (standard library only, about 9 s) prints `PASS`
  and writes one JSON file. Compare it, after removing carriage returns (it
  writes CRLF on Windows), with `data/02-kummer-atlases-finite_checks.json`.
  At the batch-52 write it exited 0 and matched except for
  `"python_version"` (3.14.4 at the write, 3.13.5 recorded). **Always pass
  `--output`:** see the next section.

## Discrepancies and delivery names

- The delivered text uses the delivery layout: Part I's Section 4 and
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
- The delivered README of source 01 asked for `python -m pip install -r
  requirements.txt`; here the file is `data/requirements.txt`, and the
  `uv --with sympy==1.14.0` form above needs no install.
- **Part II's checker overwrites by default.**
  `code/02-kummer-atlases-verify_finite_checks.py` defaults `--output` to
  `data/finite_checks.json` under the script's parent directory (l.178-179).
  In the delivered layout that is the recorded output, which a plain run
  overwrites; here a plain run creates an unshipped `data/finite_checks.json`
  beside the shipped record. It writes with `write_text` (l.205), so on
  Windows the file has CRLF line endings. Its docstring says "Run from any
  directory".
- **Part II's build script does not work here.**
  `code/02-kummer-atlases-build.sh` changes to its own directory (`code/`),
  requires `python3`, runs `python3 code/verify_finite_checks.py` and then
  compiles `optimal_kummer_atlases.tex`; neither path exists in the shipped
  layout, and in the delivered layout the first step reran the checker in
  place over the recorded output. Build this report as under "Building".
- Part II's text names delivery paths: Section 27.2 names
  `code/verify_finite_checks.py` and `data/finite_checks.json` (a `[write]`
  footnote gives the shipped names), and Appendix C.3 describes the delivered
  package (source, PDF, README, `build.sh`) and gives `python3` and
  `pdflatex … optimal_kummer_atlases.tex` commands (a `[write]` note gives
  the shipped names and the safe rerun). Source 02's delivered README (not
  shipped) gave `python3 code/verify_finite_checks.py` and `sh build.sh`.
- `data/02-kummer-atlases-build_check.json` describes the delivered 22-page
  PDF, not `article.pdf`. `data/02-kummer-atlases-source_manifest.json`
  records the pin, the inspected blob of Part I's `article.tex` and of
  `LazardQuinticFormalization.tex`, and the external references; its paths
  are repository paths and remain valid.
