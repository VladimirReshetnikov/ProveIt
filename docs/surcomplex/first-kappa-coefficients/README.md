# The First-κ Coefficients

**Omitted types, singular compression, and completion in surreal and
surcomplex Hahn fields**
Single-source research report, 22 September 2026, built from one manuscript
(item 04 of batch 22, archive `surreal_first_kappa_types`) whose repository
comparison is pinned at `465a54b`. An AI-assisted draft (author line
"OpenAI ChatGPT"), not refereed and not formalized in Lean.

```
article.tex         the report, standalone LaTeX with an internal bibliography
article.pdf         the compiled report, 25 pages
README.md           this guide
research_audit.md   the manuscript's own research audit, as delivered (see below)
code/
  verify.py         exact finite checks (Python 3.10+, standard library only)
  build.sh          the manuscript's build script, written for a flat layout
data/
  verification.json the recorded run of code/verify.py (9,622 assertions)
  build_audit.json  build and layout record of the delivered 21-page PDF
```

Every label in `article.tex` carries the prefix `fkc:` (77 labels: the
manuscript's 72, all kept, and 5 added on placement). No
[Lean ledger](../../FORMALIZATION.md) row cites an `fkc:` label.

## Provenance

One manuscript, dated 22 September 2026 (21 pages). This is **not a merge**:
no other manuscript proves its results, and the nearest material in the
collection is cross-referenced, not merged. The statements, proofs,
limitations and priority caveats are the manuscript's. It was placed in
commit `7b5f934`. What changed on placement (Section 1.4 of the article):

- **Labels** received the prefix `fkc:`. No statement, section or equation
  of the manuscript was renumbered; the added remarks and subsections come
  after the last numbered item of their sections.
- **Added:** Section 1.4 (provenance, notation conventions, neighbouring
  reports); Remark 7.6 (the countable analogues in other reports);
  Remark 9.6 (the groups `Γ_θ` elsewhere); a sentence after the rank-one
  boundary case (Section 9); Section 11.5 (corrections to the manuscript's
  repository statements); Section 11.6 (the collected non-claims N1–N12);
  seven bibliography entries for collection reports; a closing paragraph of
  the abstract; the file paths of Appendix A.
- **Cross-references.** All theorem-like environments share one counter, and
  in the delivered build every `\cref` to a proposition, lemma, corollary or
  example printed "theorem", and the appendix printed "section". The preamble
  now declares the names; no statement changed.
- `code/verify.py`, `code/build.sh`, both files in `data/` and
  `research_audit.md` are byte-identical to the delivery. The delivered member
  README and PDF are not shipped; no checksum manifest was delivered.
  `data/build_audit.json` records the delivered PDF's page count (21) and
  SHA-256, which was checked on placement; it does not describe this
  report's PDF.
- The family `surcomplex/` was chosen over `surreal/` because the results are
  stated uniformly for real and complex coefficients.

`research_audit.md` is verbatim and describes the repository at the pin. Its
"44 reports", its negative search for "spherical" and its comparison with the
Hahn-vector-space report are corrected in Section 11.5 (below); its file names
`verify.py`, `verification.json`, `build.sh` and `build_audit.json` refer to
the delivery's flat layout.

## Notation

No symbol was renamed. Section 1.4 fixes the conventions against
[NOTATION.md](../../NOTATION.md):

| Here | Meaning | Not to be confused with |
|---|---|---|
| `F_k = k((t^Γ))`, `k ∈ {R, C}` | the full Hahn field | NOTATION's `F_Γ` is the **real** field (`= F_R` here) and `K_Γ` the **complex** one (`= F_C` here) |
| `K_{κ,k}` | series with fewer than `κ` nonzero terms; `K` from Section 8 on | NOTATION's full complex workspace `K_Γ` |
| `L_{κ,k}` | its completion, Theorem 7.1 | |
| `D_x` | the approximation cut of a missing `x` | surquaternions' `D_Γ` |
| `E_x = K + Kx` | a two-dimensional valued space | three-duals' `E_Γ(V)`; the entire-function rings of `ent:` |
| `κ`, `μ = cf(κ)` | an uncountable cardinal and its cofinality | residue fields `κ_n` (`ent:`), the gain `κ = v(q)` (expanding dynamics), measures `μ` |
| `I_D` | an additive subgroup, not an ideal | the error ideal `I_κ` of expanding dynamics |
| `T_κ(x)` | the first-κ prefix, an external invariant | a truncation symbol of the language (there is none) |

`cf(Γ)` is cofinality toward `+∞`, `v = min supp`, and `t^γ ↦ ω^(−j(γ))`,
as in NOTATION. Four words are pinned down explicitly: **bounded** means a
bound on the *cardinality* of the support (in
`transcendence-over-bounded-support` it means bounded above in the exponent
order); **complete** type, complete field and spherically complete field are
three different notions; **closure** in Theorem 7.1 is topological, while
Proposition 2.2 is about real and algebraic closedness; an **omitted** type
is a one-type over the set-sized `K_{κ,k}` realized in `F_k`, not an omitted
cut of a proper-class field.

## What the report claims

Fix an uncountable cardinal `κ` (possibly singular), `μ = cf(κ)`, a nonzero
divisible ordered abelian group `Γ` (a set), `k = R` or `C`, and
`K_{κ,k} = {f ∈ k((t^Γ)) : |supp f| < κ}`. Real types are taken in the
language of ordered rings, complex valued types in the ring language with
valuation divisibility.

- **Theorem 1.1 (`fkc:thm:main`), the package.**
  (i) `K_{κ,R}` is real closed and `K_{κ,C}` algebraically closed, even for
  singular `κ`, and both inclusions in the full Hahn fields are elementary
  (Proposition 2.2).
  (ii) For missing `x, y`: `tp(x/K) = tp(y/K)` iff `T_κ(x) = T_κ(y)`, the
  first `κ` nonzero terms (Theorems 4.1 and 4.3); the realizations of a type
  in `F_k` form the coset `T_κ(x) + I_{D_x}`.
  (iii) The least number of formulas of such a type with no realization in
  `K_{κ,k}` is exactly `cf(κ)`, for arbitrary formulas (Theorem 5.3, via
  eventual agreement, Lemma 5.2, and quantifier elimination).
  (iv) If `K_{κ,k} ≠ F_k`, nests of fewer than `cf(κ)` closed balls meet and
  some nest of `cf(κ)` balls is empty, so it is never spherically complete
  (Lemma 6.1, Theorem 6.2, Corollary 6.3).
  (v) The completion is `L_{κ,k} = {f : |supp f ∩ (−∞, γ)| < κ for all γ}`
  (Theorem 7.1); the new elements have cofinal support of order type exactly
  `κ` (Proposition 7.2); and if `K_{κ,k} ≠ F_k`, it is complete iff
  `cf(Γ) ≠ cf(κ)` (Theorem 7.4, with Lemma 7.3).
- **Theorem 3.1:** the exact approximation-value set of a missing `x` is the
  cut `D_x`, of cofinality `cf(κ)`; no best approximation exists.
  Corollary 4.4: at least `2^κ` missing types when `K_{κ,k}` is proper.
- **Theorem 5.4, pure-field collapse:** in the pure ring language all missing
  elements of `F_C` have one type, with omission number `|K_{κ,C}|`.
  Corollary 5.5: restriction of types along `K_κ ≼ K_λ` is truncation of
  prefixes, so the omission number can drop from `ℵ_1` to `ℵ_0`.
- **Theorem 8.1:** the exact valuation-loss set of every linear retraction
  `K + Kx → K`; none is contractive, and a continuous one exists iff
  `x ∉ L_{κ,k}`. Corollary 8.2: the continuous dual of `K + Kx` has dimension
  0 or 2.
- **Examples (Section 9)** over `Γ_θ = ⊕_{α<θ} Q e_α` (largest-index order,
  `cf(Γ_θ) = cf(θ)`, Lemma 9.1): at `κ = ℵ_ω` a countable missing Cauchy limit
  with `L = F` (Example 9.2); the same countable ball obstruction in a complete
  field over `Γ_{κ+}` (Example 9.3); a strict chain `K ⊊ L ⊊ F`
  (Example 9.4); at `κ = ℵ_1` a sequentially complete but incomplete field
  (Example 9.5); and for `Γ ≤ R`, `K_κ = F` for every uncountable `κ`.
- **Section 10:** transfer to actual surreal and surcomplex subfields through
  Conway normal forms, with the explicit surreal
  `X_κ = Σ_{α<κ} ω^(−ω^α)`.

## What the report does not claim

Section 11.6 collects every limitation of the manuscript (N1–N11) and the
one added on placement (N12):

1. `κ` is uncountable; the finite-support case is excluded.
2. Cardinally bounded Hahn fields (Kuhlmann–Shelah for regular `κ`;
   Berarducci–Kuhlmann–Mantova–Matusinski), Hahn arithmetic and closedness,
   Conway normal forms, approximation-type theory with its ball formulas
   (F.-V. Kuhlmann, Proposition 4.4), full-Hahn ball gluing (Poonen), and
   RCF and ACVF quantifier elimination (Tarski, Robinson, Yin) are **not
   new**.
3. **The constructions and the quantifier-elimination inputs are established;
   the proposed contribution is the joint first-κ classification** with its
   exact omission number and completion and linear consequences. It was not
   identified in the reviewed material, but the priority search was targeted
   and not exhaustive (no MathSciNet or zbMATH), and expert review may find
   equivalents.
4. No named longstanding conjecture is settled; the repository comparison
   was not exhaustive; there is no Lean build or certification.
5. Only types realized in the fixed `F_k` are classified: no saturation
   theorem, no automorphism homogeneity, and types are not claimed to be
   automorphism orbits.
6. The topology is intrinsic to the set-sized workspace, not the subspace
   topology from `No`; support bounds are cardinalities, not order bounds.
7. The subfields are not claimed birthday-initial, closed under the surreal
   exponential, compatible with the Berarducci–Mantova derivation, or to
   define the prefix operator.
8. Languages with conjugation, truncation, exponential or derivation, and
   several-variable types, are not classified (left as questions,
   Section 11.4, unnumbered).
9. No new general Hahn–Banach theorem; the zero dual is over an incomplete
   base and contradicts nothing in finite-dimensional functional analysis.
10. Not a new version of the independence theorem of
    `transcendence-over-bounded-support`.
11. The 9,622 finite assertions do not verify the transfinite theorems,
    quantifier elimination, novelty or any Lean implementation.
12. The placement comparisons with other reports prove no new theorem.

## Corrections to the manuscript's repository statements

Section 11.5 keeps the pin `465a54b` as provenance and records:

- At the pin the catalogue described 44 reports, as stated; batch 21 and
  batch 22 have since added four, and the collection had 48 report
  directories when this report was written.
- The manuscript compared its universe-related material with `foundations`;
  the collection now also has `surreal-fields-across-universes`, added after
  the pin (different objects; below).
- The negative indexed search for "spherical" was a false negative:
  spherical completeness of full Hahn fields was already stated in
  `rank-one-berkovich` (`prop:spherical`) and `three-duals-of-hahn-vector-spaces`
  (`duals:prop:spherical`). The manuscript did not rely on the search.
- The comparison with the Hahn-vector-space report omitted its countable
  analogues `duals:thm:completion` and `duals:thm:cofinality-completion`,
  and the Berkovich closure of finite-support series; they do not treat
  cardinally bounded fields, but they belong in the priority context of
  Theorems 7.1 and 7.4.
- Its statements about `transcendence-over-bounded-support` and about the
  two topologies of `foundations` were confirmed.

## Relation to the neighbouring reports

- **[surreal-fields-across-universes](../../foundations-and-computation/surreal-fields-across-universes/)**
  studies saturation and omitted cuts of the proper-class field `No^M` inside
  `No^N` for inner models. It shares vocabulary (omitted types, saturation,
  cofinality spectra, a contrast between languages) but not objects: no Hahn
  field, no support bound, no completion. This report answers none of its
  questions; it was placed after the manuscript's pin.
- **[transcendence-over-bounded-support](../../surreal/transcendence-over-bounded-support/)**
  works over supports **bounded above in order** and explicitly excludes
  cardinal support bounds (`bst:eq:base` and its conventions list). Its
  `bst:cor:optimal` is consistent with this report. No `bst:` question is
  answered.
- **[three-duals-of-hahn-vector-spaces](../three-duals-of-hahn-vector-spaces/)**:
  `duals:thm:completion` (finite coefficient rank below every cut) and
  `duals:thm:cofinality-completion` (completion proper iff `cf(Γ) = ℵ_0`)
  have the shape of Theorems 7.1 and 7.4 at the excluded countable bound, for
  vector spaces (Remark 7.6). Its `duals:prop:spherical` is the full-Hahn
  gluing that Lemma 6.1 refines by a cardinal bound.
- **[rank-one-berkovich](../rank-one-berkovich/)**: spherical completeness of
  `C((t^R))` (`prop:spherical`) and the closure of the finite-support series
  in `C((t^Q))`, the countable analogue of `L_{κ,k}` (Remark 7.6). This
  report's rank-one boundary case (`K_κ = F` for `Γ ≤ R` and uncountable `κ`)
  is consistent with it.
- **[entire-functions-at-arbitrary-rank](../entire-functions-at-arbitrary-rank/)**:
  its `Γ_∞ = ⊕_{j≥0} Q e_j`, `e_j = ω^j` (`ent:eq:concrete-group`), is the
  **same construction** as `Γ_θ` here, namely `Γ_ω`, with the same embedding in
  `No`; its `Γ_{ω_1}` (`ent:eq:Gamma-omegaone`) is the group of Example 9.5
  (Remark 9.6). The questions asked of these groups differ.
- **[foundations](../../foundations-and-computation/foundations/)** separates
  the intrinsic and full fine topologies (`found:prop:twotopologies`,
  `found:thm:discrete`); Section 10 relies on that distinction.
- **[hidden-negative-hermitian-directions](../hidden-negative-hermitian-directions/)**
  asks, in an unlabelled question, about order density and approximant
  degrees for support-family subfields. `K_{κ,R}` is such a subfield, but that
  question is not answered here.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 25 pages with zero errors, zero LaTeX or package warnings,
zero overfull or underfull boxes, zero undefined references or citations,
zero multiply defined labels and zero duplicate PDF destinations. It needs
pdfLaTeX with newtx, amsthm, mathtools, microtype, geometry, enumitem,
booktabs, fancyhdr, hyperref, cleveref, bookmark and xurl; no shell escape,
BibTeX, network access or figures. The LaTeX kernel must provide hooks
(2020-10 or later).

**Run the programs on a copy of this directory.** `code/verify.py` always
writes `verification.json` next to itself (so into `code/`), without an
option to change it; `code/build.sh` expects `article.tex` and `verify.py` in
one directory and writes `article.pdf`, auxiliary files and
`build-pass-*.log` there.

```sh
cp -r first-kappa-coefficients /tmp/fkc-copy
cd /tmp/fkc-copy
python3 code/verify.py > /dev/null      # writes code/verification.json
diff code/verification.json data/verification.json

mkdir /tmp/fkc-flat                     # only to run the delivered build script
cp article.tex code/verify.py code/build.sh /tmp/fkc-flat/
cd /tmp/fkc-flat && bash build.sh
```

The recorded run (`data/verification.json`, seed 20260922) passed **9,622
exact-rational assertions** in 18 families over finite Laurent-polynomial
supports in lexicographically ordered `Z²`: first disagreement, sums and
products, leading data of factored polynomials, tail invariance, nested-ball
agreement and gluing, and the retraction-loss trichotomy. On placement a
rerun on a copy (Python 3.14.4) reproduced it exactly, up to CRLF line
endings on Windows. The flat `build.sh` run also passed and typeset this
25-page report, not the delivered 21-page manuscript that
`data/build_audit.json` describes. The checks test finite mechanisms only;
they prove no transfinite, cardinal, model-theoretic or priority statement.
