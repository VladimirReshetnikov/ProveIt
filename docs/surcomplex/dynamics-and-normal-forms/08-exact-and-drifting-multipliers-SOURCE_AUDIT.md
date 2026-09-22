# Source and claim audit

Inspection date: 22 September 2026.

## 1. Repository baseline and the exact questions

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit:
`a3124af79f66b8b9c196d76b4cbc5ac3938907c4`.

The repository was read through the GitHub connector. The root and
`docs/README.md` were consulted to avoid duplicating the existing
surreal and surcomplex reports. Selected README material from the
dynamics and differential-equations packages was also read. This was
not a line-by-line audit of all repository manuscripts or Lean modules.

The mathematical baseline is:

`docs/surcomplex/dynamics-and-normal-forms/article.tex`

Stable source:
https://github.com/VladimirReshetnikov/Surreal/blob/a3124af79f66b8b9c196d76b4cbc5ac3938907c4/docs/surcomplex/dynamics-and-normal-forms/article.tex

Relevant source ranges actually retrieved include lines 1800–1960,
2150–2260, 7815–7867, 7850–8080, and 8950–9120. The source labels are
more useful than line numbers if the report is edited:

- `dyn:q:commongerm-restate`, referring back to `dyn:q:commongerm`:
  common-domain germs at finite positive small-divisor rate remain open
  in the exact-multiplier category. The report distinguishes this from
  the negative drifting-multiplier result.
- `dyn:q:cyclic`: the two-independent-scale drifting obstruction is not
  asserted for a fixed cyclic value group such as Z; contributions can
  collide at the same Hahn exponent. The question concerns the existence
  of some positive common neighborhood, not merely retention of the
  original input disk.
- `dyn:thm:main`: existing fixed-domain, separate-germ, entire,
  polynomial, and formal coefficient-category results.
- `dyn:prop:linearization`: the support-controlled operator expansion.
- `dyn:prop:halo` and `dyn:prop:monad`: existing actual halo evaluation and
  arithmetic-free infinitesimal evaluation.

### Extent of the answers

The new common-radius theorem treats exact scalar multipliers lambda I_d,
including every one-dimensional exact multiplier in the question. It
**does not settle the arbitrary nonscalar diagonal case**.

The cyclic example addresses the one-variable drifting problem in the
specified report. The auxiliary two-parameter formula is used only for
bookkeeping; the theorem explicitly proves that the collision of those
parameters cannot cancel the leading small-divisor pole. The final
counterexample is over C((epsilon)), with value group Z.

The reference questions belong to an AI-assisted research report. They
are not described as famous published conjectures or as independently
refereed results. Claims about their open status are relative to the
pinned revision, not to future repository changes.

## 2. External literature inspected

### B. Poonen, Units in Hahn–Mal'cev–Neumann rings

Manuscript dated 14 January 2026, four pages:
https://math.mit.edu/~poonen/papers/malcev.pdf

The full short manuscript was inspected, including Theorem 4.1 and the
possibly noncommutative coefficient-ring convention. The relevant PDF
page was also viewed. It is used as a primary source for the classical
positive-support geometric-series theorem. Our free-associative-
coefficient application makes ordered-word finiteness explicit; the
underlying support theorem is not claimed as new.

### S. Marmi, An Introduction to Small Divisors Problems

Lecture notes, 2000, arXiv:math/0009232:
https://arxiv.org/abs/math/0009232

The PDF was inspected at the continued-fraction and small-divisor
sections, including best approximation, the standard convergent-error
bounds, and the discussion of Davie estimates. The relevant PDF page
containing Exercise 5.2 and the Davie-lemma discussion was viewed.
The ordinary linearization and quadratic-germ context was checked as
well. This is a targeted reading, not a claim to have independently
reproved every theorem in the notes.

### C. Carminati and S. Marmi, Linearization of germs: regular dependence on the multiplier

Bulletin de la Société Mathématique de France 136 (2008), no. 4,
533–564; DOI 10.24033/bsmf.2565; arXiv:0801.2844v2:
https://arxiv.org/html/0801.2844v2

The introduction and relevant arithmetic appendix were inspected in
full-text HTML. The paper supplies context for ordinary multiplier
regularity and Bruno arithmetic. Its existence does not by itself
establish or refute the unrestricted Hahn-coefficient common-radius
claim made here.

### F. Fauvet, F. Menous, and D. Sauzin, Explicit linearization of one-dimensional germs through tree-expansions

Bulletin de la Société Mathématique de France 146 (2018), no. 2,
241–285; DOI 10.24033/bsmf.2757:
https://www.numdam.org/articles/10.24033/bsmf.2757/

The abstract and bibliographic metadata were inspected. Attempts to
retrieve a usable full text at the publisher/archive routes did not
succeed in this session. The article is therefore credited as a tree-
expansion antecedent, but the audit does not claim a complete theorem-
by-theorem comparison against its full text.

### F. Fauvet, F. Menous, and D. Sauzin, Explicit linearization of multi-dimensional germs and vector fields through Ecalle's tree expansions

arXiv:2507.13216, first posted 17 July 2025, version 2 dated
13 September 2026, 41 pages:
https://arxiv.org/abs/2507.13216
https://arxiv.org/html/2507.13216v2

The current version metadata, introduction, formal/tree framework,
and relevant arithmetic/Bruno estimates were inspected in HTML.
Its ordinary analytic convergence estimates are relevant antecedents.
The manuscript here does not claim to have discovered Ecalle's tree
expansions, or the classical small-divisor separation method.

### J.-C. Yoccoz, Théorème de Siegel, nombres de Bruno et polynômes quadratiques

Astérisque 231 (1995), 3–88:
https://www.numdam.org/item/AST_1995__231__1_0/

Bibliographic metadata was inspected. The ordinary sharp Bruno
criterion cited in the article was cross-checked in Marmi's notes and
Carminati–Marmi's introduction. This audit does not assert a full-text
reading of the original 1995 article.

## 3. Novelty assessment

Targeted searches considered Hahn/surreal linearization, formal
parameter coefficients, fixed-depth small-divisor products, common
analytic domains, multiplier drift, tree expansions, and continued-
fraction pole separation. No exact match for the two headline results
was located in the inspected material.

That is **not** an exhaustive priority determination. In particular,
a theorem on formal analytic families, a tree-estimate refinement, or
an uninspected paper could subsume a specialization. The delivered
article therefore labels the results as proposed contributions with
proofs, not as certified bibliographic firsts.

## 4. Dependency and claim ledger

### Imported or pre-existing

- Positive-support Hahn geometric summability and Neumann word finiteness.
- Irrational-rotation homological inversion.
- The formal support-controlled conjugacy expansion.
- Classical continued-fraction best approximation and error estimates.
- The qualitative unchanged-domain result at rate zero.
- Polynomial-coefficient normalization and monad evaluation.
- The general framework of ordinary holomorphic tree expansions.

### Proposed contributions, proved in the article

- A fixed-depth product estimate whose exponential rate is tau rather
  than depth times tau.
- A positively weighted tree extension, with a divisible-subtree
  packing proof.
- A sharp common radius R exp(-tau), independent of Hahn word depth,
  for exact scalar multipliers in all finite dimensions.
- A full collision-noncancellation estimate at convergent degrees for
  the single-scale drifting example.
- Exact cyclic coefficient radii R exp(-m tau), and the resulting
  fixed-workspace distinction between exact and drifting multipliers.

### Deliberately not claimed

- A resolution for general nonscalar diagonal exact multipliers.
- A new proof of the classical Bruno–Yoccoz theorem.
- Ordinary analytic convergence jointly in a complex parameter.
- A nonpolynomial globally Hahn-entire function on all surcomplex numbers.
- A result about the Berarducci–Mantova derivation.
- Nonexistence of every conceivable set-theoretic or monad conjugacy.
- Peer review, Lean verification, or certified priority.

## 5. Verification scope

The Python suite performs exact finite checks. Its supplied output is
`data/verification.json`. Its tested dimensions, degrees, and counts
are reported separately in the article. Infinite summability,
small-divisor limsups, exact analytic radii, and universal statements
are justified by the written mathematical arguments, not by those
finite checks.

The final PDF was compiled from the supplied TeX, checked for undefined
references/citations and layout warnings, and rendered for visual
inspection. See `data/build_report.json` for the final build record.
