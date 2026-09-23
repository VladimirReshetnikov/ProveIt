# Definable Surreal Numbers and Omnific Integers

Research article dated September 23, 2026. The PDF has 26 pages, 15 main
sections, two appendices, 36 theorem/lemma/proposition/corollary statements,
and 16 bibliography entries. Some of those statements are explicitly
classical or cited; the count is not a count of claimed new theorems.

## Files

- `definable_surreal_numbers.pdf` — the complete typeset article.
- `definable_surreal_numbers.tex` — self-contained LaTeX source, including
  the bibliography. No external images or `.bib` file are needed.
- `verify_finite.py` — standalone, standard-library-only finite regression tests.
- `verification_results.json` — results of the delivered test run.
- `AUDIT.md` — proof, originality, source-inspection, and verification boundaries.

## Main reading route

The ambient definitions are in Section 3. The definable field and integer
part theorem is Theorem 4.2 (page 7), and the HOD identification is Theorem
5.1 (page 9). The reversible fixed-leading-term omnific code is Theorem
6.2 (page 10); Proposition 6.5 supplies a complementary two-term code.
The universe and pointwise-definability tests are in Section 7.

The strongest proposed contribution is Theorem 8.3 (page 14), preceded by
the general support-subfield amplification theorem. With

    K = No intersect HOD = No^HOD,

if V is not HOD and 0 < t < 1 lies outside K, then

    z_alpha = omega + omega^(t * omega^(-(alpha+1)))

is an ordinal-indexed algebraically independent family over K. Every
z_alpha is an omnific integer strictly between omega and omega+sqrt(omega),
with zero constant term and exactly two normal-form terms of coefficient 1.
All powers of omega in this statement are Conway monomials, not general
exponential powers. The class-family assertion means finite polynomial
independence and provides no set-sized bound on the size of independent
subfamilies; it does not posit a proper-class sum or a transcendence basis.

Sections 9–13 treat uniform versus termwise definitions, the first
non-HOD birthday, bounded-complexity escape ordinals, forcing without
new reals, relative ordinal parameters, and canonical surcomplex pairs.

## Build the PDF

From this directory, using an ordinary TeX Live or MiKTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error definable_surreal_numbers.tex
```

Alternatively, run `pdflatex definable_surreal_numbers.tex` three times
to resolve the table of contents and cross-references. Common packages
are used: AMS mathematics, Latin Modern, geometry, microtype, booktabs,
longtable, enumitem, fancyhdr, xurl, and hyperref.

The delivered PDF was built successfully with pdfLaTeX/latexmk. The final
LaTeX log contained no undefined references, missing citations, overfull
boxes, or other warnings. Pages were rendered and visually inspected.

## Run the finite checks

Python 3.10 or later is sufficient; no third-party Python dependencies:

```sh
python verify_finite.py --output verification_results.json
```

The default run checks 8,191 finite sign codes through length 12, rejects
11 malformed codes, checks 3,121 exact rational normalizations and 2,157
formal infinitesimal floor cases, and tests 500 finite support-coset
polynomials. A dependent-exponent negative control must vanish.

These are finite formal regression tests. They do not decide definability,
compute HOD, implement arbitrary surreal arithmetic, or prove the
transfinite theorems. The mathematical proofs are in the article.

## Status and provenance

This is an AI-assisted research draft with written proofs, not a refereed
paper or a Lean formalization. The central coding and transcendence
statements are proposed as original, with a limited literature comparison;
publication priority is not certified. Known results and source-specific
claims are identified in the article's claim ledger.

Repository snapshot consulted:
`VladimirReshetnikov/Surreal`, commit
`9a385d3957bdfe3d9ea79f9a524751c90bd2c894`.
The source catalogue and relevant introductions were inspected, not every
manuscript. No repository file was changed and no Lean build was performed.
