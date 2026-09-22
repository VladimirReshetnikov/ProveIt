# Targeted documentation-gap audit

## Snapshot and scope

Repository: VladimirReshetnikov/Surreal

Inspected commit: `e260237db9b71da8b74a0c13c8e6355119091100`

Inspection date: September 21, 2026, America/Los_Angeles.

The review used the repository map, the catalogue's introductory and topical
material, and the specialist READMEs listed below. Repository content was read
through the GitHub connector, with the commit pinned. This is not a line-by-line
audit of all article sources, not a verification of existing mathematical
claims, and not an exhaustive assertion that no derivation is mentioned
anywhere in the repository. Code-search calls did not return usable matches;
those empty responses were not used as evidence of absence.

## Positive evidence for the selected gap

1. **Documentation map.** `docs/README.md` lists fifteen packages. Its surcomplex
   family covers analysis, analytic geometry, finite deformations, contours and
   Stokes, global divisors, polynomial algebra, and trigonometry. The map also
   emphasizes set-sized Hahn workspaces and the differences between coefficient
   rings. It does not list a dedicated differential-algebra package.
2. **Trigonometry.** `docs/surcomplex/trigonometry/README.md`, in its limitations,
   explicitly excludes choosing a derivation on No, and distinguishes its
   phase-extension classification from a classification of differential-equation
   solutions. This is the most direct documented boundary.
3. **Foundations.** `docs/foundations-and-computation/foundations/README.md`
   records the requirement that scalar-field derivations, pointwise derivatives,
   formal-series germs, and coherent Hahn data be distinct interfaces. The new
   article supplies mathematical bridges between these interfaces rather than
   identifying them by notation.
4. **Analysis.** `docs/surcomplex/analysis/README.md` explains the inequivalent
   function classes, residues, and strong-summability framework. The new article
   retains a fixed common ordinary domain for its coefficient-interface results.
5. **Computer algebra.** `docs/foundations-and-computation/computer-algebra/README.md`
   separates exact denotation, effective coefficient access, and decision
   procedures. The new implementation therefore handles only rational phase
   coefficients over Q; unsupported inputs are not treated as impossibility.

## Selected contribution

**Differential Algebra of Surreal and Surcomplex Numbers: Differential Hahn
workspaces, bounded phases, logarithmic derivatives, and oscillation
obstructions.**

Suggested repository placement: `docs/surcomplex/differential-algebra/`.

The article imports the Berarducci–Mantova derivation's existence and major
properties with attribution. It supplies full proofs of the support-based
workspace construction, finite-phase differential compatibility, the exact
logarithmic-derivative image, canonical rank-one gauge representatives, rational
phase classification, constant-coefficient solution spaces, an explicit
oscillatory extension without new constants, and common-domain analytic
coefficient interfaces.

No priority or novelty claim is made. No repository write, commit, or pull
request was performed. Only the new article and its supporting artifacts are
packaged.

## Pinned repository sources

- [Documentation map](https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/README.md)
- [Catalogue](https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/manifest.tex)
- [Trigonometry scope](https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/trigonometry/README.md)
- [Analysis scope](https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/analysis/README.md)
- [Foundations scope](https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/foundations-and-computation/foundations/README.md)
- [Computer-algebra scope](https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/foundations-and-computation/computer-algebra/README.md)

## External primary sources checked

- Berarducci and Mantova, *Surreal numbers, derivations and transseries*,
  JEMS 20 (2018), 339–390; DOI 10.4171/JEMS/769; arXiv:1503.00315.
  Theorems A and B supply the selected derivation and its surjectivity.
- Aschenbrenner, van den Dries, and van der Hoeven, *The surreal numbers as a
  universal H-field*, arXiv:1512.02267v3. Used for background on Hahn fields,
  differential embeddings, and the interpretation of transfer claims.
- Berarducci and Mantova, *Transseries as germs of surreal functions*,
  Trans. AMS 371 (2019), 3549–3592; arXiv:1703.01995. Used to delimit
  composition and compatibility claims; the incompatibility result is not
  strengthened to an assertion about all conceivable alternative structures.
- B. H. Neumann, *On ordered division rings*, Trans. AMS 66 (1949), 202–252;
  DOI 10.1090/S0002-9947-1949-0032593-5. Background source for the
  positive-support summability lemma.

The three arXiv papers were consulted as primary sources, including rendered
PDF pages for the relevant theorem statements. The literature review is
focused, not exhaustive. Source texts and font files are not redistributed.
