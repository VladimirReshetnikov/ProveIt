# Naming Elementary Embeddings
## Atom Components, Replacement, and Reflection

Research manuscript prepared for Vladimir Reshetnikov, October 2026.

The article investigates a concrete intersection of Elliot Glazer's work on
urelement set theory and language-sensitive axiom schemes with ProveIt's
first-order set theory, bounded consistency, and self-embedding interests.

## Read the article

`article.pdf` is the 27-page compiled manuscript. `article.tex` is its complete,
self-contained LaTeX source, including the bibliography.

The principal results are:

- Theorem 5.1: an exact component-profile criterion for Replacement after
  finitely many canonical elementary atom lifts are named.
- Theorem 6.1: the sharp universal preservation threshold is cofinality greater
  than omega for one name, and greater than the continuum for at least two.
- Corollary 6.3: at the cutoff aleph_2, universal two-name preservation is
  equivalent externally to CH. This is not a proof or refutation of CH.
- Theorems 7.5 and 7.7: exact Collection and full transitive-reflection criteria.
- Theorem 3.6: parameter-definability is exactly small movement of atoms.
- Corollary 7.9: two individually safe named automorphisms can be jointly unsafe.

Section 9 gives a concrete ProveIt formalization route. Section 10 proposes
12 further research questions. Appendices give an explicitly bounded formula,
a dependency audit, and the finite-check scope.

## Proof and novelty status

The kernel-ideal model construction is established prior work, credited to
Bokai Yao. The article supplies complete mathematical proofs for its proposed
component-profile and finite-signature classifications. Independent review and
literature-priority verification remain outstanding. No Lean formalization or
machine-checked set-theoretic proof is included. Neither Elliot Glazer nor
Bokai Yao is an author or endorser of this manuscript.

The models are defined externally over a set of atoms in a well-founded ambient
set theory with choice. The atoms are internally a proper class of the cutoff
model. Elementarity and reflection are treated as schemes; no universal
first-order truth predicate or set of all class maps is assumed.

## Files

- `article.tex`, `article.pdf`: manuscript and compiled PDF.
- `build.sh`: three-pass pdfLaTeX build.
- `verify_finite.py`: standard-library Python regression tests.
- `verification_results.json`: recorded successful test run.
- `SOURCE_AUDIT.md`: source provenance and contribution boundary.
- `BUILD_AUDIT.json`: build, PDF checks, and delivered-file hashes.

Run `bash build.sh` to rebuild the PDF. A standard TeX Live installation with
mathpazo, microtype, hyperref, cleveref, and the usual AMS packages is sufficient.
The PDF timestamp can differ on rebuilding; bit-for-bit reproducibility is not
claimed.

Run `python3 verify_finite.py --output verification_results.json` to repeat the
finite tests. Python 3.10 or later is required. The delivered run passed 125,582
exact assertions, including 4,456 component swaps and 69,632 marker-translation
comparisons. These are finite regression checks, NOT verification of the
infinite-cardinal theorems, the Replacement scheme, or any independence claim.
