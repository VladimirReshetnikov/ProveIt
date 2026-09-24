# Source and claim audit

## Repository

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `110efe9dea646a092a640838515af4ad2d7ee2e0`

The targeted comparison inspected the root README, documentation catalogue,
and relevant portions of:

1. `docs/surreal/omnific-preserving-automorphisms/article.tex`
2. `docs/surreal/omnific-preserving-automorphisms/README.md`
3. `docs/surreal/omnific-preserving-automorphisms/14-automatic-summability-SOURCES.md`
4. `docs/surcomplex/surcomplex-field-automorphisms/article.tex`
5. `docs/surcomplex/surcomplex-field-automorphisms/README.md`

Relevant existing source labels include:

- `opa:as:thm:detect`: scalar detection of Hahn summability;
- `opa:as:thm:ctiso`: automatic strongness from constant-term covariance;
- `opa:as:thm:gaussian`: automatic strongness for valuation-compatible
  Gaussian-omnific automorphisms;
- `saut:thm:torsion`: finite subgroups and real forms;
- `saut:thm:shiftflow`: explicit fixed-shift flows.

These reports are AI-assisted research drafts, not treated as peer-reviewed
certificates. The arithmetic reconstruction and automatic-strongness arguments
needed here are reproduced with attribution in article Section 3. The report's
published-source provenance was also inspected. The source comparison was
focused, not exhaustive over every repository file or historical version.

## Primary mathematical sources checked

- Vincent Bagayoko, Lothar Sebastian Krapp, Salma Kuhlmann, Daniel Panazzolo,
  and Michele Serra, *Automorphisms and derivations on algebras endowed with
  formal infinite sums*, arXiv:2403.05827v2 (2025).
  https://arxiv.org/abs/2403.05827v2
  Imported input: Theorem 3.11 and Proposition 1.45 imply the strongly
  contracting geometric-operator inverse. This part does not require
  characteristic zero; the derivation/exponential correspondence is not
  needed for the main proof in this article.

- Salma Kuhlmann and Michele Serra, *The automorphism group of a valued field
  of generalised formal power series*, arXiv:2107.03362v3, 11 April 2022.
  https://arxiv.org/abs/2107.03362v3
  Context: valued and strongly additive Hahn automorphisms.

- Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra, *Decomposing the
  automorphism group of the surreal numbers*, arXiv:2509.22374v3,
  23 April 2026.
  https://arxiv.org/abs/2509.22374v3
  Context: class-field foundations, strong automorphisms, and the distinction
  between ordinary valued maps and strong maps. No unresolved question in
  that paper is claimed solved merely by this article's classification.

- Keith Conrad, *The Artin–Schreier theorem*.
  https://kconrad.math.uconn.edu/blurbs/galoistheory/artinschreier.pdf
  Theorem 3.1 and Section 4 supply an accessible proof of the classical
  real-closed fixed-field fact for finite automorphism groups. The source PDF
  and relevant rendered pages were inspected. Original Artin–Schreier results
  are identified in the manuscript bibliography.

- The Stacks Project, Fields, Sections 9.10 and 9.26, Tags 09GP and 030D.
  https://stacks.math.columbia.edu/tag/09GP
  https://stacks.math.columbia.edu/tag/030D
  Inputs: algebraic closure uniqueness and transcendence bases. The reduction
  of algebraically closed fields to characteristic and transcendence degree
  is spelled out in the article.

The supplied Wikipedia surreal-number page was used for orientation, not as
an input to a new technical claim.

## Proposed contribution

The central new-to-this-manuscript result is the orbit-product construction
with its full summability and arithmetic inverse, applied to Gaussian-omnific
involutions. It yields coefficient-field conjugacy classification, an exact
integer-part criterion, a sharp 2^continuum family of inequivalent arithmetic
real forms, and an abstract fixed-ring criterion for the standard form.

The classical facts about real closed coefficient fields, the principle of
Galois descent, character Hilbert–90 equations, and constant-term retractions
are not presented as new. The finite quotient and ordinary equation-solvability
propositions are included to explain what fails to detect the newly classified
nonisomorphic rings, not to claim a new general retraction theorem.

A targeted literature and repository search did not identify the exact theorem
package. This is not proof of priority or absence of antecedents. Independent
expert review is needed before any publication or “breakthrough” claim.

## Important boundaries

1. Valuation preservation is an assumption in the Gaussian application.
2. The normalizer is canonical relative to a chosen Hahn monomial section,
   not a proof that the ring defines that section.
3. Archimedean real closed fields need not be Dedekind complete or isomorphic
   to R; this distinction is essential to the cardinality theorem.
4. The class-field fraction argument uses boundedness of every set of surreal
   exponents and is not asserted for arbitrary set-sized Hahn support rings.
5. Exactly 2^continuum classes is a theorem about the valued Gaussian sector.
   The constructed examples remain distinct under arbitrary conjugators, but
   an upper bound for all pure-field involutions is not claimed.
6. Identical finite quotients and integer-coefficient polynomial equation
   solvability do not imply elementary equivalence or matching disequations.
7. The geometric inverse is justified by an established operator-summability
   theorem, not by a topological convergence slogan.
8. The 457 computational assertions are finite checks, not a formal proof of
   the universal theorems. No Lean check or repository build was performed.
