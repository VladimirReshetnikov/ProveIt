# Research audit

Date: September 22, 2026.
Repository: https://github.com/VladimirReshetnikov/Surreal
Pinned commit: `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`.

## Repository material consulted

The root README, `docs/README.md`, `docs/manifest.tex`, the incoming-report
inventory, and the README/source of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/` were reviewed.
The existing report distinguishes two inequivalent theories: bounded-operator
coefficients on an ordinary Hilbert-coefficient Hahn space, and row/column-finite
matrix coefficients on a finite-coordinate Hahn space.

Its Part I already states the constant-normal spectral formula
sigma_C(T) union (acc sigma_C(T) + m), with divisibility as a standing convention.
The relevant README statement occurs at lines 67-70 at the pinned revision.
This is explicitly credited as an overlap, not presented as a new theorem here.

The existing source also mentions Drazin spectra in its related-work paragraph
and cites Boasso. Thus a claim that the repository contains no Drazin mention
would be false. The inspected passage does not state the arbitrary-algebra
inverse-descent equivalence or the exact ramification/value-group criterion
proved in the present article.

A GitHub code search returned zero Drazin hits but had `incomplete_results=true`.
That result was not used to prove absence. A search of the fetched catalogue
found no Drazin occurrence; a search of the fetched spectral source found its
related-work paragraph and bibliography. No exhaustive all-history or all-file
absence theorem is asserted.

Direct pinned reference:
https://github.com/VladimirReshetnikov/Surreal/tree/048b72cf7cbfc8ab246e4f73788c10460cb3f6e0/docs/surcomplex/infinite-dimensional-hahn-spectral-theory

## Literature and classical inputs

- M. P. Drazin, *Pseudo-inverses in associative rings and semigroups*,
  American Mathematical Monthly 65 (1958), 506-514. Original bibliographic
  reference; its definition and identities are also documented in the primary
  papers below. This audit does not claim a full reading of the original paper.
- E. Boasso, *Drazin spectra of Banach space operators and Banach algebra
  elements*, https://arxiv.org/abs/1307.6942 . Relevant definitions, resolvent
  pole characterization, and spectral mapping were checked.
- E. Boasso, *The Drazin spectrum in Banach algebras*, published 2012,
  https://arxiv.org/abs/1309.5025 . The empty-Drazin-spectrum/algebraicity
  characterization is classical, not new here.
- J. J. Koliha, *A generalized Drazin inverse*, Glasgow Mathematical Journal
  38 (1996), 367-381, https://doi.org/10.1017/S0017089500031803 . Its generalized
  condition is distinguished from finite-index Drazin invertibility.
- H. Gonshor, *An Introduction to the Theory of Surreal Numbers*, Cambridge,
  1986; L. van den Dries and P. Ehrlich, *Fields of surreal numbers and
  exponentiation*, Fundamenta Mathematicae 167 (2001), 173-188,
  https://doi.org/10.4064/fm167-2-3 . Normal-form and field foundations are inputs.
- E. Kaplan, L. S. Krapp, M. Serra, *Decomposing the automorphism group of the
  surreal numbers*, https://arxiv.org/abs/2509.22374v3 , version dated April 23,
  2026. Related contemporary Hahn/surreal automorphism context, not a source
  credited with the new spectral statements.

Targeted searches included combinations of Hahn, Drazin, Laurent inverse,
surreal spectrum, and ramified spectral mapping. They did not locate the exact
combined theorem package. A lack of search hits does not establish priority.

## Attribution boundary

Classical: Drazin identities, finite-pole Laurent recurrences, ordinary complex
Drazin polynomial spectral mapping, the finite nilpotent ceiling calculation,
Hahn positive-support lemmas, normal forms, and ordinary Banach spectral tools.

Repository overlap: the constant-normal halo formula. Its operator category
and standing assumptions are preserved when comparing statements.

Candidate contribution: the arbitrary-infinitesimal inverse descent in the
original arbitrary value group; the resulting all-unital-complex-algebra
constant-pencil halo classification; exact inverse valuation; and the complete
ramification criterion identifying every missing polynomial-image valuation.
The Banach algebraicity result is a new Hahn interpretation of a classical fact.

## Verification and limitations

The article supplies proofs of its claimed new results. The verification suite
uses exact arithmetic but tests only finite examples and finite truncations.
No Lean proof, independent peer review, complete literature review, or settlement
of a named published conjecture is claimed. The named-algebra spectrum must not
be confused with a spectrum in all linear endomorphisms of a chosen vector space.
Actual vector nonsurjectivity is proved independently for the two examples.

The repository was read, not edited. No private repository content or downloaded
third-party source manuscript is redistributed in this package.
