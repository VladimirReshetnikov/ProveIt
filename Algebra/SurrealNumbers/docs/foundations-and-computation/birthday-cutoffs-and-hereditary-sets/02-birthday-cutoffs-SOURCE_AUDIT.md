# Source and novelty audit

Audit date: September 22, 2026.
Repository: https://github.com/VladimirReshetnikov/Surreal
Pinned commit: 4f2645599121fa872c7104995e47f86f0382351f

## Repository scope

The connected GitHub tool was used to inspect the pinned repository tree,
root README, documentation index, catalogue source docs/manifest.tex, and the
foundations report at docs/foundations-and-computation/foundations/article.tex.
The incoming-report directory and its README were also inspected. Its pinned
listing contained only README.md, not an additional pending manuscript archive.
The audit was topical; it was not a complete line-by-line audit of every file
or proof in the repository and did not use a local Lean build.

The foundations report already discusses the Chen--Hamkins--Yang announcement
of a first-order birthday-enriched surreal structure bi-interpretable with
set theory. The current article explicitly attributes the global construction
to that work. No claim is made that the repository lacks the global result.

The exact bounded image H_{kappa(lambda)}, the literal-ordinal collection
sentence, the noncardinal-cutoff elementary-extension obstruction, and the
Prikry-based cofinality non-recognition formulation were not identified in the
material inspected. This is a bounded search result, not a certification that
no equivalent formulation exists anywhere in the repository or literature.

## Primary literature inspected

1. Hamkins's announcement, reporting joint work with Junhong Chen and Ruizhi
   Yang, "Surreal arithmetic is bi-interpretable with set theory," posted
   February 4, 2026 for the March 13 CUNY Logic Workshop:
   https://jdh.hamkins.org/surreal-arithmetic-cuny-logic-workshop-march-2026/

   The linked 123-page slide deck was inspected for the first-order structures,
   global coding, and axiomatic conclusions, including visual inspection of
   the pointed-relation coding slide. Relevant material is on PDF pages
   96--107 and 108--122. The presentation labels the axiomatic program as work
   in progress. No published completeness of that program is assumed here.

2. Bournez and Guilmant, arXiv:2201.08199, "Surreal fields stable under
   exponential and logarithmic functions." Theorems 1.1--1.2 restate the
   classical ring/field cutoff and real-closedness results used here.
   https://arxiv.org/abs/2201.08199

3. Poveda, Rinot, and Sinapova, arXiv:1912.03335v2, "Sigma-Prikry forcing I:
   The Axioms." Lemma 2.10 and Section 3.1 supply the classical preservation
   properties and normal-measure Prikry forcing used in the application.
   https://arxiv.org/abs/1912.03335

4. Rangel and Mariano, arXiv:1911.12726, "An algebraic (set) theory of surreal
   numbers, I." The introduction was examined for the scope of its distinct
   categorical foundational program. The current article does not claim to
   settle that program.
   https://arxiv.org/abs/1911.12726

Classical books by Conway, Gonshor, Jech, and Marker, and the van den
Dries--Ehrlich paper, are cited for their standard background theorems. This
package does not redistribute those works or the repository's manuscripts.

## Verification boundary

The finite verification program was executed successfully. LaTeX compilation
completed without unresolved references, overfull boxes, or reported LaTeX
warnings. The PDF was rendered and its pages visually checked. These are
implementation and presentation checks, not independent mathematical peer
review or formal proof-assistant certification.

The main proofs are included in the article. The bounded interpretation is
one-way; local bi-interpretability with an unexpanded H_kappa is not asserted.
The elementary-inclusion criterion is necessary, not claimed sufficient.
The translated Power Set axiom detects strong-limit behavior, not regularity
or full ZFC. Forcing invisibility is a conditional application of the
classical measurable-cardinal Prikry theorem.
