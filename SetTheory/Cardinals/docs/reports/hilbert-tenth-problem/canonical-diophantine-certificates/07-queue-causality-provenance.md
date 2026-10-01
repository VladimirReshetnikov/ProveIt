# Provenance and verification boundaries

Prepared September 30, 2026.

## Repository inspected

ProveIt: https://github.com/VladimirReshetnikov/ProveIt
Pinned snapshot: 725d2ebb6909fe11a13a92354c0f47367a3cbbf5

The repository tree, root README, HilbertTenthProblem README, and Lean/MRDP.md
were inspected through the GitHub connector. The article uses the repository's
MRDP interfaces as context and an integration target. Its queue constructions
and memory-dimension proof are independent mathematical arguments.

Repository documentation reports axiom audits. This package did not rerun a
Lean or Rocq build and does not claim an independent kernel audit.
No files were committed or pushed to the user's repository.

## Literature

Primary research sources consulted include:

- Matthew Cook, Universality in Elementary Cellular Automata, Complex Systems
  15 (2004), 1–40. The cyclic-tag definition and simulation on printed pages
  7–8 were inspected, including page images.
- Damien Woods and Turlough Neary, On the time complexity of 2-tag systems
  and small universal Turing machines, FOCS 2006, arXiv:cs/0612089.
- Mario Carneiro, A Lean formalization of Matiyasevič's Theorem,
  arXiv:1802.01795.
- Dominique Larchey-Wendling and Yannick Forster, Hilbert's Tenth Problem in
  Coq, FSCD 2019, DOI 10.4230/LIPIcs.FSCD.2019.27.
- Pau Atela and Jun Hu, Commuting polynomials and polynomials with same
  Julia set, arXiv:math/9504210. Broader centralizer context only; the proof
  required in the article is self-contained.
- Domenico Cantone, Luca Cuzziol, and Eugenio G. Omodeo, Six equations in
  search of a finite-fold-ness proof, arXiv:2303.02208v3 (2024).

Full bibliographic links are in article.tex and article.pdf. The search was
not an exhaustive novelty review. It does not establish global priority for
the exact constructions or rule out related unpublished work.

## Companion manuscripts

Earlier Library manuscripts on witness-faithful compilation of Petri nets,
FRACTRAN and SKI, and on saturation of concurrent counter schedules were
consulted to avoid repeating those constructions. They are cited as
unpublished companion manuscripts, not treated as independently audited
publications or proof dependencies. They are not redistributed in this ZIP.

## What was executed

- The complete standard-library Python test suite in tests/run_tests.py.
- Independent exact evaluation of the four positive JSON example certificates.
- Integer-only general deletion-tag interpolation/compiler checks.
- pdfLaTeX compilation and PDF rendering for layout inspection.

The detailed actual test counts are in tests/results.json. No numerical
approximation, OCR-generated mathematics, external Diophantine solver,
or unreported Lean proof is used as a substitute for the article's proofs.

The general fixed-read FIFO-network theorem is proved in the article, but a
full multi-queue network-table compiler is not included. Executable coverage
is cyclic-tag and general one-queue deletion-tag compilation.

## Claim status

The article proves explicit bounded certificate theorems and a sharply
specified polynomial word-memory obstruction. It does not claim a resolution
of the general finite-fold/single-fold Diophantine problem, an optimal
variable bound for arbitrary Diophantine representations, or a direct
T+1-variable encoding of arbitrary cellular-automaton space-time diagrams.
