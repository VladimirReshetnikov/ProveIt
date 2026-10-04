# Source and proof audit

## Research basis

1. Elliot Glazer and Bokai Yao, *Reflection Principles in ZFU*,
   arXiv:2602.21970v1 (25 February 2026).
   https://arxiv.org/abs/2602.21970
   Used to identify the research intersection: urelements, Collection,
   full and partial reflection, and the importance of choice assumptions.
   The manuscript does not claim to solve an open problem explicitly posed in
   this paper or reproduce its choiceless separation diagram.

2. Elliot Glazer, *Global choice is not conservative over local choice for
   Zermelo set theory*, arXiv:2312.11902v3 (January 2024).
   https://arxiv.org/abs/2312.11902
   Used for the conceptual importance of extending axiom schemes to formulas
   containing a newly named class function. No proof is copied or extended
   directly from the paper's global-choice construction.

3. Bokai Yao, *Set Theory with Urelements*, doctoral dissertation,
   University of Notre Dame, June 2023; arXiv:2303.14274v3.
   https://arxiv.org/abs/2303.14274
   Definition 24 and Theorem 26 (printed pp. 21-22; PDF pages 28-29) establish
   the ideal-of-kernels construction. Theorem 27 includes relevant cutoff
   examples. Those PDF pages and the following page were inspected as images.
   The base construction and its basic fresh-atom uniqueness argument are
   established prior work and are not claimed as new.

The requested LinkedIn page did not provide usable content during retrieval.
Research interests were established from authored primary mathematical papers;
no current employment or other biographical claims are made.

## ProveIt snapshot and inspected material

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pin: 2b7b388ba81a3355b19a7c2d2fe797e92f572355

Inspected through the GitHub connector:

- `SetTheory/ZF/Lean/ZF/Zf.lean`, lines 1-170.
  Blob SHA: b33db57cfb71e00c50fa3c57ea355ee4a9a4d523.
  Important inspected declarations: Sep_form, Func_form, Image_form,
  Repl_form, ZFax, ZFprov, ZFax_s, and the opening semantic bridges.
  These declarations substantiate the formula-indexed schema interface.

- `SetTheory/BoundedConsistency/README.md`, with a broad initial read and a
  pinned confirmation of lines 1-110.
  Blob SHA: ebb5d1bfa77af47eebb60025adde46f856f21603.
  Important distinctions: external numeralwise complexity bounds; all formula
  occurrences, not just conclusions; externally indexed partial satisfaction;
  no primitive bounded quantifier in the chosen syntax.

- `Algebra/SurrealNumbers/docs/surreal/surreal-self-embeddings/README.md`,
  lines 1-80.
  Blob SHA: 554357db9c5afa97d766a4b77652146f4ed425fd.
  Used for the thematic connection and its explicit unrefereed/not-formalized
  status. No surreal-field theorem from that report is used as a premise.

The repository was not cloned, modified, built, or independently kernel-audited.
The manuscript's formalization section is a proposed extension, not a claim
that the new results already appear as verified theorems in ProveIt.

## Proposed contributions and limitations

The main proposed contribution is the component-profile criterion for full
Replacement in a language naming a finite tuple of canonical atom lifts.
Its consequences include sharp one-name/two-name cofinality thresholds, the
real-marker construction, a CH characterization, and an exact expanded
Collection/reflection spectrum.

The proofs are written in full in the manuscript, but no independent referee
or proof-assistant verification has occurred. Literature search did not
establish comprehensive priority. Therefore the article distinguishes a new
result derived in this investigation from a verified claim of being the first
publication of that result.

The finite Python checks are a regression suite for component swaps and the
marker encoding. They are not evidence sufficient to establish any of the
infinite or logical classification theorems on their own.
