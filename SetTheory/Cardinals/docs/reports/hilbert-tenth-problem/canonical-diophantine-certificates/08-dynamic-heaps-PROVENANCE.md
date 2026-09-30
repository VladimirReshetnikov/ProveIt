# Provenance and verification scope

Date: 30 September 2026.

## Repository snapshot actually inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: `4e128356d0ef75308be8ed405d89aea2ffdb8a57`

The GitHub connector was used to inspect the repository tree and these sources:

1. `Computability/HilbertTenthProblem/README.md`.
2. `Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`.
3. `Computability/CombinatoryLogic/README.md`.

The trace source exposes `boundedForall_dioph`, `exactIter_dioph`, and
`existsExactIter_dioph`. The article does not claim that their ordinary Dioph
contracts imply auxiliary-witness uniqueness. The source was inspected, but
no local Lean build or independent axiom audit was performed. The repository
was not edited. No claims from unrelated repository folders are assumed.

## Primary literature used

- Ben-Sasson, Chiesa, Genkin, Tromer, *Fast Reductions from RAMs to Delegatable
  Succinct Constraint Satisfaction Problems*, ePrint 2012/071. Metadata and
  parsed PDF text, especially section 4.1, were inspected. Sorting by
  address/time and checking consecutive accesses are established prior ideas.
  https://eprint.iacr.org/2012/071
- Ben-Sasson, Chiesa, Genkin, Tromer, Virza, *SNARKs for C*, ePrint 2013/507.
  Primary abstract and metadata were inspected for the TinyRAM implementation
  context. https://eprint.iacr.org/2013/507
- Batcher, *Sorting Networks and Their Applications* (1968). Publication
  metadata was checked; the standard bitonic correctness argument and network
  count are supplied in the article and tested in the implementation.
  https://doi.org/10.1145/1468075.1468121
- Goodrich, *Zig-zag Sort* (2014), arXiv:1403.2777. Primary abstract establishes
  the deterministic constructive O(N log N) sorting-network dependency.
  That network is not implemented in this archive.
  https://arxiv.org/abs/1403.2777
- Cantone, Casagrande, Fabris, Omodeo, *The Quest for Diophantine Finite-fold-ness*
  (2021), primary journal abstract and metadata.
  https://lematematiche.dmi.unict.it/index.php/lematematiche/article/view/2044
- Cantone, Cuzziol, Omodeo, *Six Equations in Search of a Finite-fold-ness Proof*,
  arXiv:2303.02208v3 (2024), primary abstract and metadata.
  https://arxiv.org/abs/2303.02208v3
- Lafont, *Interaction Combinators*, Information and Computation 137(1),
  69–101 (1997). Primary publication metadata identified the future adapter
  target. Its complete rule-level semantics was not implemented or audited.
  https://www.sciencedirect.com/science/article/pii/S0890540197926432

## What was constructed here

The natural-number comparator and scan assembly, exact accounting, uniqueness
proof, canonical gating lemma, nominal orbit theorem, local compiler proof,
height analysis, pointer-only simulation, safety reduction, Python memory
compiler, and executable test suite are given in the article/archive.
These are presented as research-draft constructions, not as authenticated
historical firsts. The sorting architecture and universality of linked-stack
computation are not claimed as newly discovered facts.

## What was checked

The complete memory compiler is executable. `tests/receipt.json` records the
actual run: 4,681 exhaustive short logs; 40,347 sorting permutations; 82 guarded
residual cases; additional valid and invalid logs; individual witness mutations;
and 12 fresh-name-renaming pairs. These are finite checks, not a substitute for
unbounded proof. The sum-of-squares example is exactly evaluable in integer
arithmetic. The final PDF was compiled with pdfLaTeX, rendered and visually
inspected; no text was found outside its physical page bounds.

## What was not checked or claimed

No complete generic heap-language arithmetizer, no full interaction-combinator
adapter, no Lean checking, no independent referee verification, no
fixed-arity single-fold MRDP theorem, no global graph-isomorphism quotient,
and no uniqueness claim for ordinary MRDP/list-coding compression.

The finite-history quotient preserves time order, chosen rules, occurrence
roles and birth-slot order; it removes only fresh object-name permutations.
Global freshness excludes name reuse. The semantics is over nonnegative
integers, not arbitrary integers, reals, or finite fields.
