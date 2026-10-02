# Source audit

Audit date: 2 October 2026. The active ProveIt branch changed during the research session; the report pins its motivating snapshot rather than claiming that `main` stayed unchanged.

## Repository

Snapshot: `439c0a2d9c1052595f3de6a29c11511a24fb2e11`.

1. **A finite wiring obstruction for interaction combinators**
   - Path: `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interaction_combinator_wiring_obstruction.md`
   - Fetched blob: `764c982297342093307a0e831bc0d9ed5084c87f`.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/439c0a2d9c1052595f3de6a29c11511a24fb2e11/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interaction_combinator_wiring_obstruction.md
   - Used for the exact four-agent counterexample and the expressly uncompleted topology-aware arithmetic interface. This report's examples are independently replayed with positive live-port identifiers.

2. **Hilbert-tenth README**
   - Initial fetched blob: `79153a4ed74a8ab63e5f08fb3485a168b20cf8c1`.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/439c0a2d9c1052595f3de6a29c11511a24fb2e11/Computability/HilbertTenthProblem/README.md
   - The 75/87 operation figures are attributed to this repository audit. They were not independently rebuilt or improved by this report.

3. **MRDP interface**
   - `Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`
   - https://github.com/VladimirReshetnikov/ProveIt/blob/439c0a2d9c1052595f3de6a29c11511a24fb2e11/Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean
   - Read at the pinned snapshot. It exposes `Diophantine.mrdp` and `Diophantine.mrdp_iff`, with finitely many natural witnesses and one integer polynomial chosen before the input. Its Lean dependencies and axiom checks were not executed here.

## Primary literature

- Yves Lafont, *Interaction Combinators*, Information and Computation 137 (1997), 69–101. DOI: https://doi.org/10.1006/inco.1997.2643
  - Full text inspected: https://chorasimilarity.wordpress.com/wp-content/uploads/2024/01/ic-lafont-1.pdf
  - Journal page 71: numbered ports and isolated cyclic wires.
  - Journal pages 81–82: all six rules, numbered annihilation conventions, and universality theorem.
  - These diagrams were read as rendered page images. In particular gamma–gamma swaps numbered auxiliaries, whereas delta–delta preserves their numbers.

- Marc de Falco, *An Explicit Framework for Interaction Nets*, Logical Methods in Computer Science 6(4:6) (2010). DOI: https://doi.org/10.2168/LMCS-6(4:6)2010
  - https://arxiv.org/abs/1010.1066
  - https://lmcs.episciences.org/1108
  - Prior permutation-based, loop-aware gluing and execution theory. These concepts are not claimed as new.

- Gustav I. Lehrer and Ruibin Zhang, *The Brauer category and invariant theory*, JEMS 17 (2015), 2311–2351. DOI: https://doi.org/10.4171/JEMS/558
  - https://ems.press/content/serial-article-files/32068
  - Prior matching-composition and loop-scalar framework.

- Manuel Blum, William S. Evans, Peter Gemmell, Sampath Kannan and Moni Naor, *Checking the Correctness of Memories*, Algorithmica 12(2/3) (1994), 225–244.
  - Author's publication listing with full-text links: https://www.wisdom.weizmann.ac.il/~naor/onpub.html

- Moni Naor, Merav Parter and Eylon Yogev, *The Power of Distributed Verifiers in Interactive Proofs*, arXiv:1812.10917 (2018).
  - https://arxiv.org/abs/1812.10917
  - Section 4.3 explicitly discusses RAM verification via access multisets and the earlier memory-checking work. Our exact large-integer certificate is not claimed to improve those randomized protocols' bit complexity.

- Andrew V. Sutherland, *18.783 Elliptic Curves, Lecture 3*, MIT, 12 February 2013.
  - https://math.mit.edu/classes/18.783/2013/LectureNotes3.pdf
  - Background on large-base coefficient packing / Kronecker substitution.

## Priority and evidence boundary

The sharp 2/5–2/3 theorem, its signed recurrence, contextual consequences, and the stated exact bounded compiler are proved in the article. A search of nearby interaction-net, Brauer-category, perfect-matching, and memory-checking literature did not certify historical priority for the exact statements. The report deliberately distinguishes an original derivation supplied here from a claim of being the first publication.

Two rewriting algorithms share one rule table; their comparison independently checks gluing, not the source provenance of the rule table. Direct enumeration of closure graphs is independent of the signed recurrence. The formal induction, not testing through a finite rank, establishes the all-ranks theorem.
