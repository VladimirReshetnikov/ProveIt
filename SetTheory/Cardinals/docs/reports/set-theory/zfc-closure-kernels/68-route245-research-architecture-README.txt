Supplemental architecture investigations
========================================

These are independently reproducible auxiliary results from the investigation
that produced the separate 245-state machine. The successful machine retains
the original logical theory and original AX semantic word. None of the
additional experiments below is needed as a premise of its correctness proof.

Use Python 3.10 or later, standard library only. Do not use Python's -O option:
these scripts deliberately express finite proof obligations as assertions.

1. Exact eight-row permutation witness translation

   python verify_permutation_selectors.py

   axiom_permutation_lemma.md states the generic proof-program translation
   k_pi(j)=9-pos_pi(j), with exactly25 commands and54 encoded fields per
   logical axiom leaf. The script checks all40320 permutations and322560
   selectors in a symbolic stack model. It does not claim a binary compiler
   theorem. Original logic definitions are preserved in reference/.

2. Exact semantic-word resegmentation

   python verify_semantic_resegmentation.py --write-report results/semantic_resegmentation_check.json

   Both the original702-call AX spelling and the new533-call spelling expand
   to the exact same1270 finest closed AST tokens. The checker independently
   derives these tokens from the immutable226-node source AST; it ignores
   the provided fine_atom_expansions map. Dynamic programming proves533 is
   the minimum number of calls in this fixed44-atom vocabulary. Equality uses
   implication plus THREE increments, which the checker explicitly verifies.

   Fewer calls do not imply fewer machine states: the orientation-valid seed
   supplied as AX_seed.json needs147 shared grammar rules, whereas the old
   grammar uses127. The mandatory old non-AX entry/boot closure has51 rules,
   leaving76 AX-private rules. No two of the127 original grammar words have
   equal fine expansions; no two of the44 atoms do; and there is no cross
   grammar/atom collision. Future search should choose segmentation and
   shared grammar productions jointly, keyed by exact expanded words.

3. Finite-field affine resource obstruction

   python verify_affine_resources.py --recompute --write-report results/affine_resource_check.json

   This recomputes all12 affine closures and independently checks their
   certificates for p=2,3,5,7. It reparses the pinned6459-node Prog254.v and
   verifies the inherited natural-category invariant first. It has no bound
   on concrete register values. It verifies all8391 guarded source cases.

   At each of6456 nonempty abstract sites, write A_i for the register-only
   affine space. Adding absolute header position H and spare count K gives
   exactly the one-dimensional fiber

        E_i = {(r,H,K): r in A_i, H + sum(r) - K =15 mod p}.

   Adding pointed header distance d and K instead gives exactly

        E_i = A_i x F_p^2.

   The d update includes the three full-pointer carry-overflow cases, as well
   as positive decrements. These findings concern the ORIGINAL Prog254 control
   graph and the Prefix246 frame resource interpretation. They do not assert
   that all abstract points are concretely reachable, or that no nonlinear
   invariant could help. No new zero/nonzero guard exclusions were obtained.
   With --recompute, the least fixed point of the stated reduced affine
   analysis is regenerated from the exact root, not merely checked closed.

Input provenance
----------------

ProveIt was pinned to commit c6bf052c70bbbafba8c39370a6a2d123f57cd2c1.
The source register tree SHA256 is
1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746.
The old-label Prefix246 table SHA256 is
303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee.

reference/Prog254.v and the natural product invariant originate in the
inherited zfc-beyond246 intake. The semantic grammar, symbol map, and baseline
bootstrap originate in the zfc-below246-research v2 intake. Enum254.v,
L1_Comp254.v and Codes254.v are preserved from jeff87654/busy-beaver zf-254.
source_graph.py adapts the prior intake's independent source parser and
product-invariant checker; its attribution remains at the top of the file.

No invalid provisional tree-cost experiments are included. No state count
reported for an abstract spelling is described as a certified Turing machine.
