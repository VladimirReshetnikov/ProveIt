# U/E tag-swap research

This is a separate numerical-presentation experiment, not an additional successful machine at or below 194 states.

`tag_swap_proof.tex` is a mathematical proof fragment. It swaps residues 2 and 3 for universal quantification and equality, translates both formulas and variable labels recursively, and handles the nonmonotone restricted-rho condition through the cited unrestricted-rho derivation. It does not change the target consistency statement by simply replacing PA with a weaker theory.

`tag_swap.py` independently checks the complete free-term AX effects for H and GDH, including all nine endpoint registers, scratch preconditions, eleven stack entries and the actual fourth operand. Reproduce the source checks and twelve grammar variants without altering the saved receipts:

```sh
python3 -B tag_swap.py --output /tmp/tag_swap_replay
```

The 190-token AX words become 202 tokens. The saved 90-second search made 830,774 proposals with 253,165 accepted moves. It reported best effective price 65: a nominal 199-state allocation with 134 fixed controls. This search uses atomic copy macros and does not contain the expanded-copy entry error found in the separate gate search.

However, its best score uses a matching bound rather than a compatible-fold proof at that cost. The independent audit in `exact_price.json` reconstructs the winning GDH grammar, checks all 3,683 resolved source instructions against its tag-swapped seed, and finds 208 reachable raw controls (134 fixed plus 74 readers). Of eleven fold opportunities, at most six can be applied simultaneously under the checked local scheme, giving **202 controls**. The optimistic matching count of nine does not compose.

No arbitrary-register literal runtime or blank-startup certificate is asserted for this 202-control object. Neither 199 nor 202 is advertised as a new calibrated busy-beaver bound. The useful positive result here is the alternative numerical syntax and its source identities; the successful deliverable remains PA194GS.

The optional inherited C++ search can be replayed from `search/` with a C++17 compiler and the saved seeds, leaf attributes and fixed table. Its `run1.log` is historical search evidence with the price limitation above. The main package's licenses and provenance apply.
