# Bounded S6 relation search: incomplete

The target is the exact primitive weight-seven vector `F7` equivalent to the existing `cycloquot:conj:S6` at ProveIt commit `5a790187c8e186e41e2b990b4941cb7a1a3c7b6b`.

The generated system contains 51,244 distinct imaginary double-shuffle rows from factor-weight splits (1,6), (2,5), (3,4), including the permitted single-divergence Li_1(1) rows, and two convergent Cayley rows. It covers all 24,514 free imaginary word coordinates. The letter convention is the source convention: `-1 = dt/t`, and `j=0,1,2,3` denotes `i^j dt/(1-i^j t)`.

The two Cayley seeds are the words of `g_(6,1)` and `g_(1,6)`: `[-1,-1,-1,-1,-1,1,1]` and `[1,-1,-1,-1,-1,-1,1]`.

An exploratory elimination modulo 2,147,483,647 was interrupted before completion. At the last recorded checkpoint it had made 8,500 pivots, matrix fill had reached 29,853,917 entries, and the target had 393 remaining terms. This is **not** an exhausted row-span calculation. It gives no membership or nonmembership conclusion. No rational certificate and no separating functional for the enlarged system was produced. The S6 and S8 conjectures retain their existing status.

`STATUS.json` records the exact incomplete scope. `generation.json` records matrix-generation counts. `generate_rows.py` and `word_algebra.py` regenerate the exact integer input. `modular_search.cpp` is only an exploratory finite-field search program, not a trusted proof verifier. A finite-field zero would also require an independently replayed rational certificate before proving the identity.

Large generated matrices, executables, and unfinished search output are scratch artifacts and need not be included in a research-paper package. The metadata and this scope statement are sufficient to document the attempt honestly.
