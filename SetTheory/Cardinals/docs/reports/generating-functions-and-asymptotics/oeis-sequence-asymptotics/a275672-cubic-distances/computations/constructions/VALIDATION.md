# Validation record

- Compiler: g++ 13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04), C++17, optimization -O3.
- All five C++ programs compiled successfully with the included Makefile.
- The independent standard-library Python verifier passed all 24 table certificates and all three original n8/n9/n10 article certificates.
- It recomputed cube membership, unique points, positive squared distances, pair counts, full distance inventories, and distance-to-point-index mappings.
- The packaged n10 reproduction command regenerated exactly the original 14-point certificate at 5858 iterations from the immutable 13-point starting certificate, then independently verified all 91 distances.
- Earlier deterministic checks also reproduced the original n9 certificate at 109517 iterations and the original n11 adaptive certificate at 1975 iterations.
- The n8 figure was rendered and visually inspected; labels, legend, and distance counts were checked.

Heuristic failure is not an upper-bound certificate. Exactness and upper bounds belong to the separate exact-search results and mathematical proofs.

The expanded neighborhood source was also compiled, and the n12 reproduction command regenerated both the original 15-point adaptive witness and the new 16-point witness point-for-point. The latter used 10231 deterministic iterations.
