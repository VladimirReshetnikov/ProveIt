# A sharper five-step graph-tower bound

Build the report with pdflatex five_step_refinement.tex (twice).

Replay the finite searches:
    c++ -O3 -std=c++17 depth_four.cpp -o depth_four
    ./depth_four
    c++ -O3 -std=c++17 small_benchmarks.cpp -o small_benchmarks
    ./small_benchmarks

The larger search tests every signed-permutation representative paired
with every projective point of the depth-at-least-four locus. Its counts
are for inspected pairs, not plane orbits. Small search output gives the
prime, the counts with/without zero, the maxima with zero/nonzero/simple,
and the three additional steps of a simple witness.

Run python3 symbolic.py (SymPy required) to replay the exact identities,
the modular test at 761, and direct witness evaluations. Expected outputs
are supplied alongside each program.
