# Half-integer steps in wide three-frequency progressions

Exact zero-free lengths for ±{2n,(d+2)n,(2d+2)n}, for every odd integer
d ≥ 5 and positive integer n. Both residue classes of d mod 4 are covered.

* half_integer_gaps.tex / .pdf: theorem, proof, and exact formulation.
* certify_family.js, minus.json, plus.json: fixed exact interval witnesses.
  Run node certify_family.js --minus and node certify_family.js --plus.
  Replay uses integer arithmetic only.
* guess.js: optional numerical proposer. Append --emit to regenerate
  the corresponding rational witness file, then run the ordinary replay.
* certify_2712.js: independent algebraic certificate for the 5/2 ratio.
  Run node certify_2712.js. Only the displayed diagnostics use floats.
* replay.txt: output of the two exact replays and the independent check.

No third-party Node.js dependencies. Compile with pdflatex twice.
