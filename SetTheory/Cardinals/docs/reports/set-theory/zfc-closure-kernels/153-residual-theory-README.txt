Theory artifacts
================

formalism_results.tex is an include-only mathematical section.  It gives
the exact retained native calculus, a self-contained HC interpretation
including the full support-bearing seed, the arbitrary-term fourth-field
obstruction, and two new Peirce countermodels with their precise scope.
It also states which strengthened-gate calibration questions remain open.

counter_salt.tex is an include-only section proving correctness of the
208-DAG-node source repair.  It supplies the all-natural comparator and
reader contracts, exact altered command semantics, every proof compiler
block, and the distinction between that result and an unproved 218-state
construction.  The portable source generator and source replay artifacts
are supplied elsewhere in this packet by the independent-encoding work.

Run the following from the packet root with ordinary Python 3.  No packages,
repository checkout, network access, or external tools are needed.  Do not
use -O or -OO: the checkers intentionally require assertions to be enabled.

  python theory/compound_fourth_obstruction.py --out theory/compound_fourth_obstruction.json
  python theory/peirce_hc_countermodels.py --out theory/peirce_hc_countermodels.json
  python theory/counter_salt_blocks.py --out theory/counter_salt_blocks.json

The first two checkers exhaust the finite algebra premises.  Arbitrary
terms and arbitrary derivations are handled by the mathematical proofs,
not by a claim that finite enumeration proves an unbounded theorem.
The third checker runs bounded source-tree contracts independently of
the compiler CFG, then symbolically checks the proof-block compositions.
The JSON files are reproducible receipts.  None is a proof-assistant
kernel certificate or a binary-runtime certificate for the repaired source.

For LaTeX inclusion the sections require amsmath and amssymb.  They contain
no nested file inputs, external images, or absolute paths.
