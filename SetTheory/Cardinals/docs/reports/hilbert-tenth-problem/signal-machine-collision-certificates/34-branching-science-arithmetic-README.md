# Bounded-horizon positive-integer certificates

Frozen on 4 October 2026 for independent arithmetic audit.

For one fixed deterministic two-counter program, with E transition edges including an absorbing halt edge and Z zero edges, each fixed horizon T>=1 has a single explicit quartic polynomial certificate with:

- 2 native positive inputs (counter values plus one)
- T(E+2) positive witnesses
- T(E+Z+4)+1 residual equations before sum-of-squares bundling
- a unique full witness tuple exactly when halt is reached by horizon T

A first-halt-exactly-T variant adds one residual and no witnesses. Horizon zero is handled separately.

Files: `PROOF.md`, the newly authored and inspected `static_algebra.py`, exact successful evidence in `evidence/static_checks.json`, and the pinned frozen physical predecessor under `dependencies/`. `MANIFEST.json` pins all content files.

The horizon indexes a family whose arity grows with T. This is not a fixed-arity polynomial representation of unbounded halting. Halt-loop padding is virtual arithmetic bookkeeping. Native inputs are not arbitrary physical coordinates. The physical corollary uses the separately proved geometric encoding and Report 64 compiler; the arithmetic theorem itself does not depend on that physical proof. No upstream scientific programs, physical simulations, counter-machine interpreter, or proof assistant were executed.
