# Verification scope

The report supplies the all-input mathematical proofs. Exact standard-library checks corroborate every literal source row, net arc, one-step exported coefficient, complete main-example trace, and declared sparse witness coordinate.

Main construction:
- 528 source rows, 771 transitions and the full 539-place incidence structure checked
- Source macro loop bodies checked symbolically over arbitrary nonnegative affine inputs
- All 388 reset firings and all 328 source instructions replayed
- All 922664 canonical and 1794888 projected-trace witness coordinates independently reconstructed, with omitted coordinates fixed to zero
- Natural all-duration fixture at N390 verified and the nonnegative-real N389 counterexample evaluated using exact rational arithmetic
- Generic weighted consume-reset-produce overlaps and constant-bearing affine loaders checked

Optional constructions:
- All 8408 physical prime-source rows independently reconstructed from the finite macro templates
- Direct two-counter net checked by incidence-preserving comparison with a separately generated specification
- Both shared-arc nets checked transition by transition, including all markers and forced return routes
- All 446 shared three-counter firings replayed and all terms of its canonical witness checked
- The large raw_A=64 duration and peak independently recomputed from all 328 proved prime-macro summaries; no enormous physical trace or full-horizon witness is claimed

The package includes every checker and its readable JSON receipt. Tests use exact integers or fractions, not floating-point tolerance. They are ordinary mathematical and executable verification, not a Lean/Rocq formalization or a proof of worldwide novelty.

The PDF was compiled successfully without unresolved references or overfull-box warnings. Every page was rendered and visually inspected. The archive excludes build caches, logs, third-party papers, and unrelated earlier substrate material.
