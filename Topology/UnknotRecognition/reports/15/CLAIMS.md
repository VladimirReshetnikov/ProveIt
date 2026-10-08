# Claim boundaries

## Written proofs supplied

The arc-weight grading; dot-derivative Leibniz identity; sharp radical index 2k;
marked algebra splitting and radical-power decomposition; exact minimal-object
profile; invariance of that profile under complete cancellation; finite transfer
and its sharp correction depth; two-pass marked transfer; output-sensitive
composition count; the boundary/survivor parameterized recognition theorem;
and the explicitly hypothetical one-sided model-cover criterion.

The homological perturbation lemma, the arc category, scalar cancellation,
and the unknot-detection theorem are established inputs, properly attributed.
No first-in-literature novelty claim is made for the specialized algebraic facts.

## Implementation evidence supplied

All counts listed in README.md have been executed here. The supplied raw JSON,
logs, seeds, and tests support them. Braid closures were compared degree by
degree against a separately assembled crossing cube. Full matrix homotopy
identities were checked, not merely equality of total ranks.

Timings compare this package's transfer backend to this package's independent
min-fill scalar-pivot baseline. Both favorable and unfavorable cases are
reported. Input construction, generic d^2 verification, and full certificate
construction are excluded from the timed fixed-complex reductions. Timing
repetitions use fresh caches and alternate execution order.

## Not established

- An unrestricted quasi-polynomial or polynomial unknot-recognition algorithm.
- A uniformly favorable scan order or an efficient construction of one.
- A guarantee that boundary width alone bounds minimal multiplicities.
- First-in-literature priority, peer review, or Lean verification.
- A benchmark against the optimized upstream FastScan or a speedup of the full
  recognition pipeline after its cheap filters.
- A run of the full upstream Python or Rust regression suites.
- Realizability of every abstract sharpness witness by a knot diagram.
- A production memory ceiling for the local Python harness.
- A time or memory speedup from the proof-oriented marked-transfer variant.

The cheap survivor oracle is conditional on the input being a valid complex.
It does not itself validate topology. A large predicted survivor count is a
representation lower bound, not evidence that a partial tangle closes to a nontrivial knot.
A budget refusal is never a knot verdict. Negative decisions in the model-cover
proposition require its global covering theorem, which is not supplied here.
