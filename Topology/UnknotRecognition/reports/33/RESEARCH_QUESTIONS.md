# Further research agenda

The article's Section 12 gives the full discussion and proof obligations.

1. **Direct connected-heap enumeration.** Avoid enumerating many connected core
   regions containing the same terminal-rooted trace. Supply an injective dynamic
   code and decoder, not an informal parallel-search argument.
2. **Tight next-parent incidence.** Determine whether the uniform constant 36
   can be reduced using local rotation, over/under, and boundary-identification
   constraints; finite observed maximum nine is not a proof.
3. **Triangle-covered core regions.** Exploit the additional structure of the
   connected `3k+2` core bound without assuming that every required triangle is
   already a face in the initial diagram.
4. **Compatibility-pruned subset generation.** Replace generate-then-reject
   combinations with a complete independent-set iterator, and measure actual
   production overhead as well as node counts.
5. **Certified reuse between regions.** Prove a sufficient memoization key
   including the relevant pairing, previous layer, remaining depth, and
   admissibility restrictions. Preserve a polynomial-space mode.
6. **Mutable layer transactions.** Integrate disjoint patches with the existing
   production journal, local terminal scanning, exception rollback, and original
   dart labels. Compare against the current mutable baseline.
7. **Polylogarithmic policy-gap/core families.** Bound the actual-run unlocking
   budget and residual crossing count on explicitly specified diagram families,
   accounting for the cost of obtaining the promised representation.
8. **Controlled crossing increases.** Extend causal provenance to newly created
   ports, with explicit bounds on the number and encoding of created sites.
9. **Policy-independent residual control.** Prove that an eligible reduction
   policy cannot destroy all short subsequent witnesses, or find a verifiable
   potential identifying a safe policy.
10. **Larger local terminal certificates.** Parameterize terminal-support size
    and study braid-kernel, disk, or structured multi-move shortenings without
    hiding a global invariant oracle inside the terminal test.
11. **Hierarchy-operation dependency layers.** Before applying forest counting
    to hierarchy methods, establish encoded state sizes, conservative supports,
    commutation, and a bounded next-parent candidate count.
12. **Matching parameterized lower bounds.** Study the exact local unlocking
    language under classical one-component planarity and its restricted move
    set; whole-diagram defect hardness does not transfer automatically.
13. **Modular formalization.** Formalize exchange contracts and heights, forest
    encoding, component confinement, core contraction/star invariance, then the
    dart implementation and final search count.

Immediate decision: keep production defaults unchanged. The supplied kernel
measurements do not establish a real-diagram wall-clock improvement. Require
complete regression, replay, budget, and paired end-to-end checks before
promoting the experimental mode.
