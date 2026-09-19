# Verification notes

## Proof-critical checks

1. Conditions use strict finite cost < b, while the limit may have cost = b.
   Padding is performed at a finite condition, where positive slack exists.

2. Arbitrary first-coordinate or second-coordinate extensions can be lifted
   only by copying the newly added suffix to the other coordinate. This
   preserves cost exactly.

3. In the bridge lemma every input has dense convergence on both coordinate
   cylinders. If a cylinder of divergence exists, the construction takes
   it instead. No-splitting by itself is insufficient.

4. The same finite suffix is constructed for every computation on a finite
   path, by extending it successively. All earlier convergences persist.

5. Each one-bit pair is a separate alternative extension of the padded
   stems. One does not accumulate the costs of all edges along the path.

6. The finite padded stems are fixed for all inputs of the common function.
   The search program hardcodes those finite stems; it receives no infinite
   oracle advice. Its termination follows from the proved density condition.

7. The construction's negative existential tests are explicitly assigned
   their jump complexity. A split is Sigma-1; existence of an input and a
   no-convergence cylinder is Sigma-2. The second jump suffices.

8. The weighted counting proof takes N to infinity before the finite cutoff
   M. It does not assume a computable modulus for the infinite error tail.

9. Individual genericity, not mutual genericity, is asserted.

10. The infimum theorem uses a robust block code I(Z), not a raw copy of Z.
    All coarse descriptions of the coded component compute Z nonuniformly.

11. The theorem concerns a least representative, not the absence of minimal
    representatives. Uniform and nonuniform classes can be different even
    though their Turing-degree spectra agree.

12. Total numerical coarse descriptions and binary targets are handled
    explicitly. Errors and partial divergence are not interchanged.

## Executed diagnostics

The recorded JSON contains the actual exact test results. In particular:

- Six bridge graphs, through 128 vertices, were connected.
- All 65,536 Boolean labelings of the 16-vertex graph were examined.
- Exactly two avoid unequal labels on a legal edge: the constant labelings.
- A disconnected partial-domain example passes no-splitting but fails
  constancy, detecting the need for the dense-convergence hypothesis.
- Cost preservation, affordable one-bit changes, the finite tail estimate,
  and block majority decoding were checked with exact fractions.

## Limits

These diagnostics are not a proof checker for the infinite statements.
There is no computed sample of the final noncomputable sets, no Lean file,
no independent referee certification, and no claim of first publication.
The ordinary English proofs are the basis for the mathematical assertions.
