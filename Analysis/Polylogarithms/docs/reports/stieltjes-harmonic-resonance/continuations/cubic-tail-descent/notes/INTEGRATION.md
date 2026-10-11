# Proposed integration

## Destination

A natural report destination is:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/cubic-invariant-tail-descent/`

This is a proposal only. Nothing was written to the live repository.

## Canonical placement

The compact insert `manuscript/cubic-tail-insert.tex` is designed to follow
`chapters/07-mixed-dougall-identities.tex`. It requires the existing amsmath,
amssymb, amsthm and theorem environments, but introduces no private macros.
Its labels have the prefix `cti:`. The full article uses `ct:`.

The full article's invariant Stieltjes/Lerch trace and anchored-primitive
results may be placed in the Hurwitz differentiation/integration chapters,
with a cross-reference to the cubic invariants. These are ordinary
right-half-plane function identities; they do not require periodic
Hadamard products or contact-term conventions.

## Prior dependencies and new deductions

The first mixed resonance is existing manuscript mathematics and must remain
credited to that chapter. The new organizing deductions are:

1. cubic-invariant recurrence and all-degree two-factor depth descent;
2. explicit symmetric quadratic/cubic convolutions, quartic depth-two formula,
   and quintic depth-three formula;
3. meromorphic square/cube formulas for symmetric digamma tails;
4. cubic invariant all-index Hurwitz/Stieltjes and Lerch traces;
5. anchored all-order primitives with explicit removable spectral quotients.

The general tail-to-MZV rearrangement has classical antecedents; credit
Hoffman's 2016 paper rather than describing ordered partitions as a newly
discovered method. Gamma products, Hurwitz Taylor expansions, and elementary
polylogarithm primitive rules are also classical inputs.

## Review gates

Check the analytic master proof and its centered normalization separately
from the recurrence replay. Retain the n=0 term, the weight 2n+1, and the
subtraction before extracting the exceptional linear coefficient. Use
algebraic powers rather than absolute values for complex arguments.

Keep the distinction between the symmetrized convolution and arbitrary
unsymmetrized products. A representation with a particular depth-two value
is not a proof of its arithmetic irreducibility. Do not change the status of
S6 or revised S8 based on this report.

The source states grouped normal convergence for invariant traces on
root-bounded domains and absolute double-series convergence on a smaller
explicit polydisc. Preserve that distinction during editing.

No concrete mathematical error in the inspected mixed-resonance chapter was
established. The report's false all-power extrapolation is a warning invented
for testing and explicitly is not attributed to the repository.
