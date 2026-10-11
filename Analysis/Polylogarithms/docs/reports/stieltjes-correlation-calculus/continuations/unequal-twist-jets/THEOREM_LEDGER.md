# Theorem status and dependency ledger

All “proved” entries below mean an ordinary mathematical proof in `article.tex`.
They do not mean independent peer review or proof-assistant verification.

| Result | Article label | Proof mechanism and scope |
|---|---|---|
| Entire central mixed-twist expansion | `thm:central` | Binomial expansion, Cauchy coefficient bound, smooth Fourier pairing; all complex orders |
| Arbitrary nonintegral real twists | `cor:alltwists` | Exact finite exceptional-mode head, common-phase tail |
| Every mixed order jet | `thm:jets` | Holomorphic differentiation, finite Leibniz rule, harmonic/Stirling coefficients |
| Symmetric first Stieltjes generators | `cor:symmetric` | Explicit logarithm product and canonical Gamma contact normalization |
| Eventual sequence uniqueness | `lem:sequence` | Convergent Laurent–log expansion at infinity |
| Finite functional closure classification | `thm:classification` | Mixed monodromy, then a pole obstruction for one logarithmic site |
| Ordinary log-Gamma convolutions | `thm:gammaconv` | Square-summable first primitives; absolutely summable product coefficients |
| Multishift Lerch/zeta continuation | `thm:multizeta` | Normally convergent central expansion; explicit possible polar hyperplanes |
| Every ordinary primitive | `eq:ordinaryprimitives` | Appending denominator shifts 1 through p; disk identity |
| Sharp-cutoff constants at every index | `thm:cutoff` | Absolutely convergent diagonal subtraction and Pochhammer jets at zero |
| Lower-degree recursion and collision | `thm:Crec` | Convergent parameter derivative, rational divided difference |
| Gamma antiderivative | `eq:C01primitive` | Integration by parts of the digamma divided difference |
| Every transverse ray jet | `thm:rays` | Explicit exceptional k=1 pole cancellation; remaining normal series |
| Rational polylog/Stieltjes coordinates | `eq:rootjets`, `eq:Stieltjesfilter` | Classical root filter with the zeta pole kept before expansion |

## What is not settled

The finite functional theorem does not decide isolated arithmetic values,
numerical period independence, finite bases with arbitrary argument-dependent
coefficients, arbitrary complex-order bases, or all spatial translations.
The Gaussian S6/S8 conjectures remain unresolved here. A convergence theorem
is not a claim that its infinite expansion terminates arithmetically.

The multishift zeta origin generally has direction-dependent ray values. The
article computes transverse ray jets, not a universal joint value or a
canonical multivariable finite-part prescription.

## Evidence separation

824 finite exact assertions, including three deliberate corruption controls,
and 96 floating-point comparisons at each of two working precisions accompany
the proofs. The numerical results are diagnostics, not interval certificates.
`SHA256SUMS` is an artifact-integrity record, not a theorem certificate.
