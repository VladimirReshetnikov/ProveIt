# Internal mathematical audit

**Manuscript:** *Large Closed Sets Avoiding All Convergent Linear Recurrences*  
**Audit date:** 8 October 2026  
**Scope:** The written mathematical argument, its hypotheses and quantifiers, and the accompanying exact-arithmetic examples.

## Review outcome

No remaining proof gap was identified in the manuscript as reviewed. This records the outcome of an internal mathematical audit; it is not an absolute certification of correctness or priority. The manuscript has not undergone external peer review or proof-assistant verification.

The main assertion concerns one common closed, symmetric, periodic set, with its choice preceding all recurrence parameters, translations, and nonzero dilations. The audit retained that quantifier order throughout. Eventually constant observations are excluded, and rational observations are required to be defined at the limiting vector.

## Material failure modes checked

| Potential failure | Resolution in the manuscript |
|---|---|
| Inactive unstable roots or nilpotent transients in a supplied recurrence | The stabilized span of the tail states carries an invertible operator whose powers tend to zero. Its characteristic polynomial supplies a stable invertible scalar recurrence for the tail. No dominant-root cancellation argument is assumed. |
| Repeated roots, complex roots, and collisions | Quadratic Lyapunov contraction controls the complete state. The explicit root-annulus proposition bounds the resolvent using cofactors and the characteristic determinant; its constants do not involve distances between roots. The contour formula is justified from a larger circle before deformation. |
| A large state coordinate that is not an original scalar term | Consecutive-state companion matrices give the exact identity `(A^n w)_(k+1)=u_(n+k)`. Every selected term and denominator uses this shifted original index. |
| Zero scalar values or near cancellations | First passage is measured by positive block energy. A largest-coordinate choice then gives a nonzero scalar term with a uniform signed envelope. The condition `tau<alpha^d` also makes selected original indices strictly increasing. |
| Negative displacements crossing an old grid boundary | Stability excludes a closed interval on both sides of the center. Centers exactly on a boundary are included in the exceptional set. Circle distances, half-open cells, refinement, and integer wraparound are compatible with the separation proof. |
| Unjustified independence of adaptive routes | The proof exposes only center selector entries first. Relevant activation entries are distinct and unexposed. After conditioning on all selectors, the terminal addresses are pairwise distinct. Averaging gives the exact failure probability; independence of entire routes is neither claimed nor needed. |
| An invalid union bound over uncountably many parameters | Polynomial signs determine all first-passage, coordinate-tie, and local-key choices. The full sign-condition estimate includes zero signs. Representatives depend only on deterministic data and already exposed center information, never on unexposed entries. |
| Degree growth or a circular parameter choice | Polynomial degrees grow linearly with the original prefix length. The exponentially growing grid count uses only the local edge-subtree span. The global endpoint grows affinely with the base window length after branching, height, and gap are fixed. |
| Projecting a discontinuous selected subsequence to define residual centers | The residual uses every continuous original quotient through `TB+d-1`. Compact projection proves closedness. Open-neighborhood repair may increase the final witnessing prefix, which is explicitly acknowledged. |
| A quotient denominator that changes sign or vanishes | The normalized auxiliary state has energy at most `1/4`, so `1+e_n` lies between `1/2` and `3/2`. Clearing this denominator preserves signs. A zero auxiliary state covers eventually constant denominators. |
| Loss of a fixed family when taking later tails | The matrices and metrics stay fixed; numerator states are normalized to energy one, while denominator perturbations eventually have energy at most `1/4`. One compact family covers all sufficiently late tails of each qualifying quotient. |
| Incorrect density scaling or incomplete dilation coverage | Dyadic contractions preserve unit-interval density because their periods divide one. Both signs are included in the summable budget. Arbitrarily large original dilations are handled by choosing a sufficiently late tail before contraction. The total omitted-density budget is at most `epsilon/2`. |
| An unsupported computability conclusion | Compactness supplies finite rational-arc certificates with positive margins. Their finite assertions are decidable by real quantifier elimination. The explicit summable tail bound gives computable measure for the effectively closed compact section. This does not decide zero modes of arbitrary computable-real input recurrences. |

The finite-pattern obstruction and the fixed-ratio perturbation obstruction were also checked. In particular, every positive-measure set contains an affine copy of some sequence `q^n(1+o(1))` for each fixed `0<q<1`. Thus the theorem cannot be extended to all such perturbations without restrictions on the whole family.

## Exact computation and its limits

The recorded run of `verify_recurrence.py` passes **3,380 exact assertions**, using `fractions.Fraction`. The three examples include complex roots, infinitely many exact zero terms, phase cancellation, and repeated complex roots. Checks cover the quadratic inequalities, independent scalar formulas, original-coordinate identities, shared numerator/denominator bounds, first passage with **16 exact threshold equalities**, coordinate ties, increasing selected indices, signed separation, and denominator clearing at boundary equality.

The examples satisfy the manuscript's complete sampling conditions, including `tau<min(c/2,alpha^d,1/8)`. Their auxiliary denominator is `(1/4)(-1/2)^n`, with a realization satisfying the same contraction bounds.

These finite checks validate representative algebra and implementation details. They do **not** establish the assertion for every real parameter. That assertion rests on the manuscript's deductive argument, including the external classical full sign-condition bound, finite probability, compactness, and the summable construction.

The package does not implement the full ordered routing tree or the quantifier-elimination search for universal blockers. The latter is proved to terminate in principle; no practical runtime or useful numerical blocker is claimed. The internal audit and executable checks are likewise separate from formal verification and from a literature determination of absolute novelty.
