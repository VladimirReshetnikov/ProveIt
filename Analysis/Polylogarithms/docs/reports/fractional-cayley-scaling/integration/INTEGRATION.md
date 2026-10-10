# Proposed ProveIt integration

## Source baseline

Commit `28357e8ca63dd78327db91d9be239d75e4462879`.

The canonical manuscript and relevant reports were inspected before selecting the new directions. `source_snapshot.json` records file hashes and pinned URLs. The historical S4 conjectural status is superseded by the canonical exact proof; the earlier S8 candidate is already refuted. No external repository files were modified during preparation.

## Placement map

| New source | Existing destination | Integration guidance |
|---|---|---|
| `sections/fractional_kernels.tex` | Signed-kernel and affine-moment chapters, currently `05-signed-kernels.tex` and `05-affine-signed-moments.tex` | Retain the earlier integer-order evaluator. Add the sharp real-order measure classification, atomic edges, extended complex/angular theorem, boundary scales, and valid Euler constants. Reconcile with the incoming `angular-zero-continuation` real-order theorem rather than duplicating it. |
| `sections/local_radius.tex` | Incoming angular continuation and signed-kernel chapter | Mark the quadratic-coefficient sign problem proved. Keep the full-radius integer-order conjecture open. |
| `sections/fractional_nonmonotonicity.tex` | Same angular section | Add the proved fractional maximum and minimum theorems and both exact certificates. It refutes a blanket fractional global-monotonicity extension, not the original integer-range conjecture. The separately sampled rational pair is diagnostic. |
| `sections/bessel_zeros.tex` | `09-zero-geometry.tex`, following existing fixed-index/spectral regimes | Add the adjacent-index Bessel regime and arbitrary-order small-rho theorem. Preserve fixed `r` and fixed Bessel zero label; the Bessel result is local. The small-rho global count has a pair-dependent, unspecified parameter interval. |
| `sections/gamma_transition.tex` | `07-reflected-moments.tex`, following the fixed-reflected-exponent theory | Add the joint critical scale and explicit correction. The fixed-m sharp remainder remains valid as stated and should not be relabeled as erroneous. |
| `sections/cayley_quotients.tex` | `04-S4-proof.tex` and/or `04-cyclotomic-quotients.tex` | Add raw-rank versus shuffle-ideal distinctions, Hilbert characters and asymptotics, and the explicit S-family identity. This does not prove the frozen S6 depth-two reduction. |
| `sections/research_agenda.tex` | `10-discovery.tex` | Update resolved local items and add the precise remaining questions. Preserve the actual mathematical status of S4, S6, S8 and formal dimensions. |

The standalone introduction, notation, verification section and bibliography are designed for this report. When moving individual sections into the book, reconcile definitions once, replace the standalone citation keys, and adapt section level as needed. No new section labels collide with the inspected canonical chapter labels; historical report labels should be checked separately if several whole reports are merged together.

## Proposed status/correction annotations

### C1. Stale S4 status in historical reports

**Observed:** the attribution paragraph of the incoming Lerch report describes S4 as a conjecture it does not resolve. The statement describes that report's contribution but is stale as current project status.

**Suggested annotation:** “The canonical manuscript now proves S4 using convergent Cayley symmetry and exact double-shuffle certificates. This historical report does not supply that proof. The mixed S6 depth-two reduction remains conjectural.”

Retain historical delivery files if they are used as provenance; annotate the integration record rather than rewriting their history.

### C2. The critical atom must be retained in any extension

The reciprocal-Gamma term in the fractional kernel converges to an endpoint atom at `a+b=1`; it cannot be set to zero as an ordinary density term. Add the atom of mass `1/(1-b)`. At `a=0,b>1`, the atom has mass `zeta(b)`.

This is a required correction to a naive extension, not an error in the older `a>=1` theorem.

### C3. Boundary convergence and open arcs

At the atomic edges, use analytic continuation or Abel values. Ordinary boundary Fourier terms do not tend to zero. Angular zero uniqueness is for `0<theta<pi`, with real endpoints excluded from the count.

### C4. Keep fixed-parameter qualifications

The reflected-moment asymptotic is valid with fixed reflected exponent. The new joint transition proves why an unrestricted extension fails. Likewise, the fixed-index Stieltjes asymptotic cannot be inserted into `n~k` without the new uniform argument.

### C5. Raw rows, ideals and evaluated periods are different objects

The weight-seven imaginary ranks are 12,207 for raw Cayley rows and 16,996 for all shuffle consequences. The formal quotient has 7,518 imaginary coordinates. None of these numbers is a numerical period-dimension claim. Do not add the separate Cayley and double-shuffle ranks without subtracting the actual intersection.

### C6. Fractional normalized motion is not globally classified by K

The finite certificates prove a local radial maximum immediately below the threshold for `b=1/2` and a local radial minimum immediately above it for `b=999/1000`. Thus the sign `K>0` does not force increasing motion on the whole disk. This is a correction to a proposed extrapolation, not a refutation of the original conjecture for integer `a>=2` or the stated `a=1` trichotomy.

## Verification artifacts

- `code/verify_local_radius.py`: exact polynomial and rational inequality checks.
- `code/kernels/certify_fractional_turning.py`: exact integer/Fraction interval proof of the fractional turning signs and scaling constant.
- `code/kernels/certify_fractional_minimum.py`: the complementary positive-quartic certificate; it imports the preceding interval primitives.
- `code/verify_gamma_transition.py`: exact moment and correction identities; optional independent-coordinate quadrature.
- `code/zeros/verify_zeros.py`: exact logarithm intervals and 48 sign decisions; optional Bessel/Lerch diagnostics.
- `code/zeros/bessel_coefficients.py`: exact all-order profile/zero coefficient generator.
- `code/cayley/check_cayley_ranks.py`: independently generated rational matrices, all raw/lifted rows through weight four.
- `code/cayley/verify_harmonic_cayley.py`: exact S-family word identities; regenerates the 96-term S6 JSON.

All other numeric scripts are explicitly diagnostic. The incomplete weight-seven mixed-relation search generated no certificate and no separating functional. Its matrices are not dependencies of this package and should not be described as an obstruction.

## Editorial acceptance priorities

1. Check the new analytic proofs, especially uniformity and endpoint qualifications.
2. Replay the finite exact certificate suite from the proposed report directory.
3. Reconcile theorem numbering, notation and bibliography against the manuscript.
4. Update conjecture statuses only where a complete theorem now applies.
5. Retain the scientific figure sources and data with their diagnostic captions.

The article is a serious research draft with ordinary proofs and finite exact certificates. It does not claim external peer review, proof-assistant verification, or exhaustive historical priority.
