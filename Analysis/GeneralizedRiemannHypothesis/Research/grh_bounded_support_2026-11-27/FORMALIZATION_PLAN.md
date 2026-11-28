# Lean formalization roadmap (not implemented or checked)

The new step can be isolated from the complex analysis and from the upstream Dirichlet GRH proof.

## 1. Finite combinatorial core

Define `levelWidth j = h0 * 2^(j-1)` for positive natural levels, finite lists of tagged occurrences (so repeated frequencies remain separate), and integer bin indices. For a parent bin, residual count after its own level is `Nat.sub (sum childResiduals) capacity`; capacity is `D * levelWidth j` if eligible, else zero. Base removal is a nonnegative pointwise operation on leaf counts.

Prove these lemmas with natural arithmetic and finite sums:

- A level-j bin is a disjoint union of level-i bins for i <= j.
- Residual count is monotone in original leaf counts.
- Given a bin lower bound of D*j*h_j and saturation in earlier sub-bins, the current eligible bin allocates exactly D*h_j.
- If both children have original count <= D*j*h_(j-1), and each has earlier saturated allocation D*(j-2)*h_(j-1), their residual sum after level j-1 is <= D*h_j.

These are sufficient for the saturation and coverage inductions. State them abstractly with a natural cutoff predicate rather than real logarithms at first. This part needs no probability theory or GRH.

## 2. Analytic count interface

Introduce the half-open interval count inequalities (paper equations (7)–(8), named `eq:upbin`, `eq:lowbin` in TeX) as hypotheses. Establish the real-valued threshold lemmas for `h_j`, `R_j`, `T_j` using `Real.log`, `Real.exp`, powers and inequalities. Convert interval counts to natural inequalities. For actual L-functions, prove or import the Riemann–von Mangoldt estimate and handle the conjugation-closed aggregate. This can be an interface theorem until the explicit zero-count library is available.

## 3. Positive interpolation and convolution

- Use a finite real matrix indexed by a finite symmetric set, column-sum norm, and a Neumann-series inverse (or a finite linear-algebra argument from strict diagonal dominance). Prove the norm bound and reflection invariance.
- Construct convolution of two uniform probability measures. Its characteristic function is the product of sinc functions. The density multiplier `1 + sum c_lambda exp(-i*lambda*t)` has real value >= 2/3. Normalize.
- Define `vanishesToOrder F lambda n` using complex iterated derivatives; prove order adds under product. Use existing convolution/characteristic-function lemmas where available.
- Bound Laplace transforms of symmetric compactly supported measures by `cosh(r*A)` and then by `exp(r^2*A^2/2)`; use a finite product and summability for the level proxy.

## 4. Remaining analysis

The slit-plane Jensen argument and positive Volterra stopband factor are preexisting mathematical ingredients of the article. Formalize independently or connect to verified versions, if available. For the corrected ramp theorem import the appropriate explicit formula; the correction identity and averaging of absolutely convergent Fourier series can be verified separately from the contour argument. Use the actual vendored statement `DirichletLZerosOnLine` from the pinned upstream interface only when the analytic application needs the critical-line assertion.

No claim is made that these definitions or lemmas already exist with the proposed names in Mathlib. This is a dependency breakdown, not Lean source pretending to compile.
