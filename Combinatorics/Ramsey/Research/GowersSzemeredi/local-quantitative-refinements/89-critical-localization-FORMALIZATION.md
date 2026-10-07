# Proposed formalization plan

This file is a plan, not a completed Lean development. No theorem stubs, `sorry`
proofs, research-result axioms, or unverified certificate imports are supplied.
The written mathematical proofs are in `critical_phase_removal.tex`.

## Ambient interfaces

Use a new namespace for this finite-vector-space development. Start with a
finite-dimensional vector space over `ZMod p`, an explicit prime hypothesis,
and finite probability averages. The target of a nonclassical polynomial is
the additive circle, together with a specified embedding of `ZMod p` into its
p-torsion subgroup. Do not replace a nonclassical phase by an `F_p`-valued
polynomial without separately proving the vanishing of the full Frobenius
contraction.

The tensor is symmetric and homogeneous in *all* slots, including the final
frequency-evaluation slot. This is stronger than symmetry just in the selector
variables. The repository's `IsMultilinear` predicate allows lower-order terms;
use a different predicate or prove a separate homogenization interface.

Let `d` be the tensor degree. The selector has `d-1` variables; the phase has
degree at most `d`. The normalized cube energy has `d+1` independent averages.
An unnormalized implementation multiplies it by `|V|^(d+1)`, not by `|V|^d`.
Local energies have their own scale `|H|^(d+1)`.

## Stage 1: difference algebra and exact symbols

Prove the commuting additive-difference identities, the cube formula with
conjugation parity `d-|omega|`, and the top-symbol lemma. Preserve the explicit
p-torsion embedding; multiplying a circle-valued top derivative by p gives zero
and is not how its field-valued symbol is extracted.

The multiplicative formulas must allow zero-valued f and must not divide by f.
Establish the Fourier-square identity and exact gauge invariance separately.
A successful first module should expose these normalization identities before
any primitive construction is attempted.

## Stage 2: constructive integration through degree p+1

Prove the operator identity `(1+Delta_x)^p=1`, invert its nilpotent factor over
the additive group of bounded-degree polynomials, and deduce that multiplying
by p lowers degree by p-1. The Frobenius/top-quadratic identity then establishes
necessity of the repeated-variable condition.

For sufficiency, formalize the integer representatives and carry functions,
the degree estimates for the low-depth lifts, and the critical primitive
construction. The Boolean diagonal lift has denominator 8, not 4. For odd p,
the quadratic lift has denominator p^2, and its cross coefficients differ by
a factor of two from its diagonal coefficients.

The primitive algorithm must subtract the *complete* symbol of the initial
lift before adding the residual classical polynomial. Formalize the residual
monomial coefficients with individual factorials less than p; do not divide
by the nonunit factorial `(p+1)!`.

## Stage 3: the defect, normal form and optimal repair

Show that `T(x repeated p times,y)` is bilinear by symmetry and characteristic
p. Its antisymmetrization is alternating even when p=2. Formalize the canonical
block and its defect, then symplectic elimination including a possibly nonzero
radical.

Keep the following distinct:

- minimum restriction codimension: half the defect rank;
- radical codimension: the full defect rank;
- minimum number of linear coordinates supporting an integrability correction:
  the full defect rank.

The last quantity is not asserted to be partition rank. Its lower bound follows
from inclusion of the tensor radical in the alternating radical. Prove the
maximum repair dimension and characterize all maximizers, rather than only
constructing the smaller radical restriction.

## Stage 4: face integration and lossless localization

This is the central analytic interface. Work with a direct-sum decomposition
`V = H + K` and an explicit face-integration hypothesis. Choose primitives of
all face tensors for each fixed tuple of quotient increments. Prove the finite
inclusion-exclusion identity for the vertex phases `Q_J`.

The crucial invariant is `degree(Q_J - P_H) <= d-1` for every vertex. Then
Gowers--Cauchy--Schwarz on H bounds the conditional mixed cube by a product of
local U^d norms. Average the quotient cube without selecting a coset first.
This proves the stronger intermediate inequality involving the U^d norm of the
nonnegative quotient function a.

Prove independence of the local energy from the chosen primitive, representative,
and linear complement. The quotient object should ultimately be indexed by
cosets, not by an arbitrary implementation of K.

## Stage 5: moment, sharpness and quantiles

Prove `U^d <= L^(2^d/(d+1))` by the supplied Young-induction argument. Check
normalized convolution, the derivative recursion, and all exponent conversions.
The final Jensen inequality is in the direction that gives an arithmetic-mean
upper bound on the fractional-moment expression.

Formalize the single-coset extremizer with all `d+1` independent quotient
variables constrained. Its exact probability is the index to power `-(d+1)`.
Use the fractional local-energy moment, not the mean local energy alone, to
prove the quantile estimate. Maintain strict/non-strict event conventions.

The mixed theorem follows from a second Gowers--Cauchy--Schwarz application on
the quotient and the same cube-to-moment inequality.

## Stage 6: higher degrees and explicit external dependency

Introduce the pencil of alternating forms obtained by fixing the remaining
`d-p-1` arguments in the repeated-variable defect. Strong isotropy requires
vanishing on H in the first two slots while all remaining slots range over V.
This is stronger than integrability of the restriction of T to H alone.

The general integration criterion used here is Tidor's Proposition 3.5 together
with the necessary condition. To export an unconditional all-degree theorem,
formalize that criterion. Otherwise state the face-integration theorem and the
conditional criterion interface without claiming the import is already proved.

The two dimension constructions for a common isotropic subspace are independent:
greedy extension using at most m*k linear equations, and sequential symplectic
restriction with adapted half-rank loss. Taking the better result does not mean
that one single unmodified construction attains both bounds automatically.

## Stage 7: counts, algorithms, and certificates

Prove the exact diagonal-query acceptance law from the radical size and a
nonzero linear functional's uniform distribution. It is not an energy bound.
Formalize the isotropic-space counts and uniform alternating-rank distribution
as optional finite-combinatorics modules.

The JSON verification report must not be imported as trusted mathematical data.
A verified finite checker would reconstruct the primitive tables, difference
operators, RREF subspaces, and ternary tensor census from their definitions.
The Python script is a reproducible regression suite, not that verified checker.

## Completion criteria

Record the Lean and Mathlib revisions, run an actual build with no `sorry` or
unjustified axioms, and inspect theorem dependencies before updating any status
ledger. No such build was performed for this delivery. An initial useful result
is the general face-integration localization theorem plus the independently
proved critical-degree integration module; later counting modules need not
block that milestone.
