# Proof audit

This is an internal logical audit accompanying an unrefereed manuscript. It is
not an independent referee report or a formal verification.

## Central dependency chain

1. Boolean integration is equivalent to vanishing repeated-variable defect.
2. The cubic projective-translation estimate supplies the degree-three base.
3. Exact even-direction periods give the constrained pure-tensor cap.
4. The constrained cap and cubic base prove the canonical maximum separately
   in every degree.
5. Radical codimension one is equivalent to being canonical modulo integration.
6. A direction belongs to the defect radical exactly when its contraction is
   integrable.
7. Exact energy slicing, with the preceding-degree universal cap on every
   nonintegrable slice, closes the induction in all degrees.
8. The strict gap excludes all noncanonical endpoint tensors; the subsequent
   counting, repair, recovery, and rigidity results follow from this classification.

The canonical theorem is proved before the universal induction. It does not
assume the universal bound in the same or a higher degree. There is no circular
induction.

## Critical points checked

### Normalization

The derivative Fourier coefficient uses a normalized average over its base
point, and the outside direction average is normalized. Expanding the square
introduces exactly one new direction and one base point. The total normalization
is `|V|^(d+1)`, matching the `2^d`th power of the normalized `U^d` norm after phase
removal.

### Complex conjugation and zeros

The derivative is `f(x+h) conjugate(f(x))`. All cube and shear identities are
identities of products. None divide by `f`, so zeros and amplitudes below one
are allowed. The self-projective cube expression may first appear conjugated;
it is real because it equals an average of squared absolute values. This
justifies removing that conjugation without assuming `f` is real-valued.

### Symmetry

Full symmetry is assumed, including the final frequency slot. It ensures the
correct energy slicing, bilinearity/alternation of the repeated defect, and
radical behavior in every frozen slot. The theorem is not advertised for a
selector symmetric only in its sampled direction slots.

### Rank distinctions

For `d >= 4`, `r(T)` is the codimension of the first frozen-slot radical, or
rank of the map `z -> Phi_T(z,...)`. It is not the rank of one alternating
bilinear slice, the dimension of the span of the defect's values, analytic
rank, or partition rank. The cubic case uses alternating rank and is handled
separately.

### Integrable-slice equivalence

For `d >= 4`, the defect of `T_z` is `Phi_T(z,...)`; the integration criterion
therefore gives equality of the slice set with `K_T`, not merely an inclusion.
The cubic-slice endpoint `d=4` is included, with no remaining frozen variables.
The set is a linear kernel, so its exact uniform measure is `2^(-r)`.

### Independent-slice relaxation

Exact slicing retains the derivative `partial_z f`. Applying a universal cap to
that function is legitimate because it remains one-bounded. Independent slice
optimization is only an upper-bound relaxation; no simultaneous realization of
slice optimizers is asserted. For the canonical branch, where this relaxation
is too weak, the proof instead preserves a fixed-derivative period constraint.

### Closing arithmetic

For `r >= 2` the loss is at least

    (3/4) d/2^(d-1) = (d+1)/2^d + (d-2)/2^(d+1).

The excess is strictly positive for every induction degree `d >= 4`. It is this
strictness, not compactness alone, that classifies endpoint tensors.

### Sharpness and unused coordinates

The explicit constant function on `C_d` gives the lower bound. Gauge twisting
supplies an extremizer for `C_d + S`. Upper bounds hold for arbitrary functions
on the full vector space, so unused tensor coordinates do not create an
unjustified tensor-product argument.

### Endpoint versus phase classification

The main theorem classifies tensors with maximum `b_d`. It does not classify all
functions attaining that value. The amplitude result only forces modulus one
at equality and bounds average amplitude loss near equality; no uniqueness or
phase-stability estimate is inferred.

### Repair geometry

A canonical tensor integrates on `H` exactly when the two coordinate forms
become dependent there. Thus there are three maximal integrable hyperplanes,
not a unique one. The distinguished defect radical `ker u` is only one of them.

### Counting

The higher-degree class parameters are `u != 0` and a nonzero coset of `v` modulo
`span(u)`. Cubics instead correspond to rank-two alternating forms and hence
two-dimensional dual subspaces. The counts concern tensors admitting an
extremizer, not only tensors optimized by the constant function.

### Robust bounds

Selector corruption changes a squared coefficient in `[0,1]` only on the
corrupted tuples. Function perturbation telescopes over the `2^d` labelled
vertices, which are individually uniform even when they coincide. The theorem
assumes a supplied symmetric tensor model and does not infer it from observations.

## Executed finite checks

`data/verification.json` records the exact cases. The verifier uses independent
support-coefficient integration and matrix-defect routines, exact contraction
counts, explicit canonical recovery, exact constant energies, Gaussian-rational
function tests, direct labelled cubes, and integer modular primitives.
Both ordinary and optimized Python execution are required to give the same JSON.

These computations cannot prove the continuum optimization or all-dimensional
theorems. They are regression checks of the finite algebra and conventions. The
proof of the complex spectral inequality is mathematical, not an invocation of
a numerical eigenvalue routine.

## Remaining uncertainty and open work

The manuscript is unrefereed and its literature priority is not established.
The noncanonical caps and rigidity-window width are not claimed optimal.
Maximizer phase classification, general higher-degree inactive-coordinate
stability, direct-sum multiplicativity, odd characteristic, local measures,
and the multiaffine/global inverse interfaces remain further research tasks.
