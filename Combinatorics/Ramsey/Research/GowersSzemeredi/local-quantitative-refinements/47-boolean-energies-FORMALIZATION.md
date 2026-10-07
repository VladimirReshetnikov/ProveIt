# Formalization plan

This document describes proposed interfaces. It is not Lean source and does
not claim that the names below already exist in Mathlib or the repository.
No `sorry`, unproved axiom, or proposition-valued definition is supplied as
if it were a checked theorem.

## 1. Basic objects and normalization

Use a finite-dimensional vector space V over F_2 with finite type and
nonempty instances; characters are linear maps V -> F_2 followed by
`(-1)^bit`. Complex-valued functions have normalized counting L2 norms.

Represent the derivative by

    derivative f h x = f (x+h) * conjugate (f x).

Represent tensor degree d with d actual slots. `selectedEnergy` uses d-1
directions and a final evaluation slot. Its unnormalized denominator is
`|V|^(d+1)` after expanding the Fourier square. The function has homogeneity
`2^d`, which must be retained in every scaling lemma.

Do not reuse the repository's `IsMultilinear` predicate without changing
its interface: the inspected predicate includes constant and lower-order
square-free monomials, while this manuscript assumes homogeneous
multilinearity in every slot.

## 2. Low-risk finite product lemmas

Suggested theorem names (all new):

- `iteratedDerivative_cubeProduct`: labelled cube expansion, with conjugation
  parity d - HammingWeight.
- `iteratedDerivative_translate_direction`: translation by a listed direction
  conjugates the product.
- `iteratedDerivative_translate_evenSpan`: translation by an even sum leaves
  the product invariant.
- `fourier_eq_zero_of_period_character_neg`: an exact period on which the
  tested character is -1 forces a Fourier coefficient to vanish.
- `pureTensor_fixedDerivative_energy_le`: Theorem 4.3.

Prove these as identities of products, not by division. Include h=0,
repeated directions, odd linear relations among directions, and zero
function values from the outset.

## 3. Exact energy identities

- `selectedEnergy_eq_cubeAverage`: expand the squared norm and substitute
  one base point as the other plus a new direction.
- `selectedEnergy_eq_average_slices`: for symmetric T, freeze a direction
  and commute its derivative to the function.
- `selectedEnergy_gauge`: multiplication by a top-derivative phase cancels
  an integrable tensor.
- `pureTensor_primitive`: |u(x)| / 2^m modulo one has top derivative U_m/2.

A phase-function interface with values in the unit complex circle can be
used for the gauge lemma even before a full `R/Z` polynomial interface.
The primitive theorem then supplies the phase functions.

## 4. Cubic base and canonical induction

The dependency-heavy background is the bilinear projective orthogonality
inequality. One implementation route is finite-dimensional complex spectral
theory and a Lagrangian decomposition of the alternating form. An alternative
is an explicit normal-form matrix calculation, provided arbitrary radical
coordinates and all multiplicities are retained.

After the shear profile has been proved:

- `canonicalCubic_energy_le_half` is the rank-two case.
- `canonicalTensor_slice` is multilinear expansion.
- `canonicalEnergy_le` is induction on d, using the quarter split by (u(z),v(z)).
- `canonicalEnergy_one` is a finite probability/counting identity.
- `canonicalEnergy_max` combines the upper bound and the constant witness.

The essential induction detail is that the (0,1) quarter uses the constrained
fixed-derivative cap, NOT the unrestricted maximum of the integrable pure
power tensor. The two u(z)=1 quarters can be gauge-twisted because the
induction hypothesis applies to arbitrary bounded functions.

## 5. Algebraic defect module

Suggested definitions:

- `repetitionDefect`: T(a,a,b,zs) + T(a,b,b,zs).
- `IsPureSymmetricMap`: F(zs) = A * product u(z_i), A and u nonzero.
- `firstSlotRadical`: all z whose contraction is zero.

Suggested lemmas:

- `repetitionDefect_alternating`, `repetitionDefect_multilinear`.
- `repetitionDefect_bianchi`.
- `alternatingForm_eq_wedge_of_oneFormCompatibility`.
- `pureDefect_iff_canonical_mod_integrable`.
- `oneDimensionalDefectImage_binaryReduction`.

The last theorem only reduces the tensor modulo an integrable correction;
it is not an energy tensorization theorem.

## 6. Support module, independent of complex analysis

- Nonzero s-linear maps have support at least 2^(-s).
- Two pure symmetric tensors of degree >=2 with distinct factors cannot sum
  to a pure tensor (evaluate on a, b and a mixed tuple).
- A non-pure vector-valued symmetric map admits a non-pure scalar projection.
- A non-pure symmetric map of degree >=3 has a non-pure one-variable contraction.
- Support increases by at least a factor 1/2 when one frozen input is unfrozen.
- The 16-row binary trilinear support table is a finite Boolean calculation.
- Non-pure trilinear support is at least 7/32, using radical codimension >=3
  or the binary quotient census.
- Lift to support 7/2^(s+2) for every non-pure symmetric s-linear map, s>=3.

The finite table can be discharged by exhaustive reduction after a transparent
formula has been proved. Do not replace the dimension-independent radical
argument with a finite example search.

## 7. Assembly and robust variants

Combine the pure-defect classification, support-to-energy inequality, and
canonical formula to prove universal thresholds. Keep strict inequalities
for certification. Include explicit endpoint counterexamples to the version
with a non-strict inequality.

The deficit identity is a finite algebraic subtraction of the quarter-slice
caps. The corruption margin is an average of bounded differences; the
approximate-period bound is a single Cauchy–Schwarz step.

## Acceptance requirements

A future formal contribution should record the Lean and Mathlib versions,
show an actual successful build, contain no unapproved axioms, and keep the
Boolean vector-space interface separate from the cyclic prime statement
files. Until that has been done, none of the results here should be added to
repository counts of kernel-checked theorems.
