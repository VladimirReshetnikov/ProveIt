# Formalization plan: all-degree Boolean obstruction theorem

## Status

This file proposes interfaces and dependencies. It is not Lean source, a
compilation transcript, or a list of already proved Mathlib declarations.
No Lean files are supplied in this package. The finite Python checks do not
constitute proof-assistant verification.

The existing `Sections17_18.lean` catalogue uses proposition-valued definitions
for its Section 17/18 statements. A new theorem must be proved, not obtained by
assuming that a catalogue entry is inhabited.

## Ambient types

Use a finite-dimensional vector space `V` over `ZMod 2`, with a compatible
finite-type instance. Characters should be actual linear maps `V ->ₗ[ZMod 2]
ZMod 2`; their complex realization is the sign character. Use normalized finite
averages explicitly rather than mixing cardinality factors with the repository's
unnormalized prime-cyclic Fourier definitions.

Represent a symmetric degree-`d` tensor as a multilinear map on `Fin d` together
with a proof of invariance under every slot permutation. Do not reuse
`IsMultilinear` from the existing `Definitions.lean` without reconciling its
multiaffine convention.

An integrable tensor has a circle-valued primitive of additive degree at most
`d`, with its constant top derivative equal to the sign lift of the tensor.
It may be easier to prove the coordinate primitive theorem first and then
package the abstract circle-valued statement.

## Proposed module order

### 1. Finite cube calculus

Suggested theorem names (proposals, not existing declarations):

- `selectedEnergy_eq_twistedCubeAverage`
- `selectedEnergy_eq_average_contraction`
- `selectedEnergy_phaseTwist`
- `iteratedDerivative_translate_direction`
- `iteratedDerivative_evenSpan_period`
- `fourier_eq_zero_of_nontrivial_period`

Prove the product formula with labelled vertices. This directly handles
coincident vertices and zeros and avoids all divisions by a function value.
Choose one inner-product/conjugation convention and prove the exact conversion
to the repository's difference convention separately.

### 2. Boolean integrability

- `repeatedDefect_alternating`
- `repeatedDefect_symmetric_multilinear`
- `integrable_iff_repeatedDefect_eq_zero`
- `integrable_iff_basisCoefficient_depends_on_support`
- `supportPrimitive_topDerivative`
- `pureTensor_integrable`

The support-coefficient characterization is valuable for executable
certificates. The proof can first be made for coordinates `Fin n -> ZMod 2` and
then transported through a basis. The primitive takes values modulo one with
explicit powers-of-two denominators; no factorial inverse is used.

### 3. Cubic spectral base

- `projectiveTranslation_unitary`
- `projectiveTranslation_commutator`
- `invariantSubspace_dimension_ge_symplecticDegree`
- `projectiveCorrelation_le_rankBound`
- `cubicEnergy_eq_average_shearedCorrelation`
- `cubicMaximum_eq_alternatingRankPower`

This is the heaviest analytic ingredient. Finite complex matrix spectral theory
or a finite-dimensional Hilbert-space development can supply the positive
operator trace argument. Make the inner product linear/antilinear argument
convention explicit. A common invariant subspace is automatically invariant
under inverses because projective translations have finite-order scalar inverses.

The equality proof uses a symplectic coordinate decomposition and explicit
constant-function energies, not a conjectured product rule for arbitrary
optimizing functions.

### 4. Canonical family

- `canonicalTensor_defect`
- `canonicalTensor_constantEnergy`
- `pureTensor_fixedDerivative_energy_le`
- `canonicalTensor_contraction`
- `canonicalTensor_energy_le`
- `canonicalTensor_maximum`

The fixed-derivative theorem needs `u(z)=0`; omission of this hypothesis is
false because the pure tensor has unrestricted maximum one. Prove the
canonical theorem independently by degree induction before using it in the
universal induction.

### 5. Defect radical and recognition

- `defect_bianchiIdentity`
- `oneForm_compatibleAlternating_eq_wedge`
- `defectRadical_submodule`
- `defectRadical_codim_one_iff_canonical_mod_integrable`
- `contraction_integrable_iff_mem_defectRadical`
- `integrableContraction_fraction`

The key new interface is the penultimate statement:

    d >= 4 -> (T_z is integrable in degree d-1 <-> z belongs to K_T).

The radical lives in the first *frozen* slot of the repeated defect. For degree
four the target is just alternating bilinear forms, with no remaining frozen
slots. The cubic case must not be forced into this definition by a truncated
natural subtraction.

### 6. Universal theorem and rigidity

- `energy_le_integrableContraction_fraction`
- `noncanonicalEnergy_le_radicalSensitiveCap`
- `nonintegrableSymmetric_energy_le_sharpThreshold`
- `nonintegrableSymmetric_maximum_iff_canonical`
- `nearEndpoint_tensorRigidity`

Once the preceding modules are available, this layer is a short induction.
On the radical use the bound one; off the radical use the preceding-degree
universal bound. At radical codimension one use the independently proved
canonical theorem instead. The final arithmetic inequality has gap
`(d-2)/2^(d+1) > 0` for `d >= 4`.

Formalizing the inequality first may avoid requiring compactness or a bundled
maximum. The endpoint equivalence can then be stated using existence of a
function attaining `b_d`, with explicit phase extremizers for the converse.

### 7. Certificates and consequences

- `defectMatrix_kernel`
- `rankOneDefect_reconstruction_correct`
- `canonical_integrableRestriction_iff_dependent`
- `canonical_maximalRepairHyperplanes`
- `canonicalClass_parameters_unique`
- `extremalClass_cardinality`
- `canonical_nearMaximum_amplitude`
- `selectedEnergy_selectorCorruption_le`
- `selectedEnergy_functionPerturbation_le`

For executable reconstruction, certify row reductions and the residual's
support-constant coefficient table. A verifier can be much smaller than the
search procedure. Prove correctness for arbitrary certificate output rather
than trusting a rank function as an oracle.

## Integration cautions

The current proof is on full uniform Boolean vector spaces. It does not furnish
a prime-cyclic, progression-localized, Bohr-weighted, low-energy, or arbitrary
mixed-function replacement for Gowers's Proposition 17.2. Any bridge to those
interfaces needs separate mathematical statements with explicit loss terms.

Keep all new declarations in a distinct namespace and add proved results to
status ledgers only after a real build. Do not insert `axiom`, `sorry`, or a
proposition-valued `def` and describe that as formalizing the theorem.
