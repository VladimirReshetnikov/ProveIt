# Formalization plan and proof-status boundaries

No Lean source or successful Lean build is included. The declarations below are design targets, not names of existing compiled theorems.

## Separate the model from the existing cyclic interface

Use a finite-dimensional vector space over `ZMod 2`, genuine multilinear maps in all tensor slots, and a symmetry predicate. Do not reuse the repository's multiaffine `IsMultilinear` predicate unchanged. Its constant terms and lower-support monomials belong to a different interface.

Use normalized finite averages, complex-valued functions with norm at most one, and an additive circle group for nonclassical primitives. Keep track of the equality between selected energy and the `2^d`-th power of the Gowers norm. Treat the function as possibly zero throughout; no proof step may divide by its values.

## Algebraic layer

Recommended definitions:

```text
SymmetricBooleanTensor V d
IntegrableTensor T
repetitionDefect T
contraction T z
contractionIntegrabilityRadical T
completeDefectRadical T
minimalObstructionModelDimension T
```

Prove that the repetition defect is alternating in its pair and symmetric multilinear in its frozen variables. Its zero criterion should be proved by support-indexed basis coefficients and an explicit primitive, with finite coordinate differences modulo a power of two. The coefficient-space dimension theorem should include the bilinear base case.

Prove ordinary contraction and diagonal lowering preserve integrability. For diagonal lowering, first prove linearity in the repeated slot by cancellation of the two cross terms. Then use the repetition relation for symmetry, and support coefficients for integrability. This lemma is needed in the model theorem and must not be replaced by symmetry alone.

## Spectral layer

Prove normalized selected-square/cube equality and exact symmetric slicing. Prove gauge invariance independently. The cubic base case requires a finite-dimensional projective orthogonality estimate: alternating rank `2r` forces invariant subspaces of dimension at least `2^r`, giving an operator-norm bound from the trace. The Lagrangian construction can be reduced to elementary alternating-form elimination.

Prove derivative translation/conjugation and even-period identities as product equalities. They remain true with repeated vertices and zero amplitudes. Use these for the constrained pure-power estimate, not an unrestricted optimization of each slice.

## Canonical branch and main induction

Define the canonical tensor `C_d(u,v)` explicitly as the sum placing v in one slot. Establish its defect formula, nonintegrability, and constant-function lower bound. Prove its upper bound by the four `(u(z),v(z))` slice classes, retaining the pure-power derivative constraint on the `(0,1)` class.

The contraction-integrability radical is a kernel, hence has exact relative cardinality `2^(-rho)`. Codimension one forces a pure frozen defect. The Bianchi identity then forces its alternating value to be `u wedge v`, so the tensor is canonical modulo an integrable tensor.

The new universal induction has two cases:

```text
rho = 1: canonical theorem and gauge invariance
rho >= 2: exact slicing + lower-degree universal bound
```

Its final arithmetic is

```text
1 - d*(1-2^(-rho))/2^(d-1)
  <= 1 - 3*d/2^(d+1)
   = (1-(d+1)/2^d) - (d-2)/2^(d+1)
   < 1-(d+1)/2^d.
```

This strict inequality proves the equality classification. The flag count then follows by recovering u from the kernel and v modulo the span of u. The cubic case has planes, not flags.

## Minimal models and normal form

The complete radical kills the defect in every argument. Prove both directions of the minimal-quotient statement:

- Any quotient representation modulo an integrable tensor has kernel contained in the complete radical.
- A linear section of the quotient by the complete radical produces a tensor with the same defect; the difference is integrable.

For an actual frozen radical R and complement H, define `Psi(a)` by putting a in one alternating slot and all other arguments in H. Show its target is `I_(d-2)(H)` by expressing it as the sum of an ordinary contraction and a diagonal lowering of the integrable tensor `T_a`. Its kernel is the complete radical. Rank–nullity gives the exact dimension expression and the bound.

For a prescribed subspace R_0 contained in the radical, prove the direct-sum normal form by restriction to H and Psi. Injection is a four-case expansion of defect arguments into H and R_0. Surjection uses a right inverse of diagonal lowering on the support basis and tensors with exactly one R_0 slot.

The sharpness construction uses one radical basis vector for each nonempty support of size at most d−2. Singleton supports detect every nonzero H component. The Psi map is the full support-basis isomorphism, so the complete radical is zero.

## Certificate checking

The delivered Python matrices can guide executable implementations but should not be trusted as axioms. Recompute their entries from the tensor coefficients, verify row-reduction witnesses, and verify the quotient defect equality on basis tuples. The generated JSON is a regression record, not proof evidence accepted by the kernel.

In particular, do not infer optimizer descent from tensor descent. The package proves no general identity `M(q^*T) = M(T)` outside the canonical family.

## Proposed dependency order

1. Finite Boolean coefficient tables and normalized averages.
2. Repetition criterion, explicit primitive, integrable-space dimension.
3. Defect compatibility, both radicals, and diagonal lowering.
4. Minimal quotient, normal form, and sharp model construction.
5. Cube, gauge, projective cubic base, and derivative periods.
6. Rank-one classification and canonical energy recurrence.
7. All-degree induction, flags, strict gap, and noisy-selector corollaries.

The algebraic steps 1–4 can be completed independently of the analytic steps 5–7. None of these proposed declarations should be recorded as proved until the corresponding implementation actually builds without admitted results.
