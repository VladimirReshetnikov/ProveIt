# Proposed formalization interface

This document is a plan, not a report of completed Lean verification. It contains no placeholder theorem asserted as a trusted result. The proofs to be formalized are supplied in `boolean_phase_integration.tex`.

## 1. Source interface and scope

The formal-project comparison uses commit `797aa3cfe967349322b806692a500f677f7047cf`. The relevant files are `Sections17_18.lean` and `Definitions.lean` under `Combinatorics/Ramsey/Lean/GowersSzemeredi/`.

The existing `proposition_17_2` is a global phase-removal statement over a cyclic prime field with factorial-invertibility assumptions. The new article develops a related finite-abelian/Boolean model. Its tensors are multiadditive and homogeneous. The repository predicate `IsMultilinear` permits lower-order monomials and a constant term. A formal connection must preserve this distinction and must not silently replace one predicate by the other.

Nonclassical phases take values in the additive circle R/Z. Replacing this value group by F_2 would incorrectly discard the very primitives needed in characteristic two. Use an additive-circle representation with an explicit embedding of F_2 as the two-torsion subgroup, or an equivalent rigorously specified finite dyadic value group for each bounded degree.

## 2. Definitions to introduce

Use a separate namespace for these research statements, with names chosen not to collide with the existing development. The identifiers below are suggestions, not assertions that those declarations already exist.

| Suggested identifier | Mathematical object |
|---|---|
| `normalizedAverage` | Uniform average on a finite, nonempty type |
| `multiplicativeDerivative` | `f(x+h) * conj(f(x))`, valid also when f vanishes |
| `selectedDerivativeEnergy` | Article equation (1.2), with explicit normalized Fourier convention |
| `homogeneousTensor` | A multiadditive map with all its slots, including frequency evaluation |
| `constantTopDerivative` | The d-fold additive derivative of a circle-valued phase |
| `alternatingBicharacter` | The commutator pairing associated to a biadditive phase |
| `alternatingRadical` | Kernel of that pairing in its first slot |
| `projectiveTranslation` | The unitary operator in equation (3.4) |
| `booleanRepeatedDefect` | `T(a,a,b,z) + T(a,b,b,z)` |
| `integrableRestriction` | Existence of a nonclassical primitive after restricting all slots |

Keep three distinct notions of rank separate: the matrix rank of an alternating bilinear form, analytic rank defined using bias, and partition rank of a tensor. The mixed transposition theorem controls analytic rank. It does not license a conversion to partition rank without a separate theorem.

## 3. Algebraic first milestones

### Finite differences and normalizations

Prove the exact cube expansion, the selected-Fourier-square identity, commutation of multiplicative differences, and gauge invariance. These identities must allow zero and nonunit amplitudes. A useful regression test is the pointwise identity

```text
partial_a partial_(a+w) f = conjugate(partial_a (f * translate_w f))
```

on a Boolean group. Avoid division by f in this proof. The package includes exact Gaussian-rational tests that deliberately contain zeros.

### Alternating decomposition

For a finite abelian group with an alternating bicharacter, prove that the nondegenerate quotient has square order and has a self-annihilating subgroup. The article gives an induction that splits off paired cyclic factors. Over a finite field this specializes to symplectic elimination and even alternating rank. Over composite moduli, formalize the radical-index formula independently of any field-rank shortcut.

### Boolean primitive construction

Prove `Delta_a^2 = -2 Delta_a` for additive differences on an exponent-two group. For a symmetric tensor, use this to establish the necessary repeated-variable transfer identity. For sufficiency, prove the explicit coordinate formula in Theorem 5.2, including its denominator and the vanishing of its next derivative. This recovers known nonclassical integration with all characteristic-two details visible.

This is a good finite-algebra milestone before introducing the spectral proof. The current exact checker verifies the entire formula on F_2^2 in degrees two through five but is not a general formal proof.

## 4. Finite-dimensional analytic milestone

Work in the finite-dimensional complex Hilbert space with normalized inner product. Prove that projective translations are unitary and satisfy the article's multiplication and commutation laws, including signs.

For the positive twirl operator M_g, prove:

1. Its trace is the squared L2 norm of g.
2. It commutes with every projective translation.
3. Every nonzero common invariant subspace has dimension at least the square root of the alternating-radical index.
4. Therefore each positive eigenspace of M_g has at least that dimension, giving its operator-norm bound.
5. The mixed matrix-coefficient average is the quadratic form of M_g, giving Theorem 3.2.

The equality proof additionally requires simultaneous diagonalization of the commuting translations from a self-annihilating subgroup. It constructs a modulus-one eigenfunction on each coset and checks orthogonality outside the subgroup. Formalizing only the upper bound would not yet formalize the theorem's sharpness assertion.

## 5. Spectral certification and cubic repair

The next dependency chain is:

```text
mixed orthogonality
  -> self-cube identity
  -> alternating-slice energy profile
  -> support probability for a nonzero multiadditive map
  -> sharp symmetry threshold

Boolean shear + mixed orthogonality
  -> repeated-variable rank profile
  -> nonclassical integration certificate
  -> exact phase-removal identity

cubic repeated defect
  -> alternating normal form modulo integrable tensors
  -> canonical block energy
  -> exact maximum 2^(-rank/2)
  -> minimum integrable-restriction codimension rank/2
```

The upper-bound proof and the extremizer construction should be separate lemmas. Likewise, existence of an isotropic subspace of codimension half-rank and the lower bound on every such codimension should be separate: the radical has twice the needed codimension and does not prove optimal repair.

The amplitude-sensitive cubic estimate has scale eight. Formalizing its L2-mass corollary requires the nonnegative, bounded function `|f|^2`, not a claim valid for arbitrary unbounded f. The near-extremal amplitude conclusion does not imply phase stability.

## 6. Mixed correlations

Derive the triangle estimate directly from mixed orthogonality and one Cauchy-Schwarz inequality. Verify the F_2^2 equality example to formalize the optimal fourth power. The seven-function repair argument then uses a shear and a maximal isotropic subspace.

The improvement to Tidor's displayed codimension bound does not require changing the seven-function hypotheses. However, the proof does not establish optimality of the coefficient two. A formal statement should not include such an assertion.

## 7. Quartic certificate and continuous maximum

There are two independent formal targets.

First, prove the coefficient identity (9.8), either by the human cube census in the manuscript or by a verified finite enumeration. `data/verification.json` includes all 29 monomial coefficients, while the checker independently accumulates all 1,024 cube terms and compares coefficients. Importing that JSON as unverified data would not constitute a formal proof. A small checker should reconstruct the cube signs and exponents from the mathematical definitions.

Second, prove the maximum over the full complex unit polydisc, not just roots of unity. The manuscript first moves the maximum to the distinguished boundary by separate subharmonicity; the remaining calculation is an elementary real inequality in three cosine variables. One may formalize the analytic maximum principle, or replace that step by a direct algebraic disc bound if a cleaner proof is found. The phase-grid census cannot replace this obligation.

The all-dimensional quartic reduction uses the image dimension of the linear repeated-defect map and the displayed Bianchi identity. Preserve the distinction between a tensor depending on two coordinates and an optimizing function depending on all coordinates. The manuscript leaves the resulting stabilization problem unresolved.

## 8. Integration and completion criteria

A useful first completed module would contain the finite-difference algebra and explicit Boolean primitive, with no spectral imports. The second would contain the finite-Hilbert-space estimate and its equality construction. Subsequent modules can follow the dependency chain above.

Before exporting a theorem to the existing Gowers development, explicitly discharge the ambient-group, homogeneity/multiaffinity, phase-value-group, and normalization interfaces. Localizing a translation-invariant twirl to a Bohr set or progression introduces a further boundary problem not addressed here.

No Lean build has been run for the new results because no Lean implementation is delivered. A completed formalization should have no `sorry`, no research-result axioms, a recorded toolchain and dependency revision, and a successful build before any repository ledger is updated.
