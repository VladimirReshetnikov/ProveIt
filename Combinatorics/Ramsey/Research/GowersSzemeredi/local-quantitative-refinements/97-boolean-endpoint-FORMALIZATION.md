# Proposed formalization plan

These are proposed interfaces and dependency stages, not claims about existing
Lean APIs or completed proofs. No Lean source with axioms, `sorry`, or a changed
status ledger is included as verification evidence.

## 1. Finite Boolean calculus

Use a finite-dimensional vector space over F_2, normalized finite expectations,
complex-valued functions, and circle-valued additive phases. State explicitly
that tensors are genuinely multilinear and fully symmetric, including the
frequency-evaluation slot.

Prove the selected-square / cube identity, slicing, integrable gauge identity,
Boolean derivative conjugation periods, and the pure-tensor constrained cap.
The repeated-vertex case and zeros of the tested function must remain included.

## 2. Coefficient normal forms and certificates

Develop Boolean-lattice Mobius inversion for arbitrary circle-valued truth
tables. Prove the degree criterion by coordinate differences and
Delta_e^2 = -2 Delta_e. This yields exact relative gluing in coordinates adapted
to a subspace and the endpoint truth-table certificate.

A root-of-unity checker can operate on integer residues. The search procedure
or Python output should not be trusted: its returned coefficient certificate
must be checked by a separately proved procedure.

## 3. The canonical cap

Prove projective orthogonality in a finite Hilbert space. The canonical cubic
case needs only the two-dimensional multiplicity loss from anticommuting
operators. Combine it with the derivative-constrained pure slice to prove the
all-degree canonical cap and retain the index-four nonnegative slack.

This stage can reuse verified preceding project lemmas if their hypotheses and
normalizations match. It must not reuse a proposition-valued catalogue entry as
though a proof had been supplied.

## 4. Four-point and function classification

Represent a real phase table on F_2^2 by four Walsh coefficients. Prove the
signed-count identity symbolically by partitioning direction tuples according
to their types. The integer polynomial identity in three cosine variables is a
small independent certificate target.

Show strict transverse monotonicity for d >= 4, then combine with exact gluing
to derive the full endpoint family. Formalize compactness as a finite union of
two-dimensional tori using the coefficient criterion. This also gives the
component count and the intersection statement for different distinguished u.

## 5. Relative testing: isolate the imported theorem

Package the Eisner--Tao input as a clearly documented theorem dependency, not as
an unexplained axiom presented as a new proof. Its interface supplies a modulus
uniform in all finite Boolean dimensions.

Prove the support lower bound for nonzero circle-valued polynomials, the
bounded-torsion phase gap, the piecewise degree bound, and the mixed-defect
repair. These finite algebraic steps are logically separate from the imported
qualitative analytic input.

## 6. Local coercivity and sharpness

Formalize the real-part weight, character Parseval computation, and the exact
Hessian spectrum. Prove independence of three distinct Boolean affine-cube
vertices using row independence over F_2.

For the local theorem, use the exact finite subset expansion, the disk
constraint, and nearest-torus orthogonality. Do not assume that small L2 error
has a pointwise-small argument. The local radius and constants need no
qualitative inverse theorem.

Finally combine uniform entry and explicit local coercivity. The sharpness
example needs only four points, finite separation of torus components, and the
standard limit of (1-cos t)/t^2.

## Deliverable boundaries

Suggested proof modules should mirror these six stages. Existing repo
normalizations, conjugation conventions, ambient-group hypotheses, and the
multiaffine/homogeneous distinction must be reconciled before importing any
statement. The paper's Python finite checks are useful test fixtures but are
not a substitute for proofs of the general claims.
