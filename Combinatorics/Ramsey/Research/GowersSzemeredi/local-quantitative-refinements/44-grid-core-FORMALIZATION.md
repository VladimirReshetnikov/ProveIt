# Proposed formalization plan

This is a dependency plan, not a report of completed Lean proofs. No Lean
source, placeholder proofs, or claims of a successful Lean build are included.

## Existing interface

At commit `8c12c906e4ab5a00001a65de3c882f935a15661a`, the relevant definitions
are in `Lean/GowersSzemeredi/Sections14_15.lean` under the Ramsey subtree:
`arrangementMoment`, `GeneralArrangement.IsDegenerate`,
`degenerateGeneralArrangementCount`, and `arrangementParityCoefficient`.

The manuscript uses Boolean vertices, not a change to centered coordinates.
Its `k` is the cube dimension, `d` the arrangement multiplicity, `m=2*d`
the number of cross-sections, and `v=m*2^k` the number of labels. Preserve
all squarefree moments and the field-scalar-multiple exclusion.

## Stage 1: width and paired-summary combinatorics

Prove that a proper nonempty subset of a prime field is not invariant under
nonzero translation. Deduce the width-two lemma for ternary-valued affine
Boolean maps when p >= 5. This removes the dimension-dependent cutoff
without lifting long sums to integers.

For a regular cross-section r, prove that the paired linear map L_r has
rank two. Show that the binary offset images identify only the two constant
binary vectors, have cardinality 2^m-1, contain zero, and are closed under
negation. Count injective selections of sign orbits to get the exact
large-characteristic core product. Use finite cardinality identities first;
probability statements are then normalized corollaries.

For p=2,3, characterize the offset kernel as the constant line and count
independent vectors in the quotient. Separately count injective maps from
the cross-section coefficient quotient into F_q.

## Stage 2: minimal Boolean layer and remainder

Formalize Boolean coefficient extraction and inversion without division by
two. Extract a rank-two pair of coordinate-block equations from a minimal
nonzero coefficient vector. Verify explicitly that other terms involve
only coordinates in the chosen minimal set, so two outside blocks give
four independent equations. The resulting non-core q^-3 bound can reuse
finite linear-map fibre cardinalities rather than polynomial geometry.

## Stage 3: rational incidence comparison

Represent a restricted normal by n(a)_i = a_i + a_m*w_i. Relate each minor
of t <= 3 restricted normals to a (t+1)-row integer determinant with entries
in {-1,0,1}. Establish the integer absolute bound 16 and preservation of
nonvanishing in characteristic p > 16. Add p > 2*d to remove extra modular
balance vectors. Only ranks through three are required; no full matroid
stability theorem is necessary.

## Stage 4: fixed-grid theorem

Define finite profile classes modulo translation and nonzero scaling.
Keep their exact representative multiplicities (six for two-valued,
two for three-valued profiles). Formalize the correspondence from a pair
of independent profile classes to a support in {-1,0,1}^2.

Define the local direction count nu(S) using actual affine maps. Prove that
it equals the number of incident hyperplanes in the pair's normal span.
A weighted double count yields both b2 and every flat multiplicity count.
These proofs should not depend on the subsequently computed eight-shape
compression or on a list of numerical d values.

## Stage 5: finite certificate and integer recurrence

Prove the walk recurrence and exact-support inclusion-exclusion identity.
A checker on rational affine maps of at most nine points can verify the
compact coefficient dictionary. The Python program's canonical-key method
is one design, not a required trusted implementation: a Lean checker may
instead verify an explicit list of affine bijections and cancellations.

For d=8, a verified finite evaluation of the recurrence and weighted sums
certifies b2(8). The certificate is much smaller than a direct enumeration
of all hyperplane pairs. The rational normal lists for d=2,3,4 are useful
regression cases, not axioms or substitutes for the general theorem.

## Stage 6: optional analytic and integration work

The deficit asymptotic and growing-k limits are separate from the finite
counting theorem. They need finite Fourier coefficient extraction and
standard analytic limit machinery. They need not block useful finite
formal results.

Only after the refined count is inserted into the complete corrected
selection and inverse chain should the formalization ledger claim a new
end-to-end quantitative consequence. The present package does not perform
that propagation.
