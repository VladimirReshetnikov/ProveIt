# Formalization plan and actual proof status

No new theorem in this package has been compiled in Lean. The files under `sources/upstream/` are selected existing source files, not a complete project. This plan describes mathematical interfaces to formalize, rather than introducing axioms or `sorry` declarations and calling them proofs.

## 1. Binary principal-nullity theorem

Work over `ZMod 2` with finite-dimensional vector spaces and a nondegenerate alternating bilinear form.

1. Prove the finite symplectic extension lemma for a possibly degenerate subspace: split its radical, complete a symplectic basis of the nondegenerate part, attach hyperbolic partners to the radical, and extend the isometry.
2. Count independent ordered frames with a fixed alternating Gram matrix. The induction has at least `2^(N-i) - 2^i` choices at step i. This is the main counting lemma.
3. Bound the Gaussian-binomial subspace count by `4 * 2^(s*(d-s))`; keep rational arithmetic for constants 1/4 and 2/3 until the probability corollary.
4. Use uniform measure on the finite symplectic group, orbit/stabilizer, and a union bound to prove the incidence inequality of the report.
5. For the identity-form binary isometry group, prove all elements fix the all-ones vector c via `B(x,x)=B(x,c)`.
6. Odd dimension: identify its action on `c^perp` with the full symplectic group. Even dimension: prove the radical is `span c` and construct a section of the induced map on `c^perp/span c` by fixing `span(c,e_1)`.
7. Express a principal kernel as `E_J ∩ Q^{-1}(E_{J^c})`, perform the parity-dependent projection argument, and union over finite subsets J.

No analytic limit theorem is needed for the finite tail inequality. Real asymptotic notation is only used for its corollaries.

## 2. Lubin–Tate precision and carries

The local polynomial core can be formalized before formal groups:

1. Define `F_0=X` and `F_(a+1)=pi*F_a+F_a^q` over a discrete valuation ring.
2. Prove the leading-face coefficient inequalities by induction. Separate the unique equality coefficient from all strict inequalities.
3. Define finite Laurent polynomials modulo `pi^r`; their nilpotent geometric inverses are finite sums, so coefficient reasoning is algebraic.
4. Prove the maximum pole bound and identify the extreme coefficient as `(-1)^(r-1)*pi^(r-1)*choose(m+r-2,r-1)`.
5. Relate nonzero reduction to a p-adic unit, and prove the carry criterion using the factorial-valuation/digit-sum identity.
6. For contact depths at most one, derive the exact finite maximum and the optional eventual-period corollary.

Then add the formal-group interface:

- Endomorphism difference `[b]-[c]` is `[b-c]` times a power-series unit.
- A unit endomorphism applied to `[pi^a]` preserves that association.
- Invertible integral coordinate changes preserve Laurent order.
- Monic distinguished division and Lagrange interpolation over `(O/pi^r)((X))` give the recovery theorem. Nilpotents require proving only that the lowest Laurent coefficient is nonzero; it need not be invertible.

The exact cutoff over a nonreduced coefficient ring is a separate lemma and should not be silently imported from a field-only interpolation theorem.

## 3. Orthogonal half-block laws over odd finite fields

1. Define the split form with matrix `[[0,I],[I,0]]`; use the full determinant-one subgroup, not the derived subgroup.
2. Prove `det(g)=(-1)^(rank C)` by reducing a maximal isotropic image to standard position.
3. Count rank-r images by a Gaussian binomial times `q^(r*(r-1)/2)` using graphs of skew-symmetric matrices.
4. Prove uniformity conditional on rank from left/right Levi actions.
5. Compute the rank likelihood ratios and identify their deficit strata. This gives total variation of the entire matrix distribution.

## Existing source mechanisms to reuse carefully

`PositiveType.lean` supplies the finite-group/Fourier singular-compression language, while `OneCurve.lean` supplies finite-jet extremality techniques. The new proofs are specialized extensions; neither should be represented as a one-line application of the source's final GRH theorem.
