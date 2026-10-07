# Formalization plan (no checked Lean implementation supplied)

Proposed namespace/label stem: `SharpSymmetry` / `ssc:`.
Repository snapshot: `6c2e2172bab8a0af4aed6b62d53ae7cde9252e8d`.

This plan is a list of proof obligations. It neither assumes specific current
Mathlib API names nor claims that declarations have been implemented.

## Data and conventions

Use an odd prime p and a finite-dimensional F_p-vector space V, with the
normalized finite probability measure. Model V* as the linear dual. A selector
is a k-multilinear map with values in V*. Its associated scalar form has k+1
slots. Track the empty (k-1)-tuple explicitly when k = 1.

The multiplicative derivative is `f(x+h) * conj(f(x))`, not a quotient. The
normalized Fourier coefficient at xi is the average of `f(x) * e_p(-xi(x))`.
A backward cube from the existing project differs by a translation, so its
Fourier coefficient is multiplied by a unit scalar. Prove this transport
before identifying source-level statements.

## Milestone A: elementary algebra and polarization

1. Prove a nonzero linear map has zero fibre of relative size at most 1/p.
2. Curry a vector-valued multilinear map into a space of linear maps. Induct
   to obtain nonzero support probability at least (1-1/p)^m.
3. Treat affine maps separately; their zero fibre can be empty.
4. Prove that swaps of the last slot with each previous slot generate all
   permutations. Extract a nonzero alternating slice map from nonsymmetry.
5. Expand the diagonal polynomial by finite subsets and ordered slot choices.
   Terms missing an increment cancel; exactly d! terms survive. Require d < p.
6. Derive the affine-in-x formula for the (d-1)-fold derivative.
7. Establish the pointwise Fourier-shift identity for f multiplied by a phase.

Milestones 5–7 alone yield the equality-form scalar companion to the corrected
Proposition 17.2. They do not require the main analytic rank inequality.

## Milestone B: finite operator inequality

1. Define B, Omega = B - transpose(B), and half of its even rank.
2. Construct a symplectic basis of a complement to the radical by induction.
3. Define W_h on L2(V) by translation and modulation, and
   U_h = e_p(-B(h,h)/2) W_h. Prove unitarity and the exact cocycle.
4. In a nonzero invariant subspace, simultaneously diagonalize the commuting
   Z_i. Applying all products of X_i gives p^r orthogonal eigenvectors.
5. Define the positive operator M_g as the average of rank-one projectors
   onto U_h g. Prove invariance under every U_h by reindexing a finite sum.
6. Prove trace(M_g) = ||g||_2^2. Each positive eigenspace has dimension at
   least p^r, so the largest eigenvalue is at most p^(-r)||g||_2^2.
7. Identify the quadratic form of M_g with Q_B(g,v).

This route avoids formalizing the full irreducible representation
classification just to prove the inequality.

## Milestone C: symmetry threshold and robustness

1. Freeze k-1 derivatives and identify each remaining energy with Q_B(g,g).
2. Apply the bilinear estimate and average to get the amplitude-sensitive profile.
3. For a nonsymmetric form, combine the support estimate and rank >= 2 of
   every nonzero alternating slice to obtain the sharp threshold.
4. Build the endpoint from two independent dual functionals a,c and f = 1.
5. Prove the disagreement-density estimate by bounding each summand in [0,1].
6. Add dense-domain and weighted-coset wrappers, preserving the global-selector
   and common-selector assumptions respectively.
7. For a multiaffine slice, encode the affine offset using
   v(x) = e_p(xi(x)) g(x); invoke the mixed bilinear inequality.

## Milestone D: equality and stability

Decompose by the radical's characters. Construct a Weyl representation on each
block from simultaneous eigenspaces. Prove the trace calculation giving block
dimension p^(2r), and the Hilbert–Schmidt orthogonality of the Weyl matrices.
Then prove the exact block purity formula and use eigenvalue inequalities plus
singular value decomposition. A nearby unit extremizer need not be 1-bounded;
this must remain explicit in the theorem type.

## Milestone E: extension fields

Model the character using the trace pairing. Show that the radical of the
trace-composed alternating form is the original radical and that restriction
of scalars multiplies its rank by e. The support bound uses q, while factorial
invertibility uses the characteristic p. In particular `q > k+1` is not an
adequate hypothesis for classical polarization.

## Required integration cautions

- Preserve normalized/unnormalized factors: |V|^(k+2).
- Do not weaken `energy > threshold` to `>=`.
- Do not confuse symmetry of derivative slots with full symmetry.
- Do not apply homogeneous lossless extraction to a multiaffine selector
  without accounting for its lower-order terms.
- Do not turn local-box selector information into global multilinearity without
  an extension theorem.
- Do not mark source Proposition 17.7 or a final density-increment result proved
  merely because its global scalar precursor has an equality-form companion.
- Do not modify existing checked theorem counts until actual proof terms have
  been built and audited with the repository's own toolchain.
