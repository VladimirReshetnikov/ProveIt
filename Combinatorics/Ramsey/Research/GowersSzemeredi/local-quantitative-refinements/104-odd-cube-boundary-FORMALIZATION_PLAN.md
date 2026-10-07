# Formalization plan — no Lean certificate supplied

## Definitions and reusable primitives

Work with finite subsets of an additive commutative group. Define C_k by star
coordinates or affine Boolean-cube maps, prove equivalence, and include all
degenerate cubes. Separate unnormalized counts from real-valued deficits, so
empty sets need not enter divisions. Prove the correlation recursion and the
maximal-energy coset characterization.

## First-failure injection

Fix a total order on nonbasic subsets refining cardinality. For each bad star
assignment choose its first failing subset and deterministic distinct indices.
Construct the map to a bad ternary triple and k-2 coordinates. Prove injectivity
on each selected subset by an explicit coefficient-one inverse. This should use
only additive group algebra and finite cardinalities.

## Occupancy identity

Encode the eight Boolean rows (1,omega) over the integers. Check the six orbit
representatives and the determinant census as finite statements; prove every
five-set has a unimodular subset using opposite faces. For odd-order H, prove
multiplication by two is bijective, then count prescribed vertex values.
Formalize the binomial identity for the fourth-order occupancy correction and
identify N8 with C3(R). Do not replace this step with an unexplained axiom.

## Boundary induction

Formalize fibers in G/H, z_t, c_t, P, and J. Keep separate lemmas for
c_t+2z_t <= 2s and the two-torsion-dependent c_t <= s. Prove the secant inequality
by a finite geometric sum. Prove decreasing alpha_k and the joint remainder before
deducing the simpler boundary inequality and energy consequence. Prove the
one-fiber identity via the projected cube's unique changing coordinate.

## Rounding and local profiles

Reuse checked repository lemmas only after matching every hypothesis and
normalization. Otherwise formalize the appendix: translation-defect
subadditivity, the 3/2 difference-set lemma, Markov extraction, the exact energy
complement identity, the root bound, and unique nearby cosets.

Use ring normalization for the mixed cubic and four-dimensional hole identities.
Prove all interval inequalities with exact rational constants. Keep H odd and
(G/H)[2] = {0} as distinct assumptions. Derive the quantitative inverse theorems
only after constructing the relevant subgroup inclusions.

## Verification status gate

Choose the repository's actual Lean/mathlib versions, compile all declarations,
and audit the axiom dependency closure. Only then may an integration record call
the resulting declarations formally verified. The present package contains no
unchecked `.lean` stubs and changes no formal-status ledger.
