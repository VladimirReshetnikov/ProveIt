# ProveIt integration and formalization plan

## Status and placement

Proposed new research directory:
`Combinatorics/Ramsey/Research/GowersSzemeredi/unit-dilation-restriction/`.

This delivery is a mathematical manuscript with executable finite checks.
It includes no Lean file and must not be entered in the formalization ledger
as kernel-verified. The existing `lemma_9_3_holds` should remain unchanged
until any stronger proof has actually been formalized and compiled.

Pinned inspected revision:
`17123532a2de638477dce1c92eb0b0b20a247d2f`.

## Exact statement crosswalk

At tuple length m=2k:

| Manuscript | Existing definition |
|---|---|
| `T_m(B)` | `additiveTupleCount k B` |
| `S_m(B,phi)` | `phiAdditiveTupleCount k B phi` |
| `S_m >= (1-eta) T_m` | `GammaHomOfOrder k B phi (1-eta)` |
| Ordered tuples with repetitions | Functions `Fin (2*k) -> G`; no distinctness premise |

For the current Section 9 interface specialize m=16 and M=N. The manuscript
uses a partial map on B; restrict the existing total map to B, since no
expression queries it outside B. Conversely, extend a partial map arbitrarily
if a total-map representation is chosen in the formal development.

The all-moduli theorem strengthens the tuple-count coefficient from
`(alpha*eta/4)^(2^19)` to at least `2^(-245)*alpha^31*eta^30` and supplies an
explicit natural-number threshold by taking the ceiling of the real bound.
The existing interface does not assume alpha<=1 or beta<=1: these follow in
the nonvacuous case from the tuple cap and subset cardinality. The displayed
threshold is greater than one, so the interface's N=1 possibility does not
require a new edge case. Eta<=1 is already part of the inspected statement.

## Recommended dependency order

1. Prove the finite homomorphism kernel count over `ZMod N` by eliminating
   a coefficient equal to +1 or -1. This is independent of Fourier analysis.
2. Formalize the triangular coefficient probability distribution and the
   exact divisor formula for the weighted gcd. Prove the rational K_m bound.
3. Formalize the normalized Fejer filter, convolution positivity, unit
   reduction, and the Ramanujan formula. The elementary envelope suffices;
   defer Rosser-Schoenfeld and the asymptotic zeta limit.
4. Introduce finite subset-valued random selection. The survival probability
   must use the *distinct support* of a tuple. Formalize the repeated-vertex
   union bound with its exact N^(m-2) count.
5. Prove the weighted good/bad expectation bounds and the linear objective
   extraction lemma. Instantiate the parameterized theorem.
6. Check the dyadic choice and the numerical constants symbolically, then
   deduce the strengthened order-eight statement and the old-interface
   corollary.
7. Only afterward add the defect-profile refinement, labelled extension,
   primorial obstruction, and zeta-ratio limit as independent refinements.

## Important implementation choices

Fourier transforms in the existing Gowers development may use unnormalized
sums. This article averages r and s with probability normalization and uses
probability Haar convolution on the circle. Record the factors N, phi(M),
and L explicitly at each interface rather than relying on implicit
normalization conventions.

There are two distinct objects called phi in ordinary notation: the target
map and Euler's totient. Use different Lean names, such as `targetMap` and
`Nat.totient`, throughout the new implementation. Likewise, avoid reusing
`r` for the labelled base map and the random domain character.

The pair of new integers (N,M) is intentional. A preliminary M=N theorem is
sufficient to imply the current interface, but coupling the random choices
would unnecessarily discard the stronger independent-modulus theorem.

## Downstream limitations

The theorem does not preserve a specified original-domain large spectrum.
It controls one balanced additive relation, not an arbitrary Gowers
arrangement matrix. Extending the weighted gcd argument to weighted Smith
normal form and retaining spectral compatibility are distinct tasks before
propagating any improvement through the higher-order inverse argument.
