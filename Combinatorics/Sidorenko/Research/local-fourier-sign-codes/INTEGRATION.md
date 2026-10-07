# Integration and formalization plan

## Suggested location

`Combinatorics/Sidorenko/Research/LocalFourierSignCodes/`

This is a proposed new directory. Adapt it to the maintainer's taxonomy;
no remote write or existing-path assumption was made. The paper also fits
as a cross-reference from the Ramsey/Gowers–Szemerédi research program.
Do not append it to a moving numbered companion series without checking
that series first.

## Source-independent mathematical dependency chain

The proofs do not import the Sidorenko counterexample theorem, a rank-layer
asymptotic, a quantitative Szemerédi theorem, or a proposition-valued Lean
catalogue. The necessary dependencies are finite character orthogonality,
finite products and sums, binary linear algebra, elementary graph theory,
Cauchy–Schwarz, Parseval, and convexity of integer powers on nonnegative reals.

A proposed formalization order is:

1. Define a finite bipartite graph with explicit disjoint parts and a finite
   abelian character group. Define normalized expectations and Fourier
   coefficients. Establish the real-even coefficient identities.
2. Define zero-sum tuples, inversion-invariant sign bits, frustration length,
   and the binary relation code. Prove tuple/integer-relation equivalence.
3. Prove local safety implies positive edge-product signs, and construct
   the three-edge-path theta witness for the reverse direction.
4. Prove the shortest-negative-word partial sums are distinct. Derive the
   group-size cutoff; prove the Boolean rank cutoff by minimal dependence.
   The BFS algorithm can be verified separately against this specification.
5. Prove the graph Fourier expansion directly by vertex orthogonality.
   Do not infer arbitrary finite-group surjectivity from rational matrix rank.
6. Define positive and negative finite masses. Prove the identity
   `negative_mass = (absolute_mass - signed_mass) / 2` and factor the
   one-sided relaxed sum into moments. This is the key factor-of-two check.
7. Inject pairs `(simple cycle, nonzero frequency)` into conserved labelings
   with that exact support. Treat inverse frequencies and order-two
   frequencies explicitly to avoid double counting.
8. Derive the robust inventory and inverse defect inequalities. Then use
   Parseval and centered indicators to prove the set-cut factor `1/4`.
9. Verify the two-point sharpness family, its even-subgraph expansion,
   and the leading girth coefficient. Keep forests separate from cyclic graphs.
10. Encode the 22 faces using distinct tagged point and face vertex types.
    Verify the 33 pair incidences of multiplicity two, the 22 point-graph
    triangles, connectedness, c4=33, and c6=88. Derive the main 35/66 theorem.
11. Formalize the typed certificate using finite probability weights and an
    affine system over F2. It is sufficient certifiability, not an equivalence
    with the total-density inequality.
12. Kernel-check the 8192-term point-spin enumeration and its polynomial,
    or produce a separately checkable arithmetic certificate.

## Normalization compatibility with ProveIt

The inspected `Lean/GowersSzemeredi/Definitions.lean` uses an unnormalized
`ZMod.dft`. The manuscript uses coefficients `lambda = (1/N) * dft`;
a possible reversal of frequency convention is immaterial for real even w.
Prove this compatibility rather than silently coercing the two conventions.

For the normalized U2 norm, the raw two-dimensional cube sum has N^3 terms.
Its fourth root is N^(3/4) times the normalized U2 norm. The manuscript's
`33 p^62 ||w-p||_U2^4` uses the normalized quantity.

Do not confuse the normalized convolution eigenvalue lambda with the
unnormalized weighted adjacency eigenvalue N*lambda. Do not substitute the
±1-test-function cut norm for the set-cut convention without adjusting constants.

## Trusted boundaries

No Lean files or kernel build are supplied. Mathematical proof statements
should not be introduced as new axioms or accepted through `sorry` and then
reported as verified. The current executable certificate is ordinary Python
using exact arithmetic; the interpreter and handwritten translation remain
outside any Lean kernel trust boundary.

The source repository's finite graph is imported as explicit finite data,
not through the validity of its counterexample proof. Its actual typed
matrix kernel is not automatically covered by the scalar theorems, nor has
its compliance with the typed sign-gauge hypotheses been established here.

## Regression data

`faces.json` labels point vertices 0..12 and face vertices by their positions
0..21. A graph representation must tag these two parts or offset face labels
by 13. The checker uses the latter convention. The equal numerical labels
from distinct parts must never be identified.

The polynomial variable is z=(t/p)^2. Its degree is 22, not 33, since each
of the 22 degree-three face vertices permits only zero or two selected edges
in an even-degree subgraph. The coefficient sum is nevertheless 2^32,
matching the incidence graph's cycle-space dimension.
