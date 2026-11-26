# Formalization plan

This is a specification for future work, not a completed Lean proof. The report's new
results have human proofs and exact Python checks. The upstream source excerpts are
not a transitive dependency closure and are not presented as a standalone build.

## 1. Density separation

Define the natural-density suprema alpha and beta independently, quantifying only over
sets whose natural density exists. Define rational triples by `a * c = b^2` with
`a < b < c`, and integer triples by `(a, a*r, a*r^2)` for integers `r >= 2`.

The finite certificate checker needs only integer arithmetic and finite sets:

1. Reconstruct the 507 smooth integers through 10^6 and the 102-element replacement.
2. Check integer-ratio avoidance and enumerate rational triples.
3. Verify leaf dual capacity inequalities in `density_exchange_certificate.json`.
4. Verify the three children of each branch cover all possibilities for the selected triple.
5. Deduce the integer maximum-weight threshold by induction on the proof tree.

The analytic bridge then needs convergent geometric sums, harmonic partial summation,
finite CRT density, and a uniform bound on the tail of square divisibility. Construct
sets from finite smooth supports before taking suprema; do not postulate density of
an infinite optimizer. All numerical inequalities can be proved from the integer bounds
in `density_results.json`, together with the sieve's prime-correctness theorem.

## 2. Graph-tower extremum

First formalize the finite-field core for `p > 2*m`:

- powers of distinct projective binary linear forms are linearly independent when their
  number is at most the degree plus one and the degree is less than p;
- a consecutive sequence of vanishing power sums of distinct nonzero scalars forces
  the multiplicity vector to be zero;
- the first nonzero even moment polynomial occurs by floor(m/2);
- a homogeneous binary polynomial of degree d has at most d projective zeros;
- the root-of-unity construction attains the maximum for even m and `2*m | p-1`.

Then prove the spectral interface. The Cayley multigraph keeps all parallel edges.
Connectedness follows from spanning modulo p. Diagonalize the Laplacian by characters,
compute the first unit coefficient in a truncated exponential coordinate, and use the
matrix-tree theorem. Constant and linear terms vanish integrally, including the boundary
case where the first unit coefficient has degree p-1.

## 3. Wild-radical torsion specialization

Parameterize the field by an odd prime p and unit u, with pi^p = p*u. Normalize v(p)=1.
Prove the compositum's degree and total ramification, then its relative different and
the index of the cyclotomic power-basis order. Avoid an unsupported inference that a
compositum of totally ramified fields must be totally ramified.

The central abstract lemma should accept a triangular monic basis whose evaluations
have distinct valuations modulo the base value group. It yields optimal values at each
degree and an integral basis after scaling. The index identifies the exact gain delta.

Next reduce an arbitrary polynomial packet to roots with the matching shell valuation
via the Gauss valuation. Sum positive parts separately; replacing this by an ordinary
sum would allow illicit cancellation. Match lower and upper bounds using the best monic
approximant. Costs add across finitely many shells because the corresponding root
multisets are disjoint. A finite truncation argument handles integral formal series.

Preserve strict endpoints: loss must exceed epsilon to block a shell, whereas a cost
strictly below the obstruction guarantees a point with loss at most epsilon.

## 4. Upstream source interfaces

The source already supplies a full divisible Selmer bound and a finite-level stopping
lemma. A future arithmetic application must verify its residual-image condition, scalar
inertia, finite conjugate-dual defects, local-rank budget, and exact local conditions.
Small normalized length is not vanishing when the coefficient field is enlarged.

The abstract twisted-lattice determinant theorem allows a twist for each prime, joined
by a common height comparison. Its index matrix must work for every allowed twist at
that prime. These quantifiers should be retained when extracting a reusable interface.
