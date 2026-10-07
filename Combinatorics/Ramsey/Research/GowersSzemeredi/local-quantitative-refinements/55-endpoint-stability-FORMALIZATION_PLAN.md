# Formalization plan

This is a design document. It contains no purportedly compiled Lean declarations.
The aim is to formalize the local theorem independently of the full Gowers inverse
and integration machinery, then add the qualitative entry theorem as a separate,
clearly identified interface.

## Conventions that must be fixed first

Use a finite nonempty additive commutative group `G`, normalized counting averages,
complex-valued functions, and conjugation indexed by the parity of a Boolean cube
vertex. Keep `d >= 2` explicit. Define the cubical power directly; taking a real
`2^d`-th root is unnecessary for most local arguments.

Represent polynomial phases by functions `P : G -> Complex` with modulus one and
an exact multiplicative cube identity. Do not replace these with coordinate
polynomials over a finite field. In particular, keep small-characteristic and
nonclassical phases inside the definition.

The basic local statement should be about an already supplied phase, not a minimum
over the entire phase set. Compactness and minimizers are needed only for the
later global theorem and rigidity statement.

## Layer 1: finite cube maps

Prove coordinate-reflection invariance of uniform cube sampling. Then prove that
any three distinct cube coordinates give a surjective map to `G^3`, using an
explicit minor of determinant `1` or `-1`. A direct bijection of sampling variables
may be easier than general integer-matrix machinery.

For four vertices, classify by xor and integer pair sums. In the exceptional case,
reduce to `(x, x+u+v, x+u+w, x+v+w)`. Count ordinary parallelograms through the six
coordinatewise solutions of `a+b=c+d`, and xor-zero four-sets through ordered
triples. These counts are natural independent formalization targets.

## Layer 2: analytic finite averages

Prove the four-factor Cauchy–Schwarz bound and the five-/six-factor inequalities.
The crucial five-factor inequality uses the six triples `{1,j,k}`, `2 <= j < k <= 5`,
with equal Hölder exponents. A generic finite product Hölder lemma can package the
incidence-count argument.

Establish the exact demodulated identities:

```text
m = average F >= 0
r = F - m
a = 1 - average |F|^2
D = average |F-1|^2
z = D + a = 2(1-m)
v = average |r|^2 = D - z^2/4
2*m*Re(r) = v + a - (1-|F|^2) - |r|^2
```

The real-part identity plus a telescoping product lemma proves the fifth-order
cancellation. Expand the finite cube product by subsets. The cardinality-one,
-two, and -three terms vanish by independence; bound the rest explicitly.

## Layer 3: finite Fourier analysis

Needed facts: inversion, Parseval, character orthogonality, and the effect of
complex conjugation. The quartic circuit calculation then gives `C_d E4 + J_d T4`.

Partition the nonzero dual characters into fixed points and two-element orbits
under negation. Derive the coefficient pairing inequality from the nonnegative
function `(1-|F|^2)+|F-1|^2`. Prove the scalar algebra

```text
x^4+y^4 <= (x^2+y^2)^2/2 + z^2*(x^2+y^2)
```

under `|x-y| <= z`, then sum over the negation orbits. Do not assume that the group
has odd order until the order-two Fourier mass has been exposed.

## Layer 4: local polynomial inequalities

The remaining proof consists of the master bound, a second-order upper Taylor
bound for `(1-z/2)^q`, and explicit scalar inequalities. It is preferable to prove
the pre-absorption inequality first; it displays the positive amplitude term and
makes the role of the radius auditable.

Use a namespace and names such as:

- `cube_three_coordinates_uniform`
- `cube_four_coordinate_type`
- `cube_quartic_torsion_bound`
- `bounded_fifth_real_part_bound`
- `bounded_cube_centered_expansion`
- `phase_endpoint_master_bound`
- `phase_endpoint_local_certificate`
- `phase_endpoint_local_inverse`

These are proposed names, not claims that such declarations currently exist.

## Layer 5: global statement and sharpness

Keep the Eisner–Tao qualitative entry theorem separate. One possible interface is:
for every local radius there is a uniform cubical-defect threshold yielding a
phase with correlation above the required value. Its eventual proof must not be
replaced by an undocumented axiom.

Formalize the phase-class gap by induction on phase degree. Then prove the exact
order-two character family and the signed-cube second/fourth moment identity.
Analytic Taylor estimates for bounded one-parameter families yield the matching
asymptotics. A filter-based formulation of the stability modulus should come only
after the finite estimates are complete.

The tangent theorem needs quantitative versions of elementary concentration facts
for nonnegative finite weights. A practical route is to prove finite deficit
inequalities before expressing convergence along varying groups.

## Integration safeguards

A theorem of the local shape does not discharge an existing catalogue entry whose
hypothesis merely gives a fixed positive uniformity norm. Ensure the assumptions
include the explicit candidate phase and the correlation radius. Research placement
and theorem-style English prose are not substitutes for successful elaboration and
kernel checking. This package deliberately reports no formalized theorem count.
