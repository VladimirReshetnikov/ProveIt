# Review of the faithful U15 parabolic obstruction

**PASS.** I read the complete author proof and helper and checked the
primary finite-type and peripheral presentation in Keen's Sections3–4,
using the cached PDF identified by the author hash. The result concerns
the fixed physical word `W=(ab)^3b^2` under faithful integral two-by-two
group representations; it is not a theorem against other computational
input formats or certificates with integer witnesses.

In the free basis c=ab,b, the relation W=c^3b^2 has a nonabelian S3
quotient. This excludes primitivity, because quotienting by the normal
closure of a primitive element leaves a cyclic group. The primitive
nonzero homology vector (3,5) separately excludes proper powers and
commutator powers. The same argument covers each individual published
ordinary-symbol block with odd c-exponent at least three.

Faithful projectivization is justified: a lift of projective torsion
would have a positive power equal to I or -I, contradicting freeness.
Integrality supplies discreteness. Keen's finite-type theorem and
standard peripheral generators reduce a rank-two orientable quotient
with a cusp to a three-holed sphere or a one-holed torus. Their cusp
generators are respectively primitive or commutators. Taking powers
cannot evade the two homology exclusions. Discreteness and
torsion-freeness also exclude elliptic images, leaving hyperbolicity.

I separately checked the GL2 extension. A torsion-free discrete action
has no fixed-point reflection, so its finite-type quotient is a surface.
The rank-two nonorientable cores with an end have either one crosscap
and two boundaries, or two crosscaps and one boundary. The first has
primitive peripherals; the latter's boundary has homology in2Z^2.
Neither admits W as a cusp power. For a negative-determinant integral
matrix, trace(M^2)=trace(M)^2+2; zero trace would give M^2=I, while
nonzero trace makes the square hyperbolic. This covers powers of
orientation-reversing images as well.

The helper correctly checks the finite word, permutation and matrix
ingredients. It does not purport to prove the geometric theorem by
sampling matrices. The explicit nonfaithful parabolic example usefully
demonstrates the necessity of the injection hypothesis. Restriction of
a faithful full-alphabet representation to the tape subgroup preserves
that hypothesis. Fixed invertible contexts cannot make the exponential
trace of a hyperbolic power polynomial in the ordinary input.

Fresh installed normal and optimized exact-receipt replays from `/` pass.
No predecessor code or archived compiler was run. This source and proof
cross-read adds no new matrix array or universal arithmetic bound.

| Frozen author file | SHA-256 |
| --- | --- |
| `u15_faithful_parabolic_obstruction.py` | `b48c08429428035e6f6cd974f5ccc72f74e70d82a368adce2ff0023a3df21cd0` |
| `u15_faithful_parabolic_obstruction.json` | `8c2bec88bd146f2a2567eb0bd91bd5315ae2a6ffa1d1eeabdbae8181b3667b08` |
| `u15_faithful_parabolic_obstruction.md` | `4ae00a2f43e7bda8163f7fa525605848a25647e9d7b68e393d94b0a0d4068e65` |
