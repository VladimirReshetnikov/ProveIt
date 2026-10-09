# Claims, hypotheses and evidence

This document states what the continuation establishes, what its evidence
checks, and which obligations remain for unknot recognition. The detailed
arguments appear in [article/article.pdf](article/article.pdf) and its TeX
sections.

## Implemented mathematical results

| Result | Precise scope | Argument/source |
|---|---|---|
| Compressed least representatives | A complete maintained AHT trace gives the least original point of every orbit as a union of at most `G` intervals, where `G` counts static gap intervals in the trace | `article/sections/transversals.tex` |
| Boundary circles as an additive weight | One selected point from each boundary-curve orbit, included in the full-surface point universe, counts actual boundary circles componentwise | `article/sections/transversals.tex` |
| Two-weight topology census | One boundary discovery and two weighted surface discoveries recover the joint distribution of Euler characteristic, boundary count and orientability | `article/sections/spectra.tex` |
| Sparse cover inversion | The base and orientation-cover histograms uniquely determine orientable and nonorientable counts, with a separate zero-signature equation and full-support validation | `article/sections/spectra.tex` |
| Complete multiplicity restoration | Peeled vertex links and quadrilateral content can be restored to every component type, with parity-aware scaling of one-sided components | `article/sections/kernel.tex` |
| Source-bound replay | Completed certificates are checked against the original triangulation/vector using independent reduction, transversal and spectrum checks | `article/sections/implementation.tex` |

The runtime's ambient contract is finite, compact, connected and orientable,
with exactly one torus boundary. Normal surfaces are properly embedded and
specified by admissible binary standard coordinates. Closed surface
components, multiple components and one-sided components are allowed.

The orientation-double assertion uses the orientability of the ambient
three-manifold: `F(2x)` consists of two copies of each orientable component
and the connected orientation double of each nonorientable component. An
unqualified application in a nonorientable ambient manifold would require a
different argument.

## The key reconstruction equations

For the integral signature `v = (chi, boundary_circle_count)`, let `H` be the
base histogram, `K` the orientation-cover histogram, and `O`, `A` the
orientable and nonorientable parts of `H`. Then

```text
H(v) = O(v) + A(v)
K(v) = 2 O(v) + A(v/2)
```

An absent or nonintegral half contributes zero. Away from zero, finite
support and increasing norm allow sparse inversion. At zero the equations
are solved directly:

```text
A(0) = 2 H(0) - K(0)
O(0) = K(0) - H(0)
```

The zero case distinguishes tori from Klein bottles even though both have
signature `(0,0)`. The implementation checks integrality, nonnegativity,
surface classification and the full forward equations, including cover-only
support. Conserving the total Euler characteristic is insufficient.

The core decomposition has the form `x = g p + sum_v m_v L_v`. Scaling an
orientable component by `g` yields `g` copies. Scaling a nonorientable
component yields `floor(g/2)` copies of its orientation double and one
original component precisely when `g` is odd. Thus total component count
does not in general scale by `g`. Boundary vertex links restore discs;
interior vertex links restore spheres.

## Complexity and novelty

The supplied-vector algorithm has polynomial encoded cost. Its parameters
are tetrahedron count and binary coordinate size, not knot crossing number.
It does not expand every normal disc, boundary arc, or output multiplicity.
The weight dimension is two, although the construction also carries a
compressed boundary transversal and uses two surface queries.

The sharper sparse-inversion operation bound assumes fixed weight dimension
and ordered maps. The delivered Python dictionary implementation can encounter
adversarial integer-key collisions; its conservative worst-case bound remains
polynomial. The article states both bounds and charges temporary integer bit
growth explicitly.

Core reduction bounds the primitive coordinates in terms of tetrahedron
count and quadrilateral height divided by quadrilateral content. For a
fixed core with growing outer multiplicities, the expensive orbit schedules
depend only on the core. Input reading, validation, source fingerprints,
gcd/division, reconstruction and serialization still depend on the original
bit size. No constant-time claim is made for arbitrarily long inputs, and
no universal speedup over the full-coordinate route follows from dimension
alone.

[Agol–Hass–Thurston](https://arxiv.org/abs/math/0205057), particularly
Corollary 17 and the normal-coordinate orientability discussion, already
establish polynomial encoded component-topology computation and use doubled
normal coordinates. The pinned ProveIt baseline already contains weighted
component queries, full component-coordinate recovery, normal-scaling
formulas, and the vertex-link/quadrilateral core for essential-disc counts.

The contribution here is the explicit smaller observer, compressed boundary
markers, sparse inversion, complete spectrum restoration, independently
checkable implementation and measured comparison against the existing
coordinate-based composition. Priority for this exact combination is not
asserted. It is neither the first polynomial topology algorithm nor a new
complete quasi-polynomial unknot recognizer.

## What the experiments establish

- The focused gate passed 148 methods, including the new primitives and
  their relevant inherited geometry/orbit dependencies. It is not a claim
  that every historical ProveIt test or unrelated benchmark was rerun.
- The final fresh Regina audit checked 664 bounded source vectors, obtaining
  1,395 exact API comparisons and 1,395 accepted certificates with no failures.
  Its frozen triangulations represent 26 isomorphism classes; relabelings
  increase labeled cases, not the number of isomorphism classes.
- The external oracle expands bounded surfaces and is independent of the
  producer's geometry. It is not used as an expanded oracle for huge binary
  inputs or presented as a compressed competitor on those inputs.
- Large-integer tests and paired benchmarks exercise encoded arithmetic,
  core-sensitive behavior and certificate costs. Their measured speedups
  apply to the documented families and configurations. They are not a
  complexity proof or an end-to-end recognizer benchmark.
- Certificate mutation tests check rejection beyond easy aggregate
  invariants. The Python verifier and human-readable mathematical proofs
  are not a proof-assistant formalization.

Recorded evidence is in `results/regression_summary.json`,
`results/regina_audit.json`, `results/benchmark-final.json`, and the retained
proofs and formula-audit records. The article explains comparison arms,
pairing, warmups, repeated measurements, source stability and limitations.

## Remaining global obligations

The observer computes the topology of a supplied normal vector. It does
not discover the useful vector, prove that a negative query excludes every
compressing disc, or establish that the triangulated manifold is the
exterior of the user's knot diagram. A positive disc row also needs a
componentwise essential-boundary argument. Abstract type does not determine
boundary slope, component coordinates, cutting instructions or attachment
maps.

If a future outer algorithm makes `Q(n)` queries of encoded size at most
`S(n)`, this observer contributes `Q(n) poly(S(n))` time. Quasi-polynomial
bounds on both functions would preserve quasi-polynomial cost at this stage.
The present work does not establish those bounds for unknot recognition.

The next obligations are certified diagram-to-exterior provenance,
controlled surface discovery, compressed cutting with attachment data,
and bounds on hierarchy depth, restarts and total encoded volume.
The article distinguishes the general quasi-polynomial class from the
stronger `n^(O(log n))` target and reviews the quantitative scope of
Lackenby's announced approach and available primary sources. The full
recognizer's general asymptotic guarantee remains unchanged by this patch.
