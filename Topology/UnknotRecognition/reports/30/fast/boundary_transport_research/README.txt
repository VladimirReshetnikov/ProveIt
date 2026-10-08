BOUNDARY TRANSPORT RESEARCH — 8 OCTOBER 2026

Repository inspected:
  VladimirReshetnikov/ProveIt
  HEAD 8a95834940cf77cdab1b39571ffc102ca8b6bede
  Topology/UnknotRecognition/{fast,synthesis,docs}

NEW CODE

  fast/fastunknot/boundary_transport.py
  fast/tests/test_boundary_transport.py

The new module subclasses the existing checked CoverIndex. It adds no
dependency, changes no existing recognition path, and makes no knot verdict.
No existing core file was edited by this contribution.

BoundaryTransportIndex.transports accepts:
  source_component: a sheet selecting the source component;
  target_component: a sheet selecting the target component;
  point_pairs: [(source_sheet, target_sheet), ...];
  boundary_pairs: [(base_boundary_index, source_sheet, target_sheet), ...].

Boundary correspondences refer to whole peripheral orbits. The two supplied
sheets need not map to one another. Component-selector sheets are not marks.
The base presentation and its boundary paths remain fixed. Circle
parametrizations, arbitrary attaching maps, and ambient embeddings are not
part of this interface.

The answer includes a canonical source root and at most two disjoint
arithmetic progressions of its possible target images. Their binary counts
give the exact number of covering isomorphisms. Every represented map is
evaluated using inherited transport_sheet(source_root, image, sheet).

BoundaryTransportIndex.cyclic_marked_signature additionally handles canonical
keys in pure translation presentations. Point marks are processed in order,
then boundary marks in order; their schema is part of the key. The result
includes the full key, a root image transporting to the residue-zero canonical
component, the phase modulus, the number of maps to canonical form, and the
exact number of possible marking types for that schema.

THEOREMS

Full proofs are in package/unknot_binary_tensors/sections/06_transport.tex.

1. For k constraints on the checked dihedral cover, compute every compatible
   map in O((k+1)B^3) bit work after preparation, returning O(B) bits in at most
   two root progressions. Translation boundary constraints are congruences;
   the first reflection boundary restricts the root to at most two values.

2. For arbitrary connected finite surface covers, if boundary-preserving maps
   exist, their number divides the gcd of the marked lift degrees. The
   remaining ambiguity is cyclic. A point constraint leaves at most one map.

3. For a cyclic component of degree m and mark periods q_i dividing m, a
   complete canonical key is obtained by generalized CRT normalization.
   Every marking has m/lcm(q_i) automorphisms. The exact number of types is
   product(q_i)/lcm(q_i). Canonical digits are independently bounded by
   gcd(lcm(q_1,...,q_{i-1}),q_i), permitting direct mixed-radix indexing.

4. For k>=1 boundary-circle slots without point phases, their marking count
   is at most max(2,-chi(C))^(k-1) for a connected cyclic surface cover C.
   Polynomial negative Euler complexity and O(log n) slots therefore give
   2^{O(log^2 n)} normalized local markings. This is a theorem about a fixed
   checked component type and fixed base labels, not a global hierarchy bound.

5. Exponential marking diversity still occurs without the Euler constraint:
   a four-holed-sphere cover with W=2^beta and shifts 1,W/2,W/2 has W/2
   inequivalent ordered two-boundary-circle markings. Its genus is W/2,
   so it does not refute the preceding bounded-Euler theorem. Point phases
   retain W types even on a W-fold annulus cover, whose genus is zero.

The signature alone costs O((k+1)B^3). Returning the potentially kB-bit exact
type count by ordinary products conservatively costs another O(k^2 B^2).
Do not state O(k B^3) for all operations when k is unrestricted relative to B.

VALIDATION

audit.py constructs explicit generator permutations and uses breadth-first
propagation of equivariance to find all covering maps on small fibres. It
does not use the production classifier, gcd formulas, CRT, or the rooted
transport formula for expected answers.

  817 presentations
  3,276 component pairs
  650,992 total queries:
    3,276 unmarked
    19,336 point
    38,076 boundary
    295,152 double-boundary
    295,152 mixed point/boundary
  12,496 literal transport-value checks
  all passed; elapsed 6.715 seconds on this machine

audit_canonical.py independently computes marking equivalence classes from
literal covering-isomorphism actions on peripheral cycles.

  285 presentations, fibres 1 through 9
  6,356 signature queries
  1,034 marking classes
  44,790 witness-map checks
  all passed; elapsed 0.123 seconds

The maintained unit test module contains nine tests, including independent
literal-map checks, shared-factor CRT inconsistency, whole-circle versus
point constraints, the exact type-count formula, fixed and paired dihedral
components, invalid inputs, cancellation propagation, 58,883-bit sheet
counts, and a hexadecimal JSON roundtrip returning a 24,001-bit map count.

TIMINGS

benchmark.py measures prepared queries separately from cover preparation.
Results include literal cyclic-cover scans, increasing binary input lengths,
and reflection constraints on paired components. The literal comparator
materializes peripheral orbit labels and scans root images. Its performance
is an encoding comparison for this local kernel, not a benchmark of complete
knot recognition or an empirical estimate of the hierarchy depth.

Selected measured results (seconds):
  W=1,048,576, two cyclic boundary constraints:
    literal scan 0.761936287
    compressed prepared median 0.000005929
    exact compatible map count 128
  W=2^12000 * 3^12000 * 5^12000 (58,883 bits), two constraints:
    cover preparation 0.004245231
    compressed prepared median 0.015026846
    map count 5^12000, one progression
  paired model with a 48,001-bit W and one reflection boundary:
    compressed prepared median 0.004890771
    two maps, two progressions

All numeric data, including platform metadata and the full timing grid, are
in benchmark-results.json. Timings are machine-specific and are not proofs.

REPRODUCING

From Topology/UnknotRecognition/fast:
  python -m unittest tests.test_boundary_transport
  python -m fastunknot.boundary_transport /path/to/example-query.json

With that fast directory on PYTHONPATH:
  python audit.py --output audit-results.json
  python audit_canonical.py --output canonical-audit-results.json
  python benchmark.py --output benchmark-results.json

The example query returns roots 29+36j for 0<=j<10.

PRIMARY SOURCES AND PRECISE LIMITS

Marc Lackenby, Incompressible surfaces, hierarchies and unknot recognition,
arXiv:2607.23350v1, 25 July 2026, 54 pp.
  https://arxiv.org/abs/2607.23350
  https://arxiv.org/html/2607.23350v1

Section 9 deliberately estimates iterations, not full running time:
L(g+1)^L. Section 10 gives L <= 4 c_q(H). There is no logarithmic-depth
or quasi-polynomial running-time theorem in this preprint. Its introduction
describes possible speed-up as future work. The author's September 2026 page
lists this preprint and the older quasi-polynomial seminar slides separately.

Theorem 14.4 already supplies polynomial compressed cutting, in h and log
extended surface weight, with topology and incidence data for the parallelity
bundle. Proposition 14.2 additionally performs admissibilization and interior
parallelity removal, but assumes that the current boundary pattern is
essential. Theorem 14.1 efficiently encodes/verifies an essential hierarchy.
These should not be used as an unconditional deterministic fast constructor
on unknown-essentiality repair branches without additional argument.

Earlier Oxford/UC Davis 2021 announcements state n^{O(log n)}; Princeton's
April 2021 abstract and the November 7, 2024 Tsinghua abstract instead state
2^{O((log n)^3)}. They are distinct targets, both quasi-polynomial.
  https://www.maths.ox.ac.uk/node/60914
  https://www.math.princeton.edu/events/unknot-recognition-quasi-polynomial-time-2021-04-15t193000
  https://qzc.tsinghua.edu.cn/en/info/1122/4171.htm

Allen Hatcher, Algebraic Topology, Section 1.3:
  https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf

Agol, Hass, Thurston, The computational complexity of knot genus and spanning
area, Transactions of the AMS 358 (2006), 3821-3850.

Lackenby, Some fast algorithms for curves in surfaces, January 2026 revision,
accepted in Discrete and Computational Geometry (author's listing):
  https://people.maths.ox.ac.uk/lackenby/AlgorithmsSurfaces13jan26.pdf
Theorems 1.1 and 1.2 compute geometric intersection and isotopy of essential
normal 1-manifolds in polynomial time in triangulation size and logarithmic
weights; the paper also treats pattern-relative positioning. These are useful
existing ingredients for a future boundary-transport implementation and
should not be described as new results of this package.

FURTHER RESEARCH TARGETS

1. Construct, or give a checkable certificate for, the promised dihedral or
   cyclic covering presentation inside a parallelity bundle of a triangulated
   knot exterior. Preserve base schema, orientation character, and labelled
   peripheral paths under cutting.

2. Determine when hierarchy attachment data can be represented by whole
   circles rather than point phases. Prove that the necessary quotient is
   respected by violating-disc lift and repair. The annulus example shows
   why suppressing a physically meaningful point phase is invalid.

3. Extend boundary constraints to parametrized cyclic gluing maps and their
   compositions. Identify which phase constraints remain linear congruences
   and which introduce coupling among different component parameters.

4. Prove preservation of polynomial negative Euler complexity and O(log n)
   attachment slots on the actual pieces visited by a hierarchy. Together
   with bounded presentation diversity and compatible repair, the local
   quotient theorem could then contribute to a global quasi-polynomial bound.

5. Build a verified map between literal normal-surface cutting output and
   these compressed component/attachment records. Test one complete repair
   including transported peripheral data; avoid using topology-only component
   summaries as a substitute for attaching maps.

6. Use the exact cyclic marking count to report state entropy during a
   prototype computation. Distinguish bit length, map ambiguity, normalized
   state diversity, and number of actually visited states.
