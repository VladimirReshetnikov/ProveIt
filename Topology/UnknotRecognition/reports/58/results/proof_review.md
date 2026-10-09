Review provenance: separate model audit within this research session; not external peer review or proof-assistant verification.

# Adversarial review of the component-topology continuation

## Verdict

I found no mathematical defect in the combined construction under the delivered
ambient-manifold contract. The four main steps are sound: least representatives
from AHT, lifted boundary markers in the normal orientation double, sparse
histogram inversion, and orientability-aware restoration of the quadrilateral
core. The current runtime implements those steps consistently. No runtime files
were modified and no additional large test campaign was run for this review.

Reviewed material: the current `deliverables/article/sections/overview.tex`;
`normal_topology.py`, `normal_topology_verify.py`, `normal_topology_geometry.py`,
`topology_spectrum.py`, and the two transversal modules; and the maintained
synthesis chapters on interval orbits, weighted components, normal multiplicity,
normal boundary classification, normal certificates, affine families, and
surface covers. The available report 51–53 README files were also checked.

## Findings requiring exposition attention

1. **Use an example matching all the aggregates that are claimed insufficient.**
   The current overview compares torus + sphere with two discs. This only matches
   total Euler characteristic; their total boundary-circle counts differ. A
   stronger example is *two tori* versus *a sphere and a genus-two closed surface*.
   Both have two orientable components, no nonorientable components, Euler sum
   zero and zero boundary circles, but their type spectra differ. This is an
   exposition improvement, not a flaw in the claimed insufficiency.

2. **Explicitly acknowledge that the previous coordinate route can already
   determine the same final spectrum.** The existing full-coordinate census
   supplies every distinct component vector and its multiplicity. Running the
   existing connected-topology operation on each distinct vector recovers the
   joint type spectrum. Classical AHT also already proves polynomial component
   topology. The substantive refinement is the constant-dimensional observer,
   boundary representative compilation, source-bound composition, and restoration
   through the stronger numerical core. The overview credits AHT correctly;
   replacing “new information” with “the directly returned information” would
   further avoid suggesting first computability of these types.

3. **Keep arbitrary valid traces distinct from the maintained discovery trace.**
   The transversal compiler and verifier are polynomial in the explicit supplied
   trace length. An adversary can supply a long valid trace; correctness does not
   make every valid trace polynomial in source size. Source-size polynomiality
   uses the maintained AHT producer's polynomial trace bound. The overview's
   current phrasing is defensible, but the theorem statement should say this
   explicitly.

4. **Do not imply completely independent geometry.** The producer and verifier
   share validated normal geometry, Euler ownership, the boundary embedding, and
   vertex-link classification. Their independent paths concern source/trace
   replay, selector reconstruction, weighted transport, histogram equations, core
   arithmetic, and final totals. The current source comments make that distinction
   accurately; the finished article should retain it.

## Mathematical checks

### AHT least representatives and interval bound

The crucial point is stronger than preservation of orbit *count*: the local
truncation rules preserve the induced equivalence relation on surviving points,
and every deleted point reaches a strictly earlier surviving point. For a positive
translation, repeated inverse translation reaches the prefix; for the certified
trimmed reflection, the image lies in its disjoint earlier domain. The survivor
injection into original labels is increasing. Thus an orbit's least original
point cannot be truncated, and a contracted static singleton is precisely that
least point when its orbit is completed.

The reverse selector argument proves the output interval count at most `G`:
restoring `g` contracted gaps can increase the selected run count by at most `g`,
and restoring a truncated suffix adds no selected point. The implemented convex
hull of a lifted selected interval is legitimate because it only fills restored
gaps, all independently marked selected. No point from a previously unselected
surviving interval is inserted by the hull. This avoids an otherwise plausible
but false claim that arbitrary inverse maps preserve interval shape.

The claimed raw piece bound `1+2G` and live-list bound `1+G` are also sound.
Gap endpoints can split live intervals; truncation only restricts a prefix. The
final bound is on encoded intervals, not their cardinality.

### Normal double and marker lifting

The full and boundary universes use the same global edge orientation, and their
edge-block inclusion is translation. Doubling every normal coordinate doubles
every block offset and length. Hence projection is exactly `q -> floor(q/2)`,
and a base interval `[a,b)` has full preimage `[2a,2b)`.

Euler ownership lifts correctly: each owned base cell has two lifted cells and
each receives its corresponding lifted owned point. Boundary markers require a
separate geometric fact, which is satisfied: the orientation character restricts
trivially to each boundary circle, because that circle has an annular collar in
the surface. Its orientation cover has two circles, with one lifted marker on
each. This remains true when the whole component is one-sided, for example a
Möbius band whose double is an annulus.

Using only three orbit discoveries is therefore justified. This would fail for
an arbitrary unrelated two-sheeted cover whose boundary monodromy were nontrivial,
or for a nonorientable ambient manifold where normal orientation and surface
orientation differ. Those cases are excluded by the contract.

### Sparse inversion

The equations are correctly implemented:

`H(v)=O(v)+N(v)` and `K(v)=2O(v)+N(v/2)`.

Nonzero predecessors have smaller `l1` norm. Missing base support implies zero
nonorientable multiplicity, so a dictionary lookup is sufficient; there is no
need to traverse absent numerical intermediate signatures. The special equation
`N(0)=2H(0)-K(0)` is necessary and is present. It distinguishes torus/Klein-bottle
rows, which otherwise share `(chi,b)=(0,0)`.

The implementation correctly reconstructs the *complete* cover histogram after
inversion, including cover-only keys. It checks integrality, nonnegative counts,
and the orientable/nonorientable classification formulas. Independent checking
uses the forward cover equations rather than the producer recurrence.

### Full vertex-link and quadrilateral core

The new code correctly reuses the established removal of disjoint vertex links,
then treats the remainder as `g` ordered normal sheets of the core. Normal-fibre
monodromy is either identity or reversal; no arbitrary permutation is assumed.
Consequently an orientable core component produces `g` copies, while a
nonorientable one produces `floor(g/2)` orientable doubles and an odd central
copy. Its doubled boundary count and Euler characteristic are both twice the
original, yielding genus `crosscaps-1` as required.

The reconstruction distinguishes boundary-vertex discs from interior-vertex
spheres using global vertex roots incident to boundary faces. The inherited
validator has already proved those link types. Triangle-only inputs have zero
core and are correctly restored entirely from those links. The independent
verifier recomputes the original minima, gcd, exact quotient and full source
digest, so merely substituting another vector with the same core cannot pass.

## Duplication and antecedents

No inspected maintained module already exposes this general two-weight spectrum
for arbitrary supported admissible normal vectors.

* `normal_multiplicity.tex`: aggregate counts and the sheet-pair scaling principle
  already exist. Credit these as the source of the full-spectrum restoration rule.
* `normal_boundary.tex`: distinguishes boundary presence and orientability, but
  does not give each component's number of boundary circles or Euler characteristic.
* `weighted_components.tex` / report 53: componentwise Euler and homology values,
  boundary-point counts, full-coordinate recovery, and the quadrilateral disc-count
  core already exist. The present core extends an existing reduction rather than
  introducing vertex-link stripping or quadrilateral content.
* `surface_covers.tex` / report 24: already computes full component topology and
  marked cover signatures under a global dihedral covering-presentation promise.
  Its input promise is much narrower than general normal-arc systems. The present
  output type overlaps, but the general supplied-normal-vector operation and its
  boundary-transversal construction are not duplicate implementations of that API.
* AHT already gives polynomial normal-component topology. Broad algorithmic novelty
  or priority for the entire problem would be unsupported. The current overview
  explicitly avoids that claim and should continue to do so.

The earlier proposed *two-weight essential-disc query* is different: it replaces
two boundary homology coordinates with one ambient-homology coordinate. The present
two weights are `(chi,b)` and by themselves do **not** detect boundary essentiality.
The runtime and overview currently preserve that distinction correctly.

## Complexity and performance claims

The current overview does **not** claim an unjustified asymptotic recognition
speedup. Its warning that dimension two can incur more runs and more orbit queries
is appropriate. Lower weight dimension by itself proves neither a uniform runtime
gain nor a lower worst-case polynomial degree.

The defensible core-sensitive statement is that orbit-stage numerical cost depends
on the reduced core bit length, while full-source reading, validation, gcd/division,
fingerprinting, restoration and outer proof fields still depend on original bits.
Even a fixed core does not make the full call constant-time. A measured local gain
must compare equal final outputs, include the stated verification work on both
sides, and retain primitive/no-reduction controls. The benchmark section was not
yet available at this review, so its numerical claims remain outside this sign-off.

Type histograms do not preserve an embedding, component normal vector, boundary
slope, cyclic attachment order, or cut-manifold structure. They cannot on their own
bound candidate search or state growth in a hierarchy. The existing explicit
provenance and quasi-polynomial limitations are mathematically necessary and
accurately stated, rather than optional cautions.

## Final article review

I subsequently read every completed article section, including
`benchmark_results.tex`, the generated benchmark CSV, and the reference
composition and timing loops in `topology_research/benchmark.py`. The earlier
four main exposition recommendations were integrated. The runtime remained
frozen throughout this review; I did not run expensive tests or benchmarks.

**No mathematical correctness blocker found.** The completed article preserves
the essential assumptions in the proofs, attributes the inherited AHT and
normal-coordinate results, distinguishes abstract type from embedding, and
does not convert a local polynomial observer into a claimed quasi-polynomial
recognizer. The restoration formulas, zero-signature handling, representative
invariant, and source/checker contracts match the current runtime.

One small complexity-scope correction was sent to the author:

* In `sections/spectra.tex`, the sparse doubling inversion theorem begins with
  weights in `Z^d`. Its `O(s)` integer-operation count requires **fixed dimension
  d**; for variable dimension processing each vector needs dimension-dependent
  work. Add “For fixed d” to the cost statement. The delivered dimension is two,
  so this does not alter the algorithmic claim used by the application.
* The deterministic `O(s log(s+1))` comparison / `O(s ell log(s+1))` bit bound
  should explicitly describe the ordered-map version. The implemented Python
  dictionary version does not guarantee constant-time lookup against adversarial
  integer hash collisions. It is still polynomial in explicit input size, so the
  main polynomial normal-topology theorem is unaffected.

An optional sentence-level refinement was also sent: the overview's “two discs
with different boundary slopes” example can suggest distinct essential-disc
slopes within one fixed torus-boundary manifold. The existing vertex-link-disc
versus meridian-disc example is precise and sufficient. “The same abstract type
can have different embeddings or peripheral data” avoids that unnecessary
geometric implication.

### Final measurement assessment

The measurement protocol compares the same final spectrum, while openly
acknowledging that the coordinate reference computes richer intermediate data.
Both sides produce certificates and perform independent replay inside the
reported total. The benchmark code confirms fresh source reconstruction and
separate producer/verifier timing; serialization is outside the timed region.
The tables' medians, paired factors and certificate sizes agree with the generated
CSV. The 13 cases, four arms, one warm-up and five measured rounds account for
52 warm-up calls and 260 measured calls, as reported.

The text correctly retains negative cases: the unreduced two-weight query is
slower on the largest multiplicity example and the even Möbius example; reduction
adds overhead on a primitive example. The A/A range is disclosed, and no
statistical-significance, fitted-exponent, or whole-knot improvement claim is made.
The original meridian-family exponent and pure-link timing issues are corrected.
The text reports the separate post-measurement formula audit without pretending
that the first arm's output was an independent oracle during timing.

The reported fresh Regina and regression counts are consistent internally and
are described as bounded geometric/implementation evidence. Their raw execution
was supplied by the main task; this final proofread did not repeat those jobs.
The package's final assembly and manifest check remain the main task's final
delivery gate, since its README and copied artifact tree were still being
assembled while this article review was performed.

The author subsequently confirmed application of the fixed-dimension and
ordered-map qualifications, explicit input-to-intermediate bit growth, a
conservative adversarial Python-dictionary polynomial bound, and the revised
embedding wording. **No open article correction or mathematical blocker remains
from this review.** No runtime files were changed as part of these corrections.
