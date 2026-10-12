# Integration contract

## Additive placement

Place this complete folder at
`Topology/UnknotRecognition/research/interface_homology/`, retaining the
article, table inputs, package, tests, and frozen evidence together. Do not
replace `normal_parallelity.py` or enable recognition dispatch merely by
placing the package. The package does not emit knot verdicts.

Source reference: ProveIt revision
`ed166080d7db14dd7a91d07788996f02947dd92a`.

## Existing upstream achievements

`synthesis/parallelity.tex` and `fast/fastunknot/normal_parallelity.py` already
extract all-dimensional source parallelity, classify its bases and twisting,
and retain a complementary inherited core of at most 30T handles. The
conservative source port bound is 66T. These are prerequisites and prior
work, not new results in this delivery. An inherited core is not automatically
an admissible patterned hierarchy structure.

## Proposed adapter boundary

A native adapter must start from an independently accepted
`normal-cut-parallelity-v1` packet bound to its source triangulation and
unscaled normal coordinates. It must construct the following additional
relative information without enumerating normal copies:

1. A finite CW/handle model for the inherited core, with actual closed edge
   words for its two-handle attachments. The algebra only needs `d_2` and the
   number of three-handles for Euler characteristic; the source proof must
   still establish the topological attaching maps.
2. The exact quotient partition of endpoints of core-facing base arcs.
   Each endpoint occurrence has its own binary mask bit. Push these through
   the correct source-vertex orbit relation. Keep the nonzero endpoint masks,
   form the finite degree-one/two graph, and merge its paths and cycles.
3. The core paths carried by all port arcs and their endpoint images.
   Whole-circle walks give `Loop` words. Distinct circles on an orientable
   base must have their relative signs derived from one coherent base
   orientation; locally orienting each circle independently is not enough.
4. The base type, total boundary count, genus/crosscaps, and multiplicity.
   A ported component must have multiplicity one. Only unported components
   may be combined into repeated profiles.

`ports.py` implements the finite quotient/port-graph stage after these
source data have been supplied. It does not query AHT, reconstruct native
face charts, or authenticate the endpoint quotient against the source.
`verify_condensation` independently verifies the algebraic transition from
`Model` to `Condensation`; it does not establish these geometric premises.

The adapter should emit its own versioned certificate with the source hash,
endpoint-query proof, relative orientation evidence, and paths. A hash alone
is not the certificate. Native replay should derive this information from
an independent source model rather than rerun the producer formulas.

## Validation before dispatch

Compare complete integral homology with a genuinely expanded cut oracle,
not just Euler characteristic or the final rank. Test source self-gluings,
high-degree edges, empty surfaces, one-sided surfaces, binary parallel
multiples, and bases supplied entirely by selected higher-index handles.
Retain mutations of endpoint identifications, port owners, and the sign of
one whole circle relative to another. Retain the eight-port disc-base case:
eight adjacent ports can form one circle, not eight intervals.

Measure source construction, source replay, interface extraction, algebra,
and output under common budgets. Preserve tiny-input regressions and A/A
controls. The delivered 116.599 model-kernel ratio is not a forecast of a
native speedup. Matrix incidence and word length, not merely handle count,
must be bounded for the strongest torsion/cost corollaries.

## Separate S3-aware path

For boundary-only homology and the sphere terminal, a proof chain must
bind the original diagram to its embedded exterior and certify every
subsequent operation as cutting, component selection, or an independently
verified homeomorphic change of representation. Filling or identifying
boundary components needs a separately proved rule.

Only after validating that ancestry and the boundary profiles may the
consequences returned by `s3_boundary_consequences` be promoted to certified
results. Its current return value explicitly reports that no embedding
hypothesis was checked. A generic compact orientable triangulation with one
torus boundary does not carry this ancestry. Retain generic sphere-boundary
nonball controls; a punctured homology sphere is still not certified by its
Betti numbers.

## Remaining hierarchy obligations

This integration does not find nonseparating cutting surfaces, pull symbolic
cohomology into native source cocycles, transport arbitrary boundary patterns,
construct every later admissible core, implement balanced-region searches,
or prove logarithmic hierarchy depth. The article states a sufficient
quasi-polynomial accounting criterion only after such hypotheses have been
proved for a complete hierarchy procedure.

## Documentary correction

The root README's older boundary-only checkpoint uses a broad statement that
bounded-core geometry remains open. The newer `parallelity.tex` supplies a
bounded inherited core. Reconcile that wording while preserving the still
correct qualification that a bounded **admissible patterned** core and the
full hierarchy complexity proof remain open. No production-file patch is
included, to avoid overwriting later work or obscuring this distinction.
