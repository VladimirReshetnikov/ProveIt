# Strict Pachner 3→2 preprocessing: finite evidence and integration obligations

Scratch only. No native, research-package, article or publication files changed.
No LP, ray search, or recognition benchmark was run in this experiment.

## Retained results

The initial sources are authentic endpoints of existing diagram crushing chains:

| Source | Initial tetrahedra | Deterministic trace | Accepted moves |
| --- | ---: | --- | ---: |
| trefoil | 10 | 10,9,8 | 2 |
| figure eight | 13 | 13,12 | 1 |
| two-trefoil sum TT | 23 | 23,22,21,20,19,18,17 | 6 |

Every source has one vertex and one finite torus boundary. At each stage the
scan reconstructs global edge incidence classes from the exact face pairings,
excludes boundary edges, and keeps classes with exactly three local incidences
in three distinct tetrahedra. Representatives are ordered by the smallest local
(tetrahedron,endpoint,endpoint) triple. The first independently verified move is
accepted; the next stage recomputes the entire incidence table. In these nine
steps the first eligible candidate always succeeded. Each terminal source has
no eligible edge; this is a complete scan only for this strict local move.
It is not a minimum-triangulation certificate or a claim that no other move
can simplify the source.

The old boundary-unlayer audit supplies the *baseline* 10/13-tetrahedron
endpoints, not its optional-peel endpoints. TT comes from the immutable
composition-state gzip. Initial full diagram chains independently replay.
`scan.json` preserves exact original file hashes and selectors, their historical
native pins, every current source, candidate, certificate, successor and current
native hashes. Historical pins are not reinterpreted as current pins.

`replay.py` uses no discovery producer or LP call. It reconstructs the candidate
sets independently from the original incidences, verifies all nine old
`pachner-32-v1` packets, checks strict descent and one vertex, and verifies the
empty terminal candidate sets. `replay.json` records its own fresh pins.

A fresh Regina 7.4 control checks each starting and resulting finite source,
performs Regina's Pachner move at the same indicated global edge, and finds an
explicit combinatorial isomorphism to the native successor. All nine agree.
The labelled arrays are *not literally equal*: Regina labels the replacement
differently. `regina-check.json` retains the isomorphism maps, both iso-signatures
and precise selected incidences. This oracle comparison is corroboration;
independent native relative-boundary proof replay is the soundness mechanism.

## Why the existing relative-boundary certificate is the right theorem

Use five distinct *formal* labels 0,1,2,3,4 for an abstract triangular bipyramid.
The old three tetrahedra have vertex sets 3401,3412,3420; the new two have vertex
sets0123 and0124. In a geometric triangular bipyramid these are two
triangulations of the same closed ball, with identical six triangular boundary
facets. The identity on that geometric ball gives a relative-boundary PL
homeomorphism (a common subdivision suffices if a simplicial representative is
required).

The native verifier reconstructs all old and new internal face pairings from
these formal labels, and requires their six formal boundary signatures to agree
exactly. Signatures encode boundary faces, attachments to the unchanged outside,
and pairings between boundary facets of the region itself. The relative-boundary
homeomorphism therefore descends through precisely the same boundary
identifications. Global vertex or edge identifications do not require an embedded
bipyramid in the ambient manifold. It is the *formal region* that is a ball.
Both ambient triangulations separately pass finite orientable torus-boundary
manifold validation, and every exterior face pairing remains unchanged after
literal survivor relabelling. Thus the operation preserves the compact manifold,
without relying on a normal-surface or Euler-cone argument.

This theorem is narrower than arbitrary local replacement: three distinct old
tetrahedra and the exact standard internal link are checked. A degree count alone
is not the certificate. Interior status and distinct incidence conditions are
cheap candidate filters; independent relative-boundary replay is mandatory.
No peripheral cocycle transport is currently supplied, so the operation is
appropriate for unmarked authenticated knot-exterior recognition. A marked
consumer needs additional verified boundary-data transport even though this
move preserves the actual boundary facets formally.

## Concrete callback issue found

The old `verify_pachner_32` executes source preparation inside
`except NormalOrbitError: return False`. A caller callback raising that same
exception class at the second callback is swallowed. `replay.json` retains this
exact control: it returns False instead of propagating the original object.
Earlier maintained tests exercise RuntimeError, not this malformed-input class.
This is not a proof-soundness failure, but it violates the stronger cancellation
contract required by the newer driver and independent chain verifiers.

A new wrapper must guard callbacks by rethrowing a private BaseException carrier,
then unwrap the original exception with its traceback outside malformed-packet
handling. The same guard must surround discovery candidate attempts, otherwise
an expected-invalid-move catch can misclassify caller NormalOrbitError as an
ordinary rejected edge. Do not make the new integration depend on changing this
legacy verifier's public behavior without separate compatibility review.

## Proposed native integration, after current publication

Add an optional source producer that prepares the source once, derives the
finite ordered eligible-edge list, and tries existing `pachner_32` constructors
with guarded callbacks. Every accepted result must pass a new independent
strict wrapper verifier. Avoid importing the candidate producer into the new
verifier. A source-only API returns UNCHANGED or REDUCED with diagnostics and a
small authenticated packet. No knot verdict is returned by this local API.

Suggested outer packet `normal-pachner-32-v1` has exact fields:

- schema;
- source_sha256, over the complete canonical labelled source;
- certificate, the existing exact `pachner-32-v1` formal-region proof;
- successor, the full labelled output.

The wrapper independently checks source binding, exact types/fields, strict
nonempty tetrahedron descent and the legacy relative-boundary verifier under a
callback guard. Invalid packets return False; caller exceptions preserve identity.
The source producer should avoid a work limit initially: a full strict candidate
scan is polynomial preprocessing. If a work cap is added, exhausted scan must
not return UNCHANGED with a claim of complete candidate exhaustion.

A new version of the authenticated diagram chain is needed if it accepts these
packets. Existing v1 (crush only) and v2 (crush plus unlayer) keep their meanings;
a v3 can additionally dispatch this packet to its independent verifier. Every
nonterminal move still strictly decreases the number of tetrahedra. The driver
must rebuild all normal algebra, ray coordinates, learned conflicts and dual
caches after a move. Existing negative certificates refer to the old source and
cannot be reused solely because the compact manifold is unchanged.

Keep the mixed-step allowance global: `max_crushes` already counts normal crushes
plus inverse layers, and a v3 option must also charge every3→2 move. New diagnostic
fields could count source scans, candidates attempted and accepted3→2 moves.
The factored wrapper's cap/stat mapping must be extended deliberately, as must
its option-validation coverage assertion. Changing the raw-driver signature
without extending that assertion currently fails safely; it must not silently
leave a new cap unshared across factors.

For a first integration use an explicit option, default false, until genuine
paired workloads establish its costs. Candidate priorities relative to inverse
layering should be deterministic and documented. The present scan starts on
historical baseline endpoints, so it has *not* tested the composition
vertex-reduction→unlayer→3→2 at every driver stage. In particular the figure-eight
13→12 step could overlap an existing collar simplification benefit. A next cheap
control should compare scans on the retained optional-peel endpoints and scan
for exposed layers after each accepted3→2 move; do not count the two reductions
as independent gains without that check.

## Polynomial bound and what remains open

There are O(t) edge classes at a t-tetrahedron source, and at most t-1 accepted
strict reductions. Each candidate construction, source validation and exact
relative-boundary check is polynomial in t; no normal coordinates of growing
bit size are involved. If P(t) bounds a source check and candidate attempt, a
naive full rescan implementation costs O(t^2 P(t)) in the worst case. Reusing the
article's conservative P(t)=O(t^2 log^2(t+2)) yields a deliberately loose
O(t^4 log^2(t+2)) bit bound. It can be tightened later without affecting the
polynomial conclusion. Explicitly retaining all source successors takes
O(t^2 log(t+2)) bits.

This proves only a polynomial strict preprocessing policy. There is no asserted
monotonicity for h, canonical Euler negativity, LP difficulty, certificate size
of later search, or recognition runtime. The three finite reductions establish
that this existing move can go beyond the tested vertex-reduced endpoints.
General quasi-polynomial recognition remains open.

## Literal proposed integration contract

The following is a concrete draft for the next implementation slice, subject to
independent review; these APIs and schemas are not currently maintained.

Public flag: `reduce_pachner32=False`, strict bool, on the raw and factored
crushing APIs. New source API:

```
reduce_pachner32_once(triangulation, *, check=lambda: None)
```

Outputs:

```
{'status':'REDUCED',
 'certificate':{'schema':'normal-pachner-32-v1',
                'source_sha256':<canonical full source digest>,
                'certificate':{'schema':'pachner-32-v1','region':[...]},
                'successor':<literal new face pairing>},
 'stats':{'initial_tetrahedra':n,'remaining_tetrahedra':n-1,
          'candidate_tests':j,'moves':1}}
```

or

```
{'status':'UNCHANGED','reason':<diagnostic>,
 'stats':{'initial_tetrahedra':n,'remaining_tetrahedra':n,
          'candidate_tests':j,'moves':0,'scan_complete':True}}
```

For consistency the positive stats can also record `scan_complete=False`: it
stops at the first valid reduction, rather than claiming to enumerate all moves.
This flag concerns the finite candidate scan, not recognition completeness.
Return no successor/certificate on UNCHANGED. Never call a source irreducible or
minimal merely because this local scan is complete. The wrapper can support all
finite connected orientable one-torus-boundary sources accepted by the old move;
vertex reduction makes intended search-stage sources one-vertex, but topology
soundness does not require adding an unnecessary vertex-count restriction.

New independent verifier:

```
verify_normal_pachner32(before, packet, *, check=lambda: None) -> bool
```

It accepts exactly the four outer fields above and delegates the strict nested
formal-region proof only after checking the outer digest and exact source types.
It requires n>=3, successor n-1>=1 and unchanged finite torus-boundary manifold
validation. Reconstructing formal vertices identifies the complete relative
boundary; source hash alone is never a topology proof. Caller callback guards
must enclose *every* old verifier invocation and expected-invalid-move catch.

The new chain is literally:

```
{'schema':'diagram-crushing-v3',
 'input_pd':...,'source_triangulation':...,'shelling':...,
 'steps':[<normal-ray-crushing-v1 or normal-boundary-unlayer-v1
           or normal-pachner-32-v1 packets>],
 'status':'REDUCED' or 'UNKNOT','triangulation':...}
```

The accepted field set is unchanged from v1/v2. Dispatch by exact step schema:
v1 allows only normal crushes; v2 adds certified inverse layers; v3 adds these
certified3→2 steps. A3→2 step must never produce None or conclude UNKNOT. The
old outer recognition-v1/v2 distinction describes the form of final Euler
exhaustion, so first inspect its existing checker before adding an unnecessary
third outer recognition schema: expanding the independently checked *chain*
version may suffice. Preserve both old versions' exact allowed step classes.

Priority at each source:

1. Run the existing positive vertex-reduction branch if applicable.
2. Run existing optional boundary unlayering if enabled.
3. Run the new optional strict3→2 scan.
4. Only if none reduces, construct the Euler source model and start search.

An accepted move in any branch restarts at1. This allows3→2 to expose an inverse
layer, and inverse layering to expose a new degree-three edge. Every restart
strictly decreases n; order is deterministic and is not an assertion that h is
monotone. No 2→3 escape or neutral move is included in this polynomial descent.

Use `len(steps)` for the global mixed-step limit in the raw driver. Before
appending any new reduction packet, require remaining max_crushes>0 when finite;
a terminal positive normal crush consumes one unit too. Keep all earlier source
search expenditures charged. Add diagnostic counters `pachner32_calls`,
`pachner32_candidates`, `pachner32_moves` only when the flag is enabled if literal
old stats shape is desired; optionfalse must retain old default chain schemas
and decision behavior. V3 is selected only when reduce_pachner32 is true;
otherwise retain the existing unlayer-selected v1/v2 behavior.

The factor wrapper's max_crushes charge becomes

```
crushing_steps + boundary_unlayerings + pachner32_moves
```

with absent disabled-option counters interpreted as zero. Extend the wrapper's
policy-option whitelist and strict bool validation, and update its independent
result-accounting checker in the next *new* evidence package. Do not edit frozen
historical research checkers merely to make their old source pins pass. Avoid
creating a fresh move budget per factor or per source. Initial/shelled counts
remain sums over attempted factors, and the new counters are additive.

Required controls before promotion: historical v1/v2 reject the new step; v3
accepts a genuine mixed chain; wrong source hash/successor/region/permutations and
boolean integer fields reject; malformed-source callback exceptions preserve
identity; all three reduction kinds together respect max_crushes exactly;
source models/caches rebuild after each3→2 move; terminal candidate scans are
complete; optionfalse preserves existing behavior; factorwise cap accounting
includes moves from failed children. Retain exact candidates and independent
Regina isomorphism controls from this scratch set, without turning the oracle
into a runtime dependency.
