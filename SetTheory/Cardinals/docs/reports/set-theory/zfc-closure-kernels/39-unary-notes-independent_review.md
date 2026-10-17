# Independent mathematical and finite-code review

Date: 16 October 2026.

## Main mathematical section

I read research_theory/unary_support_theorem.tex in full after its first
complete draft. The tagged normalized-cycle construction, first-order
definability, stage-rank exclusion of ordinary cycles, hereditary support
condition, local-fiber set existence, equivariance, exact least closure,
coarse orbit containers, H=M identity, bounded-Pairing obstruction, bilateral
chain extension, and Ext+Pairing+EPSC1 calibration were checked independently.
No substantive mathematical gap was found. The bound witness is not chosen
uniformly; unique fibers let ambient Replacement do exactly the required
collection. The support proof uses only the one parameter's support; it
would not silently work for an arbitrary tuple, which is the intended
obstruction.

Three corrections were sent to the author: a missing LaTeX backslash in
the first EPSC conjunction; the sign of the phase step when talking about
membership arrows; and phrasing the well-founded-copy observation in the
intended ambient universe, avoiding an external well-foundedness assumption
about arbitrary nonstandard ZFC models. These are presentation corrections,
not changes to the theorem or construction.

The subsequent stronger finite repair was checked independently against
the pinned source21 proof: EPSC1 plus the single equality-free exact
incoming-profile Pairing sentence DP suffices, without a separate raw
Extensionality axiom. DP gives pure Pairing in H/Delta using the existing
one-parameter purity cut. Once finite pure parameter tuples can be packed,
apply EPSC1 directly to the guarded interpreted EPSC matrix with its one
tuple parameter. Global support makes every member of the initial hull
pure; one-parameter saturation then transfers initial closure, recurrent
closure and support. Raw emptiness and interpreted emptiness agree on H,
and all raw empty objects are H. The earlier two-parameter root graft and
support filter are unnecessary because the target at this stage is EPSC,
not seeded PSC. A fixed universally closed two-parameter disjoint Delta
gate yields DP; if the first parameter is nonempty it activates the second
branch, if only the second is nonempty interchange them, and if both are
empty their incoming profiles coincide. This supplies a finite calibrated
repair, not a measured compiler or machine-state saving.

The support-free extension in research_repo/support_deletion.tex was proved
separately. It uses full orbit saturation after each image stage, so it does
not assume that a fixed arbitrary-parameter matrix is fully equivariant.
All intermediate orbit unions are sets because Sym(I) is a set. Newly added
inputs are processed at subsequent stages, ensuring closure at the limit.
The exact source support clause fails for the displayed two-parameter
constant matrix, as required.

## Finite regression

I read zfc_unary_closure_research/code/support_diagnostics.py in full and
executed it independently with output
research_repo/support_diagnostics_replay.json. The replay was exactly equal
as parsed JSON to the delivered result. Counts reproduced:

- 24 permutations of four indices, acting on eight primitive cycle nodes.
- 256 base subsets, with minimum-support histogram 4,48,180,24 for sizes
  0,1,2,3; 52 supported represented nodes after singleton normalization.
- 1,024 full-group invariant relations and 131,072 one-index-stabilizer
  invariant relations; total 132,096.
- 350,400 successful comparisons against prefixed carrier subsets.

The Gray-code loop visits every union of the disjoint ordered-pair orbits
exactly once. The image tables compute the intended positive operator.
Leastness is checked against every prefixed carrier subset, rather than
only the invariant ones. The finite rank truncation is extensional and
irreflexive, but fails the constant Empty(y) EPSC instance because the exact
singleton of its empty node is absent. Thus the explicit disclaimer that
this truncation is not a full EPSC model is mathematically supported.

No full-schema satisfaction, consistency theorem, proof-assistant check,
or machine-state improvement follows from this finite regression. Its scope
is the group-action and least-closure algebra used in the ordinary proof.

A minor wording suggestion was sent: the three-index caution applies to
the chosen same-phase unordered pair. It should not be generalized to every
cross-phase pair on three indices. The program's actual calculation and
JSON claim have the correct narrow scope.

## Bounded machine-search source and replay

I additionally read research_machine/edge_contexts.py, edge_inventory.py,
both C++ search programs and MACHINE_AUDIT.md. Both search programs were
compiled independently and executed at radii four and six on the retained
context inputs. All four complete stdout files agreed byte-for-byte with
the original retained outputs. Each radius tests 218 candidate deletions
over 407 incoming edges, with 102,564 target-only choices and 410,256 whole
transition choices. The respective partial edge-option counts are 40 and
52, and all four runs found zero complete deletions.

The report accurately describes the finite window, 64-step limit,
strictly positive original/candidate progress, complete-window joins,
terminal exception, and stops before using unaccounted changed rows.
I did not independently regenerate all affine contexts. This replay
therefore validates the finite search implementation and retained result
for those inputs, not a kernel proof that all concrete reachable contexts
are represented. The context overapproximation and bounded joins mean
the zero result is no semantic state-count lower bound. A wording
suggestion was sent to call this a diagnostic stage rather than a
necessary search stage for general semantic deletion.
