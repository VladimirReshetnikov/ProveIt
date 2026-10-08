# Research provenance and claim boundaries

## ProveIt baseline

The implementation baseline is
[`VladimirReshetnikov/ProveIt` at `86f23490006c880cd01db9bec10761d39c6395c8`](https://github.com/VladimirReshetnikov/ProveIt/tree/86f23490006c880cd01db9bec10761d39c6395c8/Topology/UnknotRecognition).
The authoritative inventory is
[`integration/source_manifest.json`](integration/source_manifest.json).
It records the repository, pinned commit, paths, Git blob identifiers and byte
sizes for 82 fetched source blobs: 73 under `fast/` and nine selected synthesis
and report files. This is a targeted audit of the unknot-recognition program,
not a claim to have fetched or reviewed the entire ProveIt repository.

The complete baseline `fast/` snapshot is retained with the modifications in
this package. Its inherited MIT No Attribution license remains in `fast/LICENSE`.
The older architecture already includes checked short-strand braid decisions,
signed-Seifert certificates, Reidemeister and descending reductions, visible
factorization, modular polynomial obstructions and exact Khovanov backends.
These components are not credited as new contributions of this report.

The code delta is isolated in
`integration/fast_arithmetic_continuations.patch`. Its 13 paths include the
new modules, integration, documentation, tests and the local fixtures needed by
those tests. `integration/patch_manifest.json` records exact file identities.
An isolated baseline application reproduced the delivered 81-file noncache
`fast/` tree byte-for-byte, followed by successful execution of the 18 new test
methods there. The accompanying log is `results/patch_verification.txt`.

## Narrow inspiration from openai/math

The inspected external snapshot is
[`openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a),
whose README explicitly distinguishes
stages of verification. The report does not adopt its headline conjecture claims
as unconditional mathematical inputs.

The useful narrowly inspected source is the separation section in
[`An exponential two-way deterministic state lower bound for one-way liveness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026/build/sections/separation.tex).
The relevant idea is elementary context distinguishability: two compositional
summaries that agree must produce the same acceptance under every admitted
continuation. Carefully selected continuations can therefore separate summaries.
This is standard Myhill--Nerode reasoning, not a new principle claimed here.
The inspected section has Git blob hash
`4f7b9feb631736f004273bbdb212adea3eee9d3a`.

The present work independently constructs rational-tangle columns and
continuations whose Boolean unknot matrix is an exact identity of exponential
order. It does not rely on that manuscript's exponential automaton-state theorem,
diagram-monoid representation or rank-loss induction. Its signed determinant
pairing has rank at most two before nonlinear readout; this explicitly shows
why a Boolean linear-summary lower bound is not a general time lower bound.

The source inspection supplied an approach to formulating the obstruction.
The topology and the concrete rational-tangle construction are verified and
argued separately in the article. A targeted search did not establish publication
priority for the specific construction, and this package claims no exhaustive
novelty search.

## Imported topology and new implementation work

The rational fraction classification and two-tangle numerator-closure criterion
are classical results presented by Kauffman and Lambropoulou; the latter is stated in
[*Hard Unknots and Collapsing Tangles*](https://arxiv.org/abs/math/0601525),
Theorem 5. The Montesinos/Seifert-cover input is classical. The local
non-embeddability criterion is imported from
[Nogueira and Salgueiro, arXiv:2110.15645](https://arxiv.org/abs/2110.15645),
Theorem 4.9. The article supplies precise statements and their required input
conditions rather than treating arbitrary formal fraction data as topology.

The fixed-prefix full-complex argument uses the ordinary Bar--Natan tangle
category, additive closure functors and the determinant lower bound for reduced
Khovanov homology. The independent audit is retained in
`research_notes/checkpoint_provenance.md`. The lower bound concerns a specified
prefix and explicitly delooped chain summands counted with multiplicity. It is
not a lower bound for every crossing order, every representation, or the entire
filtered recognition pipeline.

The implementation contribution is the exact checked boundary between these
theorems and executable decisions: primitive arithmetic, actual planar tangle
construction, source preservation and replay, strict local disk matching,
resource semantics, tests and integration. Integer normalization never reduces
the common numerator across distinct rational summands. A determinant-one
integer homology-sphere cover is not automatically identified with the sphere.
The test corpus contains examples that expose both mistakes.

## Evidence and limits

The delivered combined suite has 152 passing test methods: 134 inherited and
18 added here. Independent finite diagnostics cover additional diagram and
arithmetic cases. Raw benchmark files preserve paired samples, control ratios,
construction costs, censored incomplete baseline runs and measured regressions.
These are executable checks and observations, not formal proofs or asymptotic
runtime measurements.

The complete source classifier requires a supplied Montesinos presentation.
The local search is literal and opt-in, with a fixed small catalogue or supplied
admissible patterns. No automatic recognition of all rational or Montesinos
subtangles up to isotopy is provided. The general worst-case quasi-polynomial
target remains unproved for this implementation; the article identifies the
missing structural and discovery obligations explicitly.
