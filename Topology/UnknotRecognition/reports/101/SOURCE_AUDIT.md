# Source audit and attribution

Research date: 12 October 2026. Reference repository revision:
`fe8702d8a864daf4fcfde1cf4ef8dbcc6d83b69c`.

The repository was read through the connected GitHub tool. Its default branch
was moving during this work; this report uses the explicit revision above
for the core geometric sources, not an assertion that the whole repository
remained frozen. This was a targeted review, not an audit of all reports or
all incoming archives. No commit, branch, pull request or production write
was made.

## Native material actually inspected

`Topology/UnknotRecognition/synthesis/cut_cells.tex`, Git blob
`dc12b1a58aedaed78f00b63109b0aa5214832ca1`: the full maintained article,
including exact raw-cut cells, source occurrences, linear family counts and
bit-size bounds. These are predecessor results, not new claims of this package.

`Topology/UnknotRecognition/synthesis/parallelity.tex`, Git blob
`d7293976bea14fce6b4848bf6a2d7a20134c2491`: all-dimensional source parallelity,
bounded inherited core, retained boundary ports and the separate admissibility
obligation. The new paper does not re-propose raw cutting or the 30 T core.

`Topology/UnknotRecognition/fast/fastunknot/normal_cut_cells.py`: a request for
lines 1–240 returned the constructor prefix, including family layout, local
rank events, face cycles and attaching occurrences. This was source inspection,
not a live invocation or complete software audit.

`Topology/UnknotRecognition/synthesis/data/parallelity-admissibility-obstruction.json`,
Git blob `2ea36d9d629c133e540cce4802ef76aa7342b2af`: the exact source fixture
has one tetrahedron with face 0 paired to face 1 by permutation `(1,2,3,0)`
and reciprocal `(3,0,1,2)`, and faces 2 and 3 unpaired. All seven normal
coordinates are zero. The native certificate's input digest is retained in
`provenance/sources.json`. Our atlas digest is a *different representation's*
digest; equality between those hashes is neither expected nor asserted.
The importer, direct local flag oracle and 24 relabellings were executed here.

The repository README and incoming listings were read for context. A listing
is not a content audit. No full checkout or maintained suite was obtained or
run. The exact nonzero normal-cut exporter remains unimplemented here.

## Incoming predecessor

The principal predecessor is *Modular Morse Certificates for Compressed Unknot
Hierarchies*, 12 October 2026, obtained as an existing Library archive. Its
manuscript identifies native source regularization as a missing gate. Its
`ranked_morse.py`, verification CLI and license are retained with byte-identical
hash checks. The CLI alone is renamed to `morse_verify.py`. The adapter invokes
the real preceding arithmetic code, not a mocked signature.

The prior scalar-separator, sparse-cut-grammar and cographic archives received
limited research-continuity inspection. None is a mathematical black box or a
runtime dependency of the new flag construction. No novelty claim depends on
having exhaustively reviewed all prior ProveIt material.

## External primary sources

Hatcher's appendix *Simplicial Complexes and Delta-complexes* supplies the
classical distinction between one regularizing subdivision and two subdivisions
to an abstract simplicial complex. Forman's 2002 guide supplies the Morse
framework; the collapsible PL-manifold consequence is classical and also
recorded by Adiprasito, Benedetti and Lutz. These sources were checked through
primary-host PDFs, including visual page inspection. The new contribution is
not ordinary barycentric subdivision or the classical collapsible-ball fact.

Lackenby's July 2026 preprint `2607.23350v1`, the Oxford 2021 announcement and
lecture material were checked for the relationship between hierarchy
construction, local operations and a running-time proof. The current paper
uses no unsupported claim that the native recognizer already meets the full
quasi-polynomial target. URLs and coverage are recorded in the provenance JSON
and the article bibliography; external papers are not redistributed.

## Evidence and trust boundaries

The retained JSON measurements come from completed local runs in this session.
The unfinished 1,024-layer pilot is explicitly identified. The 32 unit tests,
448 counted audit replays, source-fixture comparisons and local timings are
ours. Prior repository and predecessor test counts remain prior results and
are not added to these totals.

Hashes establish byte integrity or source binding, not geometric truth.
Geometric validity relies on the stated source construction, exact charts,
independent replay and theorem hypotheses. Proofs are research drafts, not
peer-reviewed or proof-assistant checked. Full native exporter integration,
matching discovery, pattern/admissibility machinery and hierarchy accounting
remain separate obligations.
