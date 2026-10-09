# Cocycle Transport and Ordered Boundary Interfaces for Unknot Recognition

Research continuation for Vladimir Reshetnikov's ProveIt project, 9 October 2026.

**Main article:** [article/unknot_geometric_transport.pdf](article/unknot_geometric_transport.pdf)  
**TeX source:** [article/unknot_geometric_transport.tex](article/unknot_geometric_transport.tex)

The work is pinned to ProveIt commit **3a90fb34146c915328ab8eac6250cc2514f74ed0**, under Topology/UnknotRecognition. It also audits the relevant packages then present in docs/incoming.

## Results

The article proves exact Euler and normal-piece changes for a transported integral cocycle across a legal 2–3/3–2 Pachner move. This enables all eligible collapse scores to be computed in one incidence pass, and permits a whole downward epoch without solving cohomology after every move. Normalized coefficient growth is charged to upward moves.

A second implementation recovers marked cyclic order on a supplied compressed normal boundary. Degree-two deletion leaves paths with exactly two endpoint occurrences, so count, sum, sum of squares, and length recover each endpoint pair exactly. Four coordinates replace the previous one-hot dimension of 2p+1.

Both interfaces have independent consumers. A source-bound positive search verifies the diagram exterior, optional shellings, all cocycle moves, and a terminal essential-disc component. The existing production recognition schedule is unchanged.

The article also proves nonincrease of vertex-link-peeled piece count and a thirteen-corner-record lemma for scoring after vertex-link peeling. That refinement is **not implemented**. The prescribed macrosearch and upward-burst bounds are **conditional** on explicit witness-coverage hypotheses and complete state queries. No general quasi-polynomial recognition theorem is claimed.

## Performance evidence and negative results

The final corrected-source all-candidate benchmark measures 20.519 ms versus 6,857.931 ms at 384 tetrahedra and 128 eligible collapses, a 334.23-fold median ratio. The arms produce identical per-site Euler and piece outputs. This measures scoring every candidate, not the entire recognizer.

At 128 marked occurrences, moment replay takes 1,062.141 ms versus 15,035.489 ms for one-hot replay, a 14.16-fold ratio. Producer plus independent replay improves by 10.31-fold when measured together. The full mathematical output and 4,215-event AHT trace are identical. Raw paired samples and exact measured sources are retained.

On 82 source diagrams, all three descent arms complete, each performs 144 total collapses, and each finds 15 positive supplied-vector cases. There is **no added recognition coverage**. Both transport policies give the same final Euler characteristics and piece counts on this corpus.

A new checked example turns one primitive coherent compressing disc into a disc plus two spheres under a legal collapse. Connectivity and the bound chi <= 1 therefore cannot be assumed for transported primitive fibres. Tiny literal boundary walks also beat the compressed producer on small inputs. The article includes these limitations and twelve research questions with concrete milestones.

## Package contents

| Path | Purpose |
|---|---|
| article/ | Complete TeX sources, generated tables, figure files, and rendered PDF |
| fast/ | Pinned 566-file supporting snapshot plus additive production modules, tests, drivers, and boundary measurements |
| reports/ | Seventeen exact historical oracle files needed by the maintained full test suite |
| synthesis/data/ | Obstruction input, local/corpus/scoring audits, and splitting certificates |
| reproduce/ | Portable checks, retained-proof replay, compact 84-source fixture, and table/figure generator |
| validation/ | Final test logs, proof-replay record, and integration checks |
| provenance/ | Source inventory, environment, and measurement lineage |
| integration.patch | Additive code/test/research-text patch for the pinned repository |
| integration_manifest.json | Patch scope, target revision, and verified file mapping |
| SOURCE_AUDIT.md | Current-baseline audit, incoming package boundaries, and primary literature |
| RESEARCH_STATUS.md | Proven, implemented, measured, conditional, and unimplemented claims |

The full snapshot is included so the experiments can be reproduced without an unshipped repository checkout. It omits unrelated historical result archives. The historical pre-callback transport source ZIP is a small measurement provenance artifact, not an additional change to apply.

## Reproduction

Using Python 3.12, from the extracted package root:

    python3 -m venv .venv
    . .venv/bin/activate
    python -m pip install -r requirements-research.txt
    python reproduce/run_checks.py --full

The new native algorithms use the standard library. Optional dependencies enable the exact research environment, plotting, and independent Regina comparisons. With no additional packages, the native feature checks can be run using:

    python reproduce/run_checks.py

Benchmarks should run sequentially. Exact commands and contracts are in the article's reproduction appendix and the two research READMEs under fast/. Regenerated files go to reproduced/; the supplied evidence is retained.

To rebuild the article from existing figures:

    cd article
    latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_geometric_transport.tex

To regenerate the tables and figure first, run python reproduce/build_tables.py from the package root.

## Integration

From a checkout at the pinned commit:

    git apply --stat /path/to/integration.patch
    git apply --check /path/to/integration.patch

The patch was checked against the pinned files and its result compared with the included additions. It does not publish changes or modify the default recognizer. A newer checkout may already contain competing additions; check it separately.

The repository's incoming-report policy places an unknot report under the next Topology/UnknotRecognition/reports/<NN>/ directory, preserving delivered contents and leaving any code patch inside that report for separate integration. No report number is assigned here. This package contains no checksum-only manifest.

Code follows the repository's included MIT-0 license. Third-party runtime packages are not bundled. The mathematical article contains no claim of Lean formalization.
