# Affine proof cores and incremental machine transport

21 October 2026. New research packet; earlier delivered packets are preserved.

## Read first

report.pdf summarizes the new findings, recent archive status and limits. The new reusable macro interface contracts 1,059 exact drain loops into a 367-vertex affine core with 33 shared matrices. This is not a TM state reduction. For the currently identical source graphs, direct normalized/canonical equality is simpler; contraction adds checks and may add overhead. Its strongest use is comparison of future differing loop implementations.

The exact context215 patch is an independently checked six-block instance of an ALREADY KNOWN old-run positive-stutter method. Nine old-table graph histories suffice; arbitrary initial tape equivalence reuses startup. FM215/M124 use fewer local blocks/marker facts but still need upstream semantic adapters. CM215 has the least remaining Lean integration work: its Core attachment is recorded compiled, while its final ZFC adapter closure is explicitly not freshly compiled. No new compiled context215 theorem is claimed.

The new model patch removes three formula inductions (270 to 235 lines). All new formal proposals remain uncompiled. Recent incoming archives do contain recorded compiled normalized and zero-offset source lanes, but maintained Lean/Coq subtrees are unchanged through main 62f0f95e2b2df5b380ae502eb65bd64f1ee90209. Archive proof records are not a fresh local full-endpoint build.

## Portable replay

Python 3 standard library only, assertions enabled, using a fresh external directory:

    python -I -B verify.py --work /tmp/next-proof-check

The verifier regenerates the complete canonical input graph from pinned Lean literals, checks current tree equality, recomputes drain contraction, ranks, shared matrices, auxiliary quotient/interval results and adversarial tests. It checks six whole-tape patch blocks, old-only histories, malformed-patch rejection, decoder products and the complete DR row-dependency census. The DR analyzer assumes existing BoxLemmas; unchanged direct row footprints do not alone establish formal oracle reuse. Logical proposed-source hashes and removed induction names are checked, not compiled.

All generated outputs are written to copies in the external work directory. None of the received Lean/Rocq sources or archived scripts are executed. Owned Python checkers operate on inert data. Structural and runtime scripts reject optimized Python. graph_origin is the earlier owned source-to-graph audit, included so that contraction's input need not be trusted as an unexplained JSON file.

## Contents and provenance

- structural: complete original/affine graphs, local drain certificates, ranks, shared matrices, independent validator, mutations and scoped negative analyses.
- runtime: exact old/new context tables, patch certificate/checker, decoder inputs and certificates, DR affected-guard receipt and owned replay.
- calculus: uncompiled exact patch and generic transport/projection proposals with pinned source excerpts.
- review: current commit/subtree receipts, recorded archive source/log hash audits, and two relevant incoming proof archives as INERT evidence.
- graph_origin: pinned source-tree literals and owned canonical graph checker with exact wrapping pointer semantics.
- licenses: inherited source notices/pins retained; new scripts are owned research validators. No external dependency installation or network access is required by replay.

The top manifest pins every payload, including nested manifests. Archive status records have not been independently recompiled. To build report.tex, run pdflatex twice with geometry, lmodern, amsmath, amssymb, booktabs and hyperref. The delivered PDF is separately rendered and visually checked.
