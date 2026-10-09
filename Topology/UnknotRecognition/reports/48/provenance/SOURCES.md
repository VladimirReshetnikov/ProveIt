# Source and execution provenance

Inspected repository: VladimirReshetnikov/ProveIt.
Pinned reference: `47002f64b9a97f64edc8e8b8f793b83983b719f9`.
Repository content was read using the connected GitHub reader. No repository writes were performed.
The pinned reference is a reproducibility baseline, not a claim that main stopped changing.

Key paths under `Topology/UnknotRecognition/`:

- `fast/fastunknot/braid.py`, blob `d7de8c2d8f7b12f35a4ccc19478ca09a370bc2a3`: existing explicit three-braid classification and matrix control.
- `fast/fastunknot/compressed_words.py`, blob `bd68418e226813a7fa50dc87405c214970ddf50e`: source of the adapted exact string kernel.
- `fast/README.md`: maintained pipeline, source-reported 687-test status, compressed relator work.
- `reports/19/README.md`: previous explicit rank-two substring kernel.
- `reports/34/README.md`: previous explicit singleton decomposition, minority-sign bounds, and endpoint descent.

`compressed_b3/strings.py` is a **source-derived adaptation**, not a byte-identical upstream file.
It retains exact indexed split/periodicity-compaction equality, bounded direct probes, slicing, and LCP.
It omits the free-group-specific operations and adds height instrumentation.
The independent explicit stack control is also source-derived; the matrix control is separately coded.
The producer and certificate replay share the string kernel. Replay does not use producer reduction or LCP search.

A full repository clone was not available in the execution container (network DNS failure).
The full upstream regression suite, actual upstream WordArena injection, and Rust port were NOT run.
`integration/upstream_check.py` is supplied for an actual checkout; no successful run is claimed.
No supplied test substitutes a fake upstream checkout and calls it a production check.

Executed software: CPython 3.13.5, Linux x86-64 (full metadata in results/audit.json).
All source, tests, experiments, certificates, and article text newly supplied here use MIT-0.
Third-party paper PDFs and font files are not redistributed.

Primary mathematical references (complete citations also in the article):

- Saul Schleimer, Polynomial-time word problems, Comment. Math. Helv. 83 (2008), 741–765, DOI 10.4171/CMH/142; https://arxiv.org/abs/math/0608563.
- Derek Holt, Markus Lohrey, Saul Schleimer, Compressed decision problems in hyperbolic groups, Groups Geom. Dyn. 18 (2024), 1233–1273, DOI 10.4171/GGD/809; https://arxiv.org/abs/1808.06886.
- Daniel Bennequin, Entrelacements et équations de Pfaff, Astérisque 107–108 (1983), 87–161; https://www.numdam.org/item/AST_1983__107-108__87_0/.
- Anthony Conway, Burau maps and twisted Alexander polynomials; https://arxiv.org/abs/1510.06678.
- Cornelia A. Van Cott, Relationships between braid length and the number of braid strands, Algebr. Geom. Topol. 7 (2007), 181–196, DOI 10.2140/agt.2007.7.181; https://arxiv.org/abs/math/0605476.
- P. B. Kronheimer and T. S. Mrowka, Khovanov homology is an unknot-detector, Publ. Math. IHES 113 (2011), 97–208; https://arxiv.org/abs/1005.4346.
- Marc Lackenby, Incompressible surfaces, hierarchies and unknot recognition, arXiv:2607.23350v1, 25 July 2026; https://arxiv.org/html/2607.23350v1.
- Tuomas Kelomäki and Dirk Schütz, On computational complexity of Khovanov homology, arXiv:2601.02119v1; https://arxiv.org/html/2601.02119v1.
