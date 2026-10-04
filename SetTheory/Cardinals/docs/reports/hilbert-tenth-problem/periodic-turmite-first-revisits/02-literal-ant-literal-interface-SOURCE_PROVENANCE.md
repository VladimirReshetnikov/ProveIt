# Source credit and provenance

Maldonado, Gajardo, Hellouin de Menibus and Moreira, *Nontrivial Turmites are Turing-universal*, arXiv1702.05547v1,18 February2017, is the primary geometric source:

- https://arxiv.org/html/1702.05547
- https://arxiv.org/pdf/1702.05547v1
- https://arxiv.org/src/1702.05547v1

Theorem2.1 supplies periodic abstract hardware with finite input changes; Theorem3.1 realizes it by nontrivial turmites. Section5 states the construction's two-visit property. Those qualitative ideas and results are credited to this paper. Our coordinate extraction, complete local histories, specific fixed CA compiler, input anchor, acceptance residues and executable audits make that interface literal; they are not offered as prior-art-free qualitative universality.

Primary PDF SHA256:
44419ddfc0e135d62f1c87e9ec93a7aeb698aee21aa4c7183fe1cb6fe0a3c246

Primary source-archive SHA256:
e4c5d6a09d8fbb4da496ecaa837a65952f8aaca0e136c153cc6d3bc130126adc

The seven finite numerical cell maps were read from explicit unit-square fills in `img/cable_a.mps`, `cable_b.mps`, `cable_c.mps`, `box.mps`, `cruceA.mps`, `cruceB.mps`, and `union.mps`. PostScript/MetaPost/TeX and all other upstream code were never executed. The derived numeric maps and independent local history catalog are retained under `common/`; source-asset hashes are in `primitive_catalog.json`. Full article text, PDFs, source archives and article images are deliberately excluded from this self-contained replay packet.

The primitive-map JSON SHA256 is
fb2e7245f325bfbbe8a6d59e0ac1a3c63e4e73c0fb523d4738ea9c661c3d1add.

The fixed U15 transition table is the previously supplied pure-data table, SHA256
0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a.
Its exact data are included in `ca/u15_table.json`. The U15 program-to-pair universality proof is not replaced by a new implemented compiler here.

The existing arithmetic interface was inspected at ProveIt commit5883b08b7af362077f13bb4afa97a23a90ae4cf8:

- https://github.com/VladimirReshetnikov/ProveIt/blob/5883b08b7af362077f13bb4afa97a23a90ae4cf8/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/5883b08b7af362077f13bb4afa97a23a90ae4cf8/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md

Their SHA256 pins are9c26b118aa28f8454204be6fb6f751beeae713a752d18b75943e9862e7de1656 and2bb857e68135bc5f1998c4d2a8560a8d9278f29e626d8433d014f22e620ae2df, respectively. No upstream arithmetic program was executed, and no171/174-operation novelty is claimed.
