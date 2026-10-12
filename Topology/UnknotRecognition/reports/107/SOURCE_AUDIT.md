# Source audit

Audit date: 12 October 2026.

## Pin

GitHub ref API returned `c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5` for `main`.
Subsequent substantive file reads named this ref explicitly. GitHub's code-search index also returned entries from `32008c6397fa6f3613c4dda277ab18e99dcdd36e`; those search snippets are not treated as a replacement for the explicit pin.

Repository: https://github.com/VladimirReshetnikov/ProveIt

## Maintained material actually inspected

- `Topology/UnknotRecognition/README.md`: project status and current stage boundaries.
- `Topology/UnknotRecognition/synthesis/column_cancellation.tex`: full text; blob `29d8eb3ae71c9fe54514cd42480862c8ffc6dad0`.
- `Topology/UnknotRecognition/synthesis/core_three_handles.tex`: full text; blob `a2855b337c66fe0c1b493988f0230ffbc023ef49`.
- `Topology/UnknotRecognition/synthesis/three_handles_results.tex`: full text; blob `21ca25c62ad2e57a91eab4634a1f7832531e77f1`.
- `Topology/UnknotRecognition/fast/fastunknot/core_handlebody.py`: lines 1–90, input contract, primal forest, occurrence extraction, and beginning of capped planner; blob `3c27ec79052bf820cbccbd4c6f8cb4e3c0154ca7`. Search also confirmed `column_cancellation_plan`; the complete module was not imported or executed.
- `Topology/UnknotRecognition/fast/fastunknot/core_three_handle_reduction.py`: full text; blob `34d0fd29e0a6f2a4decb01a734e348822e93744a`.
- `Topology/UnknotRecognition/fast/fastunknot/core_three_handle_reduction_verify.py`: full text; blob `dea091754bf8706125b0d7ac21bebefef176b934`.
- `docs/incoming/README.md`: first 120 lines and incoming directory metadata.

The cited source results, including the loop matrix, are reports of the maintained repository. The only measurements performed in this package are in `results/` and explicitly have matrix/graph scope.

## Incoming inventory, not an archive-content audit

The directory listed the following relevant delivery names:

- `ProveIt_Component_Gauge_Cut_Atlases_2026-10-12.zip`
- `ProveIt_Dual_Forest_Normalization_2026-10-12.zip`
- `ProveIt_Dual_Forests_Homological_Progress_2026-10-12.zip`
- `ProveIt_Flag_Regularization_2026-10-12.zip`
- `ProveIt_Positive_Cancellation_2026-10-12.zip`

Their binary contents were not decoded in this study. In particular, the two dual-forest deliveries may overlap with results in this article. The maintained text was the research starting point, but this is NOT an exhaustive reconciliation of every current incoming package. An attempted whole-repository runtime download failed; connector source reads did succeed. No archive bytes or third-party PDF bodies are redistributed.

## External primary references

- Marc Lackenby, Oxford-hosted quasi-polynomial talk slides. The displayed theorem was visually inspected at PDF page 13; the final hierarchy flowchart was also inspected. https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk.pdf
- Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*, arXiv:2607.23350v1, especially Section 9 and Proposition 9.1. https://arxiv.org/html/2607.23350v1
- Mihály Bárász, Kristóf Bérczi, Tamás Király, Yutaro Yamaguchi, Yu Yokoi, *Matroid Intersection under Minimum Rank Oracle*, arXiv:2407.03229v1 / EGRES TR-2024-13. The original version is specified; later author metadata differ. https://arxiv.org/html/2407.03229v1
- Stephen A. Cook, *The complexity of theorem-proving procedures*, STOC 1971, pp. 151–158, DOI 10.1145/800157.805047. Publisher metadata were verified through the DOI result. https://doi.org/10.1145/800157.805047

The conventional proofs in this package do not depend on the truth of an unverified empirical claim from another report. The geometric bridge is explicitly conditional on the authenticated source construction and its existing theorem.
