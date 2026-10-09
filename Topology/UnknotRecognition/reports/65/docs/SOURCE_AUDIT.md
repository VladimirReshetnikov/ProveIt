# Source audit and research boundary

Date: 2026-10-09.
Reviewed ProveIt revision: `3a90fb34146c915328ab8eac6250cc2514f74ed0`.

## Repository material actually read

The GitHub connector was used to read the UnknotRecognition and incoming directory listings, the UnknotRecognition README, the incoming intake README, the main-branch revision metadata, and the following source texts at the pinned revision:

- `Topology/UnknotRecognition/synthesis/weighted_components.tex`
- `Topology/UnknotRecognition/synthesis/diagram_exterior.tex`

The source texts establish that the maintained project now has a source-checked compact exterior constructor and supplied-vector component/disc census. The article's status discussion is based on these current pinned sections rather than the older predecessor report's statement that diagram provenance was absent.

The incoming listing included compiled-port, sparse-incidence and 2026-10-09 research ZIPs. **The incoming archive collection was not fully downloaded, unpacked, or audited.** Their titles were not used as evidence for unobserved theorem contents. No assertion is made that the present theorem is absent from every incoming binary manuscript. Network/archive access was insufficient for a full archive-by-archive review; the deliverable instead records the exact reviewed texts and its novelty limitation.

The maintained `fast/` runtime was not checked out or run. No native test count, code timing, or integration success is asserted on the basis of an unexecuted call.

## Predecessor report reviewed through Library text

`unknot_port_continuations.pdf`, titled **Certified Port Quotients and Guarded Interval Attachments**, dated 2026-10-08, 26 pages. Relevant reviewed passages include:

- The multiplicity-aware incidence quotient formula (Section 3).
- Bell(r+1) distinguishability of physical partial-partition states (Section 7).
- The fixed-source restricted coning-search bound and its assumptions (Section 7).
- The further-research question seeking 2^O(r) states for geometrically useful restricted continuations (Section 12).
- The report's own local/native/global scope and source pin `eb368edf975695e3e16a8774dcb7846bda0c13a0`.

Our disk-completion reducer does not refute its physical-state lower bound. It preserves a terminal optimization predicate by a family of representatives, not the complete state or every guard. The article contains an explicit three-port counterexample to unrestricted guard preservation.

## Primary literature checked

1. Bodlaender, Cygan, Kratsch, Nederlof, arXiv:1211.1505. Deterministic rank-based and determinant-based algorithms for weighted connectivity problems. This is prior art for the main compression framework.
2. Fomin, Lokshtanov, Panolan, Saurabh, arXiv:1304.4626v4. Linear-matroid representative sets. This is prior art for the exterior/minor interpretation.
3. The same authors, arXiv:1402.3909, Representative Sets of Product Families. Relevant to a future faster join implementation; not claimed implemented here.
4. Mannens and Nederlof, arXiv:2307.01046. Includes a forest-union compatibility rank bound. Our matrix is the connected-tree predicate over F2, not an assertion that the entire forest matrix has rank 2^(r-1).
5. Lackenby, arXiv:2607.23350v1, particularly Section 9. The article does not silently assume a general fully costed quasi-polynomial hierarchy implementation. Later refinements in that paper are not dismissed; they do not supply this report's complete disk-assembly compiler.
6. Agol, Hass, Thurston, arXiv:math/0205057. Classical compressed orbit-counting context, not a complete candidate-discovery bound.

The bibliography and source URLs are in `references.bib`, `article.tex`, and `docs/provenance.json`.

## Novelty and proof status

The paper supplies full proofs of the exact disk-completion factorization and sharp ranks, weighted representative-subset theorem, topological defect contract, typed composition and conditional complexity consequences. The general rank-based / matroid technique is explicitly credited as prior art. This work has not undergone an exhaustive worldwide priority search or external peer review; equivalent algebraic formulations may already exist in the literature or incoming drafts.

All numerical statements are from retained completed executions. Finite code tests do not replace the mathematical proofs. No Lean, Rocq, or other proof-assistant verification is claimed.
